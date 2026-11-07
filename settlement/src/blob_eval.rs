//! Audit H-01, part 1: the value of a blob's polynomial at a point, computed from the blob's
//! bytes exactly as EIP-4844 defines it, and the 0x0a point-evaluation input that proves the
//! same value on L1.
//!
//! The binding we are building: the proof computes `y = p_blob(z)` from the transaction bytes it
//! executed (over the BLS12-381 scalar field, with the uint256 MULMOD AIR), for a point `z`
//! drawn by Fiat-Shamir after the blob is fixed; the contract checks `p_blob(z) = y` for the
//! blob it actually carries with the point-evaluation precompile. Two different blobs agree at a
//! random `z` with probability at most 4096 / r_bls (~2^-243). This module is the native
//! reference both sides must match, tested against c-kzg (Ethereum's KZG library).
//!
//! EIP-4844 (`evaluate_polynomial_in_evaluation_form`): the blob holds the evaluations
//! `e_i = p(w_i)` at the 4096-th roots of unity `w_i` in bit-reversed order, and for z not a root
//!
//! ```text
//! p(z) = (z^4096 - 1) / 4096 * sum_i e_i * w_i / (z - w_i)      (mod r_bls)
//! ```

use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::sync::OnceLock;

/// Field elements per blob.
pub const WIDTH: usize = 4096;
/// Address of the point-evaluation precompile.
pub const POINT_EVALUATION: u8 = 0x0a;

/// BLS12-381 scalar field modulus (BLS_MODULUS in EIP-4844).
pub fn modulus() -> &'static BigUint {
    static R: OnceLock<BigUint> = OnceLock::new();
    R.get_or_init(|| BigUint::parse_bytes(b"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001", 16).unwrap())
}

/// The 4096 roots of unity in the blob's (bit-reversed) order: w_i = g^(brp(i)) with
/// g = 7^((r-1)/4096).
pub fn roots_brp() -> &'static [BigUint] {
    static W: OnceLock<Vec<BigUint>> = OnceLock::new();
    W.get_or_init(|| {
        let r = modulus();
        let g = BigUint::from(7u32).modpow(&((r - 1u32) / WIDTH as u32), r);
        let mut natural = Vec::with_capacity(WIDTH);
        let mut x = BigUint::one();
        for _ in 0..WIDTH {
            natural.push(x.clone());
            x = x * &g % r;
        }
        (0..WIDTH).map(|i| natural[(i as u32).reverse_bits() as usize >> (32 - 12)].clone()).collect()
    })
}

/// The blob's field elements (big-endian 32-byte words), or None if one is not below r_bls.
pub fn elements(blob: &[u8]) -> Option<Vec<BigUint>> {
    if blob.len() != WIDTH * 32 {
        return None;
    }
    let r = modulus();
    blob.chunks(32).map(|c| Some(BigUint::from_bytes_be(c)).filter(|e| e < r)).collect()
}

/// p_blob(z) for `z < r_bls` (any z, including a root of unity).
pub fn evaluate(blob: &[u8], z: &BigUint) -> Option<BigUint> {
    let r = modulus();
    let e = elements(blob)?;
    let w = roots_brp();
    if let Some(i) = w.iter().position(|wi| wi == z) {
        return Some(e[i].clone());
    }
    // batch inversion of (z - w_i)
    let d: Vec<BigUint> = w.iter().map(|wi| (z + r - wi) % r).collect();
    let inv = batch_inverse(&d, r);
    let mut acc = BigUint::zero();
    for i in 0..WIDTH {
        acc = (acc + &e[i] * &w[i] % r * &inv[i]) % r;
    }
    let zn = (z.modpow(&BigUint::from(WIDTH), r) + r - 1u32) % r;
    let inv_width = BigUint::from(WIDTH).modpow(&(r - 2u32), r);
    Some(acc * zn % r * inv_width % r)
}

fn batch_inverse(v: &[BigUint], r: &BigUint) -> Vec<BigUint> {
    let mut prefix = Vec::with_capacity(v.len());
    let mut acc = BigUint::one();
    for x in v {
        prefix.push(acc.clone());
        acc = acc * x % r;
    }
    let mut inv = acc.modpow(&(r - 2u32), r);
    let mut out = vec![BigUint::zero(); v.len()];
    for i in (0..v.len()).rev() {
        out[i] = &inv * &prefix[i] % r;
        inv = inv * &v[i] % r;
    }
    out
}

/// 32-byte big-endian encoding.
pub fn be32(x: &BigUint) -> [u8; 32] {
    let b = x.to_bytes_be();
    let mut out = [0u8; 32];
    out[32 - b.len()..].copy_from_slice(&b);
    out
}

/// The 192-byte input of the 0x0a precompile for `blob` at `z`:
/// versioned_hash || z || y || commitment (48) || KZG proof (48).
pub fn point_evaluation_input(blob: &[u8], z: &[u8; 32]) -> Option<Vec<u8>> {
    let s = c_kzg::ethereum_kzg_settings(0);
    let b = c_kzg::Blob::from_bytes(blob).ok()?;
    let (proof, y) = s.compute_kzg_proof(&b, &c_kzg::Bytes32::from(*z)).ok()?;
    let mut v = Vec::with_capacity(192);
    v.extend_from_slice(&crate::blob::versioned_hash(blob));
    v.extend_from_slice(z);
    v.extend_from_slice(y.as_ref());
    v.extend_from_slice(&crate::blob::commitment(blob));
    let p: &[u8] = proof.as_ref();
    v.extend_from_slice(p);
    Some(v)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kzg_y(blob: &[u8], z: &[u8; 32]) -> [u8; 32] {
        let b = c_kzg::Blob::from_bytes(blob).unwrap();
        let (_, y) = c_kzg::ethereum_kzg_settings(0).compute_kzg_proof(&b, &c_kzg::Bytes32::from(*z)).unwrap();
        *y.as_ref()
    }

    #[test]
    fn evaluation_matches_c_kzg() {
        let data: Vec<u8> = (0..crate::blob::MAX_DATA).map(|i| (i * 31 + 7) as u8).collect();
        let blob = crate::blob::to_blob(&data).unwrap();
        let r = modulus();
        for seed in [1u64, 2, 0xdead_beef] {
            let z = BigUint::from_bytes_be(&crate::public_input::keccak256(&seed.to_be_bytes())) % r;
            assert_eq!(be32(&evaluate(&blob, &z).unwrap()), kzg_y(&blob, &be32(&z)), "z from seed {seed}");
        }
        // at a root of unity the value is the element itself
        let z = roots_brp()[5].clone();
        assert_eq!(be32(&evaluate(&blob, &z).unwrap()), kzg_y(&blob, &be32(&z)));
        // another blob differs at a random point
        let other = crate::blob::to_blob(&data[1..]).unwrap();
        let z = BigUint::from(123456789u64);
        assert_ne!(evaluate(&blob, &z), evaluate(&other, &z));
    }

    /// The in-STARK witness (`ss_rap_p3::blob_eval`) gives S with S * (z^4096 - 1) / 4096 equal
    /// to Ethereum's KZG evaluation of the same blob.
    #[test]
    fn stark_witness_matches_c_kzg() {
        let data: Vec<u8> = (0..20_000).map(|i| (i * 13 + 5) as u8).collect();
        let blob = crate::blob::to_blob(&data).unwrap();
        let z = BigUint::from_bytes_be(&crate::public_input::keccak256(b"z")) % modulus();
        let e = ss_rap_p3::blob_eval::elements(&blob).unwrap();
        let (_, s) = ss_rap_p3::blob_eval::trace::<p3_baby_bear::BabyBear>(&e, &z);
        let y = ss_rap_p3::blob_eval::value_from_sum(&s, &z);
        assert_eq!(be32(&y), kzg_y(&blob, &be32(&z)));
    }

    #[test]
    fn precompile_input_verifies() {
        let blob = crate::blob::to_blob(b"SS-RAP").unwrap();
        let z = be32(&BigUint::from(42u32));
        let v = point_evaluation_input(&blob, &z).unwrap();
        assert_eq!(v.len(), 192);
        let s = c_kzg::ethereum_kzg_settings(0);
        let c = c_kzg::Bytes48::from_bytes(&v[96..144]).unwrap();
        let p = c_kzg::Bytes48::from_bytes(&v[144..]).unwrap();
        let y = c_kzg::Bytes32::from_bytes(&v[64..96]).unwrap();
        assert!(s.verify_kzg_proof(&c, &c_kzg::Bytes32::from(z), &y, &p).unwrap());
        assert_eq!(&v[64..96], &be32(&evaluate(&blob, &BigUint::from(42u32)).unwrap()));
    }
}
