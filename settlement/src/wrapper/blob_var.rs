//! Audit H-01 in the settlement circuit: from the STARK's blob claim to what the contract checks.
//!
//! The batch STARK proves, for its blob slots j, the digest D_j of the elements it holds and
//! S_j = sum_i e_i w_i / (z - w_i) at a point z it takes as a public value
//! (`ss_rap_p3::blob_eval`). This circuit
//!
//! 1. derives the point from the digests and the header's blobs hash, after both are fixed:
//!    z = Poseidon(tag, pack(D_0), .., pack(D_{k-1}), blobsHash_hi, blobsHash_lo) (BN254, so
//!    z < r_BN254 < r_BLS), and requires the STARK's z to be its 32 little-endian bytes;
//! 2. computes y_j = S_j (z^4096 - 1) / 4096 over the BLS12-381 scalar field (emulated), with
//!    S_j the STARK's canonical bytes;
//! 3. returns z and every y_j as 32-byte big-endian words for the header hash.
//!
//! The contract checks p_j(z) = y_j for blob j with the point-evaluation precompile, and y_j = 0
//! for a slot without a blob. Two different polynomials agree at z with probability at most
//! 4096 / r_BN254, so the elements the STARK holds are the blobs' elements.

use ark_bn254::Fr;
use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_ff::fields::{Fp256, MontBackend, MontConfig};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::emulated_fp::EmulatedFpVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::convert::ToBitsGadget;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use num_bigint::BigUint;
use ss_rap_p3::blob_eval::{BlobClaim, DIGEST};
use ss_rap_v2::hash::{pack, poseidon_config, poseidon_hash, tag_fr};

type R<T> = Result<T, SynthesisError>;

/// The BLS12-381 scalar field (EIP-4844's BLS_MODULUS).
#[derive(MontConfig)]
#[modulus = "52435875175126190479447740508185965837690552500527637822603658699938581184513"]
#[generator = "7"]
pub struct BlsFrConfig;
pub type BlsFr = Fp256<MontBackend<BlsFrConfig, 4>>;

const TAG: &[u8] = b"SS-RAP/v2/blob-point";
const BABYBEAR: u64 = 2013265921;

/// The blobs hash as two field elements (big-endian halves of 16 bytes).
fn halves(h: &[u8; 32]) -> [Fr; 2] {
    [Fr::from_be_bytes_mod_order(&h[..16]), Fr::from_be_bytes_mod_order(&h[16..])]
}

/// Native z for the digests `d` (one per slot) and the header's blobs hash.
pub fn blob_point(d: &[[u32; DIGEST]], blobs_hash: &[u8; 32]) -> BigUint {
    let mut v = vec![tag_fr(TAG)];
    v.extend(d.iter().map(|dj| pack(dj)[0]));
    v.extend(halves(blobs_hash));
    let z = poseidon_hash(&v);
    BigUint::from_bytes_le(&z.into_bigint().to_bytes_le())
}

/// Native y_j = p_j(z) of a claim, as 32-byte big-endian words.
pub fn blob_values(claim: &BlobClaim) -> Vec<[u8; 32]> {
    claim.s.iter().map(|s| crate::blob_eval::be32(&ss_rap_p3::blob_eval::value_from_sum(s, &claim.z))).collect()
}

/// The STARK's blob public values as circuit values, in `BlobClaim::public_values` order.
pub struct BlobPublicVar {
    pub z: Vec<FpVar<Fr>>,
    pub s: Vec<Vec<FpVar<Fr>>>,
    pub d: Vec<Vec<FpVar<Fr>>>,
}

impl BlobPublicVar {
    /// Witnesses for `slots` slots. Bytes are checked where they are used (z, S); the digest
    /// values are range-checked here as canonical BabyBear values.
    pub fn witness(cs: &ConstraintSystemRef<Fr>, claim: Option<&BlobClaim>, slots: usize) -> R<Self> {
        let byte = |v: Option<u8>| FpVar::new_witness(cs.clone(), || v.map(|b| Fr::from(b as u64)).ok_or(SynthesisError::AssignmentMissing));
        let le = |x: &BigUint| ss_rap_p3::blob_eval::le32(x);
        let z = (0..32).map(|k| byte(claim.map(|c| le(&c.z)[k]))).collect::<R<_>>()?;
        let s = (0..slots).map(|j| (0..32).map(|k| byte(claim.map(|c| le(&c.s[j])[k]))).collect::<R<_>>()).collect::<R<_>>()?;
        let mut d = Vec::with_capacity(slots);
        for j in 0..slots {
            let mut dj = Vec::with_capacity(DIGEST);
            for k in 0..DIGEST {
                let bits: Vec<Boolean<Fr>> = (0..31).map(|b| Boolean::new_witness(cs.clone(), || claim.map(|c| (c.d[j][k] >> b) & 1 == 1).ok_or(SynthesisError::AssignmentMissing))).collect::<R<_>>()?;
                Boolean::enforce_smaller_or_equal_than_le(&bits, [BABYBEAR - 1])?;
                dj.push(Boolean::le_bits_to_fp(&bits)?);
            }
            d.push(dj);
        }
        Ok(Self { z, s, d })
    }

    /// In `BlobClaim::public_values` order: z, then per slot S_j and D_j.
    pub fn flat(&self) -> Vec<FpVar<Fr>> {
        let mut v = self.z.clone();
        for (s, d) in self.s.iter().zip(&self.d) {
            v.extend(s.iter().cloned());
            v.extend(d.iter().cloned());
        }
        v
    }
}

/// LE bits -> LE bytes as field values.
fn bytes_of(bits: &[Boolean<Fr>]) -> R<Vec<FpVar<Fr>>> {
    bits.chunks(8).map(Boolean::le_bits_to_fp).collect()
}

/// A canonical BLS value whose LE bits are returned with it (255 bits, padded to 256).
fn bls_witness(cs: &ConstraintSystemRef<Fr>, v: Option<BigUint>) -> R<(EmulatedFpVar<BlsFr, Fr>, Vec<Boolean<Fr>>)> {
    let x = EmulatedFpVar::<BlsFr, Fr>::new_witness(cs.clone(), || v.map(|v| BlsFr::from_le_bytes_mod_order(&v.to_bytes_le())).ok_or(SynthesisError::AssignmentMissing))?;
    let mut bits = x.to_bits_le()?;
    bits.resize(256, Boolean::FALSE);
    Ok((x, bits))
}

/// Value of LE byte variables (prover only).
fn bytes_value(b: &[FpVar<Fr>]) -> Option<BigUint> {
    let v: Option<Vec<u8>> = b.iter().map(|x| x.value().ok().map(|f| f.into_bigint().as_ref()[0] as u8)).collect();
    v.map(|v| BigUint::from_bytes_le(&v))
}

/// Big-endian 32-byte word of LE bits, as header bits (bytes in order, LSB first in a byte).
fn be_word(bits: &[Boolean<Fr>]) -> Vec<Boolean<Fr>> {
    (0..32).rev().flat_map(|k| bits[8 * k..8 * k + 8].to_vec()).collect()
}

/// Enforces the derivation of z and returns the header bits of z and every y_j (big-endian
/// words). `blobs_hash` is the header's blobs hash, as header bits.
pub fn blob_evals(cs: &ConstraintSystemRef<Fr>, pv: &BlobPublicVar, blobs_hash: &[Boolean<Fr>]) -> R<Vec<Boolean<Fr>>> {
    assert_eq!(blobs_hash.len(), 256);
    // 1. z = Poseidon(tag, pack(D_j).., hi, lo)
    let mut inputs = vec![FpVar::constant(tag_fr(TAG))];
    for dj in &pv.d {
        let mut acc = FpVar::zero();
        for v in dj.iter().rev() {
            acc = acc * Fr::from(1u64 << 31) + v;
        }
        inputs.push(acc);
    }
    for half in blobs_hash.chunks(128) {
        // big-endian bytes, LSB-first bits within a byte
        let mut acc = FpVar::zero();
        for byte in half.chunks(8) {
            acc = acc * Fr::from(256u64) + Boolean::le_bits_to_fp(byte)?;
        }
        inputs.push(acc);
    }
    let mut sponge = PoseidonSpongeVar::new(cs.clone(), poseidon_config());
    sponge.absorb(&inputs)?;
    let z = sponge.squeeze_field_elements(1)?.remove(0);
    let mut z_bits = z.to_bits_le()?;
    z_bits.resize(256, Boolean::FALSE);
    for (b, v) in bytes_of(&z_bits)?.iter().zip(&pv.z) {
        b.enforce_equal(v)?;
    }
    // 2. the same z over BLS12-381, and f = (z^4096 - 1) / 4096
    let (ze, ze_bits) = bls_witness(cs, bytes_value(&pv.z))?;
    for (a, b) in ze_bits.iter().zip(&z_bits) {
        a.enforce_equal(b)?;
    }
    let mut zn = ze;
    for _ in 0..12 {
        zn = zn.square()?;
    }
    let inv_n = BlsFr::from(4096u64).inverse().unwrap();
    let f = (zn - EmulatedFpVar::constant(BlsFr::from(1u64))) * EmulatedFpVar::constant(inv_n);
    // 3. y_j = S_j f
    let mut out = be_word(&z_bits);
    for s in &pv.s {
        let (se, s_bits) = bls_witness(cs, bytes_value(s))?;
        for (b, v) in bytes_of(&s_bits)?.iter().zip(s) {
            b.enforce_equal(v)?;
        }
        let y = &se * &f;
        let mut y_bits = y.to_bits_le()?;
        y_bits.resize(256, Boolean::FALSE);
        out.extend(be_word(&y_bits));
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;

    fn header_bits(cs: &ConstraintSystemRef<Fr>, h: &[u8; 32]) -> Vec<Boolean<Fr>> {
        (0..256).map(|i| Boolean::new_witness(cs.clone(), || Ok((h[i / 8] >> (i % 8)) & 1 == 1)).unwrap()).collect()
    }

    fn bytes_of_bits(b: &[Boolean<Fr>]) -> Vec<u8> {
        b.chunks(8).map(|c| c.iter().enumerate().map(|(i, x)| (x.value().unwrap() as u8) << i).sum()).collect()
    }

    #[test]
    fn circuit_matches_native_and_c_kzg() {
        let data: Vec<u8> = (0..40_000).map(|i| (i * 7 + 3) as u8).collect();
        let blob = crate::blob::to_blob(&data).unwrap();
        let e = ss_rap_p3::blob_eval::elements(&blob).unwrap();
        let bh = crate::blob::versioned_hash(&blob);
        let d = vec![ss_rap_p3::blob_eval::digests_u32(&e), ss_rap_p3::blob_eval::digests_u32(&vec![BigUint::from(0u32); 4096])];
        let z = blob_point(&d, &bh);
        let input = ss_rap_p3::blob_eval::BlobInput { slots: 2, blobs: vec![e], z: z.clone() };
        let claim = input.claim();
        assert_eq!(claim.d, d);
        let ys = blob_values(&claim);
        // y_0 is Ethereum's KZG evaluation of the blob at z; the empty slot's is 0
        let pe = crate::blob_eval::point_evaluation_input(&blob, &crate::blob_eval::be32(&z)).unwrap();
        assert_eq!(&pe[64..96], &ys[0]);
        assert_eq!(ys[1], [0u8; 32]);

        let run = |claim: &BlobClaim, bh: &[u8; 32]| {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let pv = BlobPublicVar::witness(&cs, Some(claim), 2).unwrap();
            let hb = header_bits(&cs, bh);
            let out = blob_evals(&cs, &pv, &hb).unwrap();
            (cs.is_satisfied().unwrap(), bytes_of_bits(&out), cs.num_constraints())
        };
        let (ok, out, n) = run(&claim, &bh);
        assert!(ok);
        eprintln!("blob point + 2 values: {n} constraints");
        assert_eq!(&out[..32], &crate::blob_eval::be32(&z));
        assert_eq!(&out[32..64], &ys[0]);
        assert_eq!(&out[64..96], &ys[1]);
        // a z that is not the hash of the digests and the blobs hash
        let mut bad = claim.clone();
        bad.z += 1u32;
        assert!(!run(&bad, &bh).0, "z chosen by the prover");
        let mut other = bh;
        other[31] ^= 1;
        assert!(!run(&claim, &other).0, "z of another blobs hash");
        let mut bad = claim.clone();
        bad.d[1][0] ^= 1;
        assert!(!run(&bad, &bh).0, "z of other digests");
        // a sum above the BLS modulus is not canonical: no witness
        let mut bad = claim.clone();
        bad.s[1] = ss_rap_p3::blob_eval::modulus().clone();
        assert!(!run(&bad, &bh).0, "non-canonical sum");
    }
}
