//! Hash backends for commitments and Fiat-Shamir.
//!
//! - `Blake3`: fastest natively; used when the STARK is verified natively.
//! - `Poseidon` over BN254 (t = 3, x^5, 8 full + 57 partial rounds): ~240 R1CS constraints per
//!   2-to-1 compression, so a BN254 circuit (the Groth16 wrapper) can re-check Merkle paths and
//!   re-derive every challenge. Leaves pack 8 values of 31 bits into one field element.
//!
//! Both produce 32-byte digests; a Poseidon digest is the canonical little-endian encoding of
//! a BN254 scalar.

use ark_bn254::Fr;
use ark_crypto_primitives::sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonConfig, PoseidonSponge};
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ff::{BigInteger, PrimeField};
use std::sync::OnceLock;

pub type Hash = [u8; 32];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HashMode {
    Blake3,
    Poseidon,
}

/// Values packed per field element in Poseidon leaves (8 * 31 = 248 bits < 253).
pub const PACK: usize = 8;

pub fn poseidon_config() -> &'static PoseidonConfig<Fr> {
    static CFG: OnceLock<PoseidonConfig<Fr>> = OnceLock::new();
    CFG.get_or_init(|| {
        let (ark, mds) = find_poseidon_ark_and_mds::<Fr>(254, 2, 8, 57, 0);
        PoseidonConfig::new(8, 57, 5, mds, ark, 2, 1)
    })
}

pub fn fr_to_hash(x: &Fr) -> Hash {
    let mut out = [0u8; 32];
    out.copy_from_slice(&x.into_bigint().to_bytes_le());
    out
}

pub fn hash_to_fr(h: &Hash) -> Fr {
    Fr::from_le_bytes_mod_order(h)
}

/// Domain tag as a field element (a constant in the circuit).
pub fn tag_fr(tag: &[u8]) -> Fr {
    Fr::from_le_bytes_mod_order(&blake3::hash(tag).as_bytes()[..31])
}

/// Packs 31-bit values, 8 per field element: sum v_i * 2^(31 i).
pub fn pack(values: &[u32]) -> Vec<Fr> {
    values
        .chunks(PACK)
        .map(|c| {
            let mut acc = Fr::from(0u64);
            for &v in c.iter().rev() {
                debug_assert!(v < 1 << 31);
                acc = acc * Fr::from(1u64 << 31) + Fr::from(v);
            }
            acc
        })
        .collect()
}

pub fn poseidon_hash(inputs: &[Fr]) -> Fr {
    let mut s = PoseidonSponge::new(poseidon_config());
    s.absorb(&inputs.to_vec());
    s.squeeze_field_elements::<Fr>(1)[0]
}

/// Leaf of 31-bit values under a domain tag.
pub fn hash_leaf(mode: HashMode, tag: &[u8], values: &[u32]) -> Hash {
    match mode {
        HashMode::Blake3 => {
            let mut h = blake3::Hasher::new();
            h.update(tag);
            for v in values {
                h.update(&v.to_le_bytes());
            }
            *h.finalize().as_bytes()
        }
        HashMode::Poseidon => {
            let mut inputs = vec![tag_fr(tag)];
            inputs.extend(pack(values));
            fr_to_hash(&poseidon_hash(&inputs))
        }
    }
}

pub fn hash_node(mode: HashMode, l: &Hash, r: &Hash) -> Hash {
    match mode {
        HashMode::Blake3 => {
            let mut h = blake3::Hasher::new();
            h.update(l);
            h.update(r);
            *h.finalize().as_bytes()
        }
        HashMode::Poseidon => fr_to_hash(&poseidon_hash(&[hash_to_fr(l), hash_to_fr(r)])),
    }
}
