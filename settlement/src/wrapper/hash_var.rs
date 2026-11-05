//! R8.1: the hashing side of the STARK verifier inside the BN254 circuit.
//!
//! Mirrors `HashMode::Poseidon` of the native code exactly:
//! - `TranscriptVar`: the Poseidon duplex transcript (`ss_rap_v2::transcript`), message by
//!   message, and the challenges it derives (base field elements of every lane, query indices);
//! - `leaf_hash`: Poseidon of the tag and the 31-bit values packed 8 per field element;
//! - `merkle_root`: Poseidon 2-to-1 up a path, the side at each level chosen by an index bit.
//!
//! Every value that enters a packed leaf is range-checked to 31 bits: with 32 bits two value
//! vectors could pack to the same element (v0 + 2^31, v1 - 1).

use super::fp31::{range_witness, E4, M31};
use ark_bn254::Fr;
use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::prelude::ToBitsGadget;
use ark_r1cs_std::select::CondSelectGadget;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use num_bigint::BigUint;
use ss_rap_v2::hash::{poseidon_config, tag_fr, PACK};
use ss_rap_v2::transcript::poseidon_message;
use ss_rap_v2::DEFAULT_RNS_CHANNELS;

type R<T> = Result<T, SynthesisError>;

fn constants(v: &[Fr]) -> Vec<FpVar<Fr>> {
    v.iter().map(|&x| FpVar::constant(x)).collect()
}

/// The Poseidon transcript of `ss_rap_v2::transcript::Transcript` (mode `Poseidon`).
pub struct TranscriptVar {
    cs: ConstraintSystemRef<Fr>,
    sponge: PoseidonSpongeVar<Fr>,
}

impl TranscriptVar {
    pub fn new(cs: &ConstraintSystemRef<Fr>, label: &[u8]) -> R<Self> {
        let mut sponge = PoseidonSpongeVar::new(cs.clone(), poseidon_config());
        sponge.absorb(&constants(&poseidon_message(b"SS-RAP/v2/transcript", label)))?;
        Ok(Self { cs: cs.clone(), sponge })
    }

    /// A message the verifier knows when the circuit is built (shapes, labels).
    pub fn absorb_const(&mut self, label: &[u8], data: &[u8]) -> R<()> {
        self.sponge.absorb(&constants(&poseidon_message(label, data)))
    }

    /// A message given as its field elements (`poseidon_message` layout), e.g. a witnessed
    /// statement whose hash is a public input.
    pub fn absorb_elements(&mut self, elems: &[FpVar<Fr>]) -> R<()> {
        self.sponge.absorb(&elems.to_vec())
    }

    /// `absorb_digest` of a Poseidon root: the 32 LE bytes go in as two 16-byte elements.
    pub fn absorb_root(&mut self, label: &[u8], root: &FpVar<Fr>) -> R<()> {
        let bits = root.to_bits_le()?; // canonical
        let lo = Boolean::le_bits_to_fp(&bits[..128])?;
        let hi = Boolean::le_bits_to_fp(&bits[128..])?;
        let msg = vec![FpVar::constant(tag_fr(label)), FpVar::constant(Fr::from(32u64)), lo, hi];
        self.sponge.absorb(&msg)
    }

    /// A message of 16 constant bytes followed by a 32-byte digest (the state AIR's statement):
    /// (prefix, low 128 bits, high 128 bits).
    pub fn absorb_prefixed_digest(&mut self, label: &[u8], prefix: &[u8; 16], digest: &FpVar<Fr>) -> R<()> {
        let bits = digest.to_bits_le()?;
        let lo = Boolean::le_bits_to_fp(&bits[..128])?;
        let hi = Boolean::le_bits_to_fp(&bits[128..])?;
        let msg = vec![FpVar::constant(tag_fr(label)), FpVar::constant(Fr::from(48u64)), FpVar::constant(ark_ff::PrimeField::from_le_bytes_mod_order(prefix)), lo, hi];
        self.sponge.absorb(&msg)
    }

    /// One squeezed element, its low 64 bits (what the native `squeeze_u64` uses).
    fn squeeze_low64(&mut self) -> R<Vec<Boolean<Fr>>> {
        let x = self.sponge.squeeze_field_elements(1)?.remove(0);
        let mut bits = x.to_bits_le()?;
        bits.truncate(64);
        Ok(bits)
    }

    /// `challenge_base`: x mod m with x the low 64 bits of a squeeze.
    pub fn challenge_base(&mut self, ch: usize) -> R<M31> {
        let bits = self.squeeze_low64()?;
        let x = M31 { v: Boolean::le_bits_to_fp(&bits)?, bound: BigUint::from(1u128 << 64), ch };
        x.reduce(&self.cs)
    }

    pub fn challenge_ext4(&mut self, ch: usize) -> R<E4> {
        let c = [self.challenge_base(ch)?, self.challenge_base(ch)?, self.challenge_base(ch)?, self.challenge_base(ch)?];
        Ok(E4 { c })
    }

    /// `challenge_ext4_all` of a proof over every lane.
    pub fn challenge_ext4_all(&mut self) -> R<[E4; DEFAULT_RNS_CHANNELS]> {
        let mut out = Vec::with_capacity(DEFAULT_RNS_CHANNELS);
        for ch in 0..DEFAULT_RNS_CHANNELS {
            out.push(self.challenge_ext4(ch)?);
        }
        Ok(out.try_into().unwrap_or_else(|_| unreachable!()))
    }

    /// `challenge_index` for bound 2^bits: the low bits of a squeeze, little-endian.
    pub fn challenge_index(&mut self, bits: usize) -> R<Vec<Boolean<Fr>>> {
        let mut b = self.squeeze_low64()?;
        b.truncate(bits);
        Ok(b)
    }
}

/// An opened 31-bit value (range-checked so that packing is injective).
pub fn value31(cs: &ConstraintSystemRef<Fr>, x: Option<u32>, ch: usize) -> R<M31> {
    let v = range_witness(cs, x.map(BigUint::from), 31)?;
    Ok(M31 { v, bound: BigUint::from(1u64 << 31), ch })
}

/// `hash_leaf(Poseidon, tag, values)` of 31-bit values.
pub fn leaf_hash(cs: &ConstraintSystemRef<Fr>, tag: &[u8], values: &[FpVar<Fr>]) -> R<FpVar<Fr>> {
    let mut inputs = vec![FpVar::constant(tag_fr(tag))];
    let shift = Fr::from(1u64 << 31);
    for chunk in values.chunks(PACK) {
        let mut acc = FpVar::zero();
        for v in chunk.iter().rev() {
            acc = acc * shift + v;
        }
        inputs.push(acc);
    }
    let mut s = PoseidonSpongeVar::new(cs.clone(), poseidon_config());
    s.absorb(&inputs)?;
    Ok(s.squeeze_field_elements(1)?.remove(0))
}

/// Poseidon 2-to-1 (`hash_node`).
pub fn node_hash(cs: &ConstraintSystemRef<Fr>, l: &FpVar<Fr>, r: &FpVar<Fr>) -> R<FpVar<Fr>> {
    let mut s = PoseidonSpongeVar::new(cs.clone(), poseidon_config());
    s.absorb(&vec![l.clone(), r.clone()])?;
    Ok(s.squeeze_field_elements(1)?.remove(0))
}

/// Root of the path from `leaf` at the position whose bits (LSB first) are `index`.
pub fn merkle_root(cs: &ConstraintSystemRef<Fr>, leaf: &FpVar<Fr>, index: &[Boolean<Fr>], path: &[FpVar<Fr>]) -> R<FpVar<Fr>> {
    assert_eq!(index.len(), path.len());
    let mut h = leaf.clone();
    for (bit, sib) in index.iter().zip(path) {
        // bit 0: h is the left child
        let l = FpVar::conditionally_select(bit, sib, &h)?;
        let r = FpVar::conditionally_select(bit, &h, sib)?;
        h = node_hash(cs, &l, &r)?;
    }
    Ok(h)
}

/// Witnesses a Poseidon digest (a `Hash` holding a canonical field element).
pub fn digest_witness(cs: &ConstraintSystemRef<Fr>, h: Option<&ss_rap_v2::hash::Hash>) -> R<FpVar<Fr>> {
    FpVar::new_witness(cs.clone(), || h.map(ss_rap_v2::hash::hash_to_fr).ok_or(SynthesisError::AssignmentMissing))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_r1cs_std::eq::EqGadget;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use ss_rap_v2::fri::Tree;
    use ss_rap_v2::hash::{hash_leaf, hash_to_fr, HashMode};
    use ss_rap_v2::transcript::Transcript;

    fn m31_value(x: &M31) -> u32 {
        x.value().unwrap()
    }

    #[test]
    fn transcript_matches_native() {
        let mut t = Transcript::with_mode(b"r8", HashMode::Poseidon);
        let root = hash_leaf(HashMode::Poseidon, b"x", &[1, 2, 3]);
        t.absorb(b"stark/statement", b"some statement bytes that are longer than sixteen");
        t.absorb_digest(b"stark/main", &root);
        let chals = t.challenge_ext4_all(b"stark/alpha");
        let idx = t.challenge_index(b"fri/query", 1 << 12);

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut tv = TranscriptVar::new(&cs, b"r8").unwrap();
        tv.absorb_const(b"stark/statement", b"some statement bytes that are longer than sixteen").unwrap();
        let rv = digest_witness(&cs, Some(&root)).unwrap();
        tv.absorb_root(b"stark/main", &rv).unwrap();
        let cv = tv.challenge_ext4_all().unwrap();
        let iv = tv.challenge_index(12).unwrap();
        assert!(cs.is_satisfied().unwrap());
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let got: Vec<u32> = cv[ch].c.iter().map(m31_value).collect();
            assert_eq!(got, chals[ch].c.to_vec(), "lane {ch}");
        }
        let got_idx = iv.iter().enumerate().fold(0usize, |a, (k, b)| a | ((b.value().unwrap() as usize) << k));
        assert_eq!(got_idx, idx);
        eprintln!("transcript gadget: {} constraints", cs.num_constraints());
    }

    #[test]
    fn leaf_and_path_match_native_and_reject_forgeries() {
        let leaves_vals: Vec<Vec<u32>> = (0..16u32).map(|i| (0..11).map(|k| (i * 1000 + k) * 7919 % 2013265921).collect()).collect();
        let leaves: Vec<_> = leaves_vals.iter().map(|v| hash_leaf(HashMode::Poseidon, b"SS-RAP/v2/main", v)).collect();
        let tree = Tree::from_leaves(HashMode::Poseidon, leaves);
        let pos = 11usize;
        let path = tree.path(pos);
        let run = |vals: &[u32], pos: usize, root_ok: bool| -> bool {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let vs: Vec<FpVar<Fr>> = vals.iter().map(|&v| value31(&cs, Some(v), 0).unwrap().v).collect();
            let leaf = leaf_hash(&cs, b"SS-RAP/v2/main", &vs).unwrap();
            let bits: Vec<Boolean<Fr>> = (0..4).map(|k| Boolean::new_witness(cs.clone(), || Ok((pos >> k) & 1 == 1)).unwrap()).collect();
            let p: Vec<FpVar<Fr>> = path.iter().map(|h| digest_witness(&cs, Some(h)).unwrap()).collect();
            let root = merkle_root(&cs, &leaf, &bits, &p).unwrap();
            let mut expected = hash_to_fr(&tree.root());
            if !root_ok {
                expected += Fr::from(1u64);
            }
            root.enforce_equal(&FpVar::new_input(cs.clone(), || Ok(expected)).unwrap()).unwrap();
            cs.is_satisfied().unwrap()
        };
        assert!(run(&leaves_vals[pos], pos, true));
        let mut bad = leaves_vals[pos].clone();
        bad[3] ^= 1;
        assert!(!run(&bad, pos, true), "changed opened value");
        assert!(!run(&leaves_vals[pos], pos ^ 2, true), "wrong position");
        assert!(!run(&leaves_vals[pos], pos, false), "wrong root");
        // a 31-bit witness cannot hold 2^31 + v: it is made of 31 bits
        let cs = ConstraintSystem::<Fr>::new_ref();
        let v = value31(&cs, Some((1u32 << 31) + 5), 0).unwrap();
        assert_eq!(v.value_big().unwrap(), BigUint::from(5u32));
    }
}
