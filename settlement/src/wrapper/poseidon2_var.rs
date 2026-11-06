//! Poseidon2 over BN254 (width 3, x^5, 4 + 4 full rounds, 56 partial) in R1CS: the same
//! permutation as Plonky3's `Poseidon2Bn254<3>` with the constants of `ss_rap_p3::bn254`
//! (blake3("SS-RAP/v2/poseidon2-bn254-t3/<i>") mod r). It hashes the Merkle trees and drives the
//! Fiat-Shamir challenger of the Plonky3 lane proof, so the circuit verifying that proof needs it.
//!
//! Layers (as `p3-poseidon2` for width 3):
//! - external linear layer: x_i += x_0 + x_1 + x_2 (the matrix circ(2, 1, 1));
//! - internal linear layer: s = x_0 + x_1 + x_2, x_0 += s, x_1 += s, x_2 = 2 x_2 + s;
//! - permutation: external layer, 4 full rounds, 56 partial rounds (S-box on x_0 only), 4 full.
//!
//! Cost: 3 constraints per S-box, (8 * 3 + 56) * 3 = 240 constraints per permutation.

use ark_bn254::Fr;
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_relations::r1cs::SynthesisError;
use num_bigint::BigUint;
use std::sync::OnceLock;

pub const HALF_FULL_ROUNDS: usize = 4;
pub const PARTIAL_ROUNDS: usize = 56;

pub struct Constants {
    pub initial: Vec<[Fr; 3]>,
    pub terminal: Vec<[Fr; 3]>,
    pub internal: Vec<Fr>,
}

fn constant(i: usize) -> Fr {
    let mut h = blake3::Hasher::new();
    h.update(format!("SS-RAP/v2/poseidon2-bn254-t3/{i}").as_bytes());
    let mut out = [0u8; 64];
    h.finalize_xof().fill(&mut out);
    Fr::from(BigUint::from_bytes_le(&out) % BigUint::from(Fr::MODULUS))
}

pub fn constants() -> &'static Constants {
    static C: OnceLock<Constants> = OnceLock::new();
    C.get_or_init(|| {
        let mut i = 0;
        let mut next = || {
            i += 1;
            constant(i)
        };
        let initial = (0..HALF_FULL_ROUNDS).map(|_| std::array::from_fn(|_| next())).collect();
        let terminal = (0..HALF_FULL_ROUNDS).map(|_| std::array::from_fn(|_| next())).collect();
        let internal = (0..PARTIAL_ROUNDS).map(|_| next()).collect();
        Constants { initial, terminal, internal }
    })
}

/// Native permutation (for witnesses and tests).
pub fn permute(mut s: [Fr; 3]) -> [Fr; 3] {
    let c = constants();
    let sbox = |x: Fr| x.square().square() * x;
    let ext = |s: &mut [Fr; 3]| {
        let sum = s[0] + s[1] + s[2];
        s.iter_mut().for_each(|x| *x += sum);
    };
    ext(&mut s);
    for rc in &c.initial {
        (0..3).for_each(|i| s[i] = sbox(s[i] + rc[i]));
        ext(&mut s);
    }
    for &rc in &c.internal {
        s[0] = sbox(s[0] + rc);
        let sum = s[0] + s[1] + s[2];
        s[0] += sum;
        s[1] += sum;
        s[2] = s[2] + s[2] + sum;
    }
    for rc in &c.terminal {
        (0..3).for_each(|i| s[i] = sbox(s[i] + rc[i]));
        ext(&mut s);
    }
    s
}

/// In-circuit permutation: 240 constraints.
pub fn permute_var(mut s: [FpVar<Fr>; 3]) -> Result<[FpVar<Fr>; 3], SynthesisError> {
    let c = constants();
    let sbox = |x: FpVar<Fr>| -> Result<FpVar<Fr>, SynthesisError> { Ok(x.square()?.square()? * x) };
    let ext = |s: &mut [FpVar<Fr>; 3]| {
        let sum = &s[0] + &s[1] + &s[2];
        s.iter_mut().for_each(|x| *x += &sum);
    };
    ext(&mut s);
    for rc in &c.initial {
        for i in 0..3 {
            s[i] = sbox(&s[i] + rc[i])?;
        }
        ext(&mut s);
    }
    for &rc in &c.internal {
        s[0] = sbox(&s[0] + rc)?;
        let sum = &s[0] + &s[1] + &s[2];
        s[0] += &sum;
        s[1] += &sum;
        s[2] = s[2].double()? + &sum;
    }
    for rc in &c.terminal {
        for i in 0..3 {
            s[i] = sbox(&s[i] + rc[i])?;
        }
        ext(&mut s);
    }
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use p3_symmetric::Permutation;

    fn to_p3(x: Fr) -> p3_bn254::Bn254 {
        let b: BigUint = x.into();
        p3_bn254::Bn254::from_biguint(num_bigint_05::BigUint::from_bytes_le(&b.to_bytes_le())).unwrap()
    }

    #[test]
    fn matches_plonky3_poseidon2_bn254() {
        let p = ss_rap_p3::bn254::perm();
        for seed in 0..4u64 {
            let input = [Fr::from(seed), Fr::from(seed * 7 + 1), Fr::from(u64::MAX - seed)];
            let ours = permute(input);
            let theirs = p.permute(input.map(to_p3));
            assert_eq!(ours.map(to_p3), theirs, "native vs plonky3");
            let cs = ConstraintSystem::<Fr>::new_ref();
            let vars = input.map(|x| FpVar::new_witness(cs.clone(), || Ok(x)).unwrap());
            let out = permute_var(vars).unwrap();
            assert_eq!(out.iter().map(|v| v.value().unwrap()).collect::<Vec<_>>(), ours.to_vec());
            assert!(cs.is_satisfied().unwrap());
            if seed == 0 {
                eprintln!("poseidon2-bn254 permutation: {} constraints", cs.num_constraints());
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Plonky3's MultiField32PaddingFreeSponge<BabyBear, Bn254, Perm, 3, 2, 1> and
// TruncatedPermutation<Perm, 2, 1, 3> (Merkle leaf hash and node compression).
// ---------------------------------------------------------------------------------------------

/// BabyBear values packed per BN254 element (shifted radix 2^31, `max_shifted_absorb_injective_limbs`).
pub const PACK: usize = 8;
/// Radix bits of the packing (bit length of BabyBear's order - 1).
pub const RADIX_BITS: u32 = 31;
const RATE: usize = 2;

fn pack_native(vals: &[u32]) -> Fr {
    let base = Fr::from(1u64 << RADIX_BITS);
    vals.iter().rev().fold(Fr::from(0u64), |acc, &v| acc * base + Fr::from(v as u64 + 1))
}

/// Native leaf hash of canonical BabyBear values.
pub fn hash_babybear(vals: &[u32]) -> Fr {
    let mut s = [Fr::from(0u64); 3];
    for block in vals.chunks(RATE * PACK) {
        for (i, chunk) in block.chunks(PACK).enumerate() {
            s[i] = pack_native(chunk);
        }
        s = permute(s);
    }
    s[0]
}

/// Native 2-to-1 compression of Merkle nodes.
pub fn compress(l: Fr, r: Fr) -> Fr {
    permute([l, r, Fr::from(0u64)])[0]
}

/// In-circuit leaf hash. `vals` must already be canonical BabyBear values (< p); packing is
/// linear, so the cost is one permutation per 16 values.
pub fn hash_babybear_var(vals: &[FpVar<Fr>]) -> Result<FpVar<Fr>, SynthesisError> {
    let base = Fr::from(1u64 << RADIX_BITS);
    let mut s: [FpVar<Fr>; 3] = std::array::from_fn(|_| FpVar::zero());
    for block in vals.chunks(RATE * PACK) {
        for (i, chunk) in block.chunks(PACK).enumerate() {
            s[i] = chunk.iter().rev().fold(FpVar::zero(), |acc, v| acc * base + v + Fr::from(1u64));
        }
        s = permute_var(s)?;
    }
    Ok(s[0].clone())
}

pub fn compress_var(l: &FpVar<Fr>, r: &FpVar<Fr>) -> Result<FpVar<Fr>, SynthesisError> {
    Ok(permute_var([l.clone(), r.clone(), FpVar::zero()])?[0].clone())
}

#[cfg(test)]
mod sponge_tests {
    use super::*;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;
    use p3_symmetric::{CryptographicHasher, MultiField32PaddingFreeSponge, PseudoCompressionFunction, TruncatedPermutation};

    fn to_fr(x: p3_bn254::Bn254) -> Fr {
        use p3_field::PrimeField;
        let b = x.as_canonical_biguint();
        Fr::from(BigUint::from_bytes_le(&b.to_bytes_le()))
    }

    #[test]
    fn sponge_and_compression_match_plonky3() {
        assert_eq!(p3_field::max_shifted_absorb_injective_limbs::<BabyBear, p3_bn254::Bn254>(), PACK);
        assert_eq!(p3_field::absorb_radix_bits::<BabyBear>(), RADIX_BITS);
        let perm = ss_rap_p3::bn254::perm();
        let h = MultiField32PaddingFreeSponge::<BabyBear, p3_bn254::Bn254, _, 3, 2, 1>::new(perm.clone()).unwrap();
        for len in [1usize, 7, 8, 9, 16, 17, 66, 100] {
            let vals: Vec<u32> = (0..len as u32).map(|i| (i * 2654435761u32) % 2013265921).collect();
            let theirs = to_fr(h.hash_iter(vals.iter().map(|&v| BabyBear::from_u32(v)))[0]);
            assert_eq!(hash_babybear(&vals), theirs, "len {len}");
            let cs = ConstraintSystem::<Fr>::new_ref();
            let vars: Vec<_> = vals.iter().map(|&v| FpVar::new_witness(cs.clone(), || Ok(Fr::from(v as u64))).unwrap()).collect();
            assert_eq!(hash_babybear_var(&vars).unwrap().value().unwrap(), theirs);
            assert!(cs.is_satisfied().unwrap());
        }
        let c = TruncatedPermutation::<_, 2, 1, 3>::new(perm);
        let (a, b) = (Fr::from(12345u64), Fr::from(678u64));
        let to_p3 = |x: Fr| {
            let bi: BigUint = x.into();
            p3_bn254::Bn254::from_biguint(num_bigint_05::BigUint::from_bytes_le(&bi.to_bytes_le())).unwrap()
        };
        let theirs = to_fr(c.compress([[to_p3(a)], [to_p3(b)]])[0]);
        assert_eq!(compress(a, b), theirs);
        let cs = ConstraintSystem::<Fr>::new_ref();
        let (av, bv) = (FpVar::new_witness(cs.clone(), || Ok(a)).unwrap(), FpVar::new_witness(cs.clone(), || Ok(b)).unwrap());
        assert_eq!(compress_var(&av, &bv).unwrap().value().unwrap(), theirs);
    }
}

// ---------------------------------------------------------------------------------------------
// Plonky3 MerkleTreeMmcs (arity 2, cap height 0): batch opening of matrices of several heights.
// ---------------------------------------------------------------------------------------------

use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::select::CondSelectGadget;

/// Enforces that `opened[i]` is row `index >> (log_max - log2 heights[i])` of matrix i under `root`
/// (as `MerkleTreeMmcs::verify_batch`). `heights` are powers of two; `index_bits` is the index
/// in the tallest matrix, LSB first (log2 max height bits); `siblings` has log2 max height entries.
pub fn verify_batch_var(
    root: &FpVar<Fr>,
    heights: &[usize],
    index_bits: &[Boolean<Fr>],
    opened: &[Vec<FpVar<Fr>>],
    siblings: &[FpVar<Fr>],
) -> Result<(), SynthesisError> {
    assert_eq!(heights.len(), opened.len());
    assert!(heights.iter().all(|h| h.is_power_of_two()));
    let max = *heights.iter().max().unwrap();
    let log_max = max.trailing_zeros() as usize;
    assert_eq!(index_bits.len(), log_max);
    assert_eq!(siblings.len(), log_max);
    // tallest first, stable on ties (sorted_by_key)
    let mut order: Vec<usize> = (0..heights.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(heights[i]));
    let rows_at = |h: usize| -> Vec<FpVar<Fr>> { order.iter().filter(|&&i| heights[i] == h).flat_map(|&i| opened[i].iter().cloned()).collect() };
    let mut digest = hash_babybear_var(&rows_at(max))?;
    let mut h = max;
    for (bit, sib) in index_bits.iter().zip(siblings) {
        let left = FpVar::conditionally_select(bit, sib, &digest)?;
        let right = &digest + sib - &left;
        digest = compress_var(&left, &right)?;
        h /= 2;
        if heights.contains(&h) {
            let inj = hash_babybear_var(&rows_at(h))?;
            digest = compress_var(&digest, &inj)?;
        }
    }
    digest.enforce_equal(root)
}

#[cfg(test)]
mod merkle_tests {
    use super::*;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_relations::r1cs::ConstraintSystem;
    use p3_baby_bear::BabyBear;
    use p3_commit::Mmcs;
    use p3_field::{PrimeCharacteristicRing, PrimeField, PrimeField32};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::Dimensions;

    fn to_fr(x: p3_bn254::Bn254) -> Fr {
        Fr::from(BigUint::from_bytes_le(&x.as_canonical_biguint().to_bytes_le()))
    }

    #[test]
    fn merkle_batch_opening_matches_plonky3() {
        let mmcs = ss_rap_p3::bn254::config_mmcs::<BabyBear>();
        let shapes = [(16usize, 5usize), (4, 3), (16, 2), (2, 17), (8, 1)];
        let mats: Vec<RowMajorMatrix<BabyBear>> = shapes
            .iter()
            .enumerate()
            .map(|(m, &(h, w))| RowMajorMatrix::new((0..h * w).map(|i| BabyBear::from_u32((i as u32 + 1) * 7919 + m as u32)).collect(), w))
            .collect();
        let (commit, data) = mmcs.commit(mats);
        let dims: Vec<Dimensions> = shapes.iter().map(|&(h, w)| Dimensions { width: w, height: h }).collect();
        for index in [0usize, 5, 11, 15] {
            let opening = mmcs.open_batch(index, &data);
            mmcs.verify_batch(&commit, &dims, index, (&opening).into()).unwrap();
            let check = |tamper: bool| {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let w = |x: Fr| FpVar::new_witness(cs.clone(), || Ok(x)).unwrap();
                let root = w(to_fr(commit[0][0]));
                let bits: Vec<_> = (0..4).map(|b| Boolean::new_witness(cs.clone(), || Ok((index >> b) & 1 == 1)).unwrap()).collect();
                let mut opened: Vec<Vec<FpVar<Fr>>> = opening.opened_values.iter().map(|r| r.iter().map(|v| w(Fr::from(v.as_canonical_u32() as u64))).collect()).collect();
                if tamper {
                    opened[3][0] = w(Fr::from(1u64));
                }
                let sibs: Vec<_> = opening.opening_proof.iter().map(|d| w(to_fr(d[0]))).collect();
                let heights: Vec<usize> = shapes.iter().map(|s| s.0).collect();
                verify_batch_var(&root, &heights, &bits, &opened, &sibs).unwrap();
                (cs.is_satisfied().unwrap(), cs.num_constraints())
            };
            let (ok, n) = check(false);
            assert!(ok, "index {index}");
            assert!(!check(true).0, "tampered opening");
            if index == 0 {
                eprintln!("merkle batch opening (5 matrices, height 16): {n} constraints");
            }
        }
    }
}
