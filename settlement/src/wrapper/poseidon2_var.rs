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
