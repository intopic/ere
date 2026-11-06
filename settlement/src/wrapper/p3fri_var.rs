//! Plonky3's `TwoAdicFriPcs::verify` (BabyBear, Poseidon2-BN254 Merkle trees, arity-2 folding,
//! final polynomial of length 1, no proof of work) in R1CS, driven by `ChallengerVar`.
//!
//! What it checks, in Plonky3's order (`two_adic_pcs.rs`, `verifier.rs`):
//! 1. transcript: PCS seed, every claimed evaluation, alpha; FRI seed, per round the commitment
//!    and beta; the final polynomial; one index per query;
//! 2. per query: every input batch opens at the index under its commitment; the reduced opening
//!    per height, sum_k alpha^k (p_k(z) - p_k(x)) / (z - x) with the alpha ladder per height;
//!    the arity-2 folds with the siblings (each round's pair opens under that round's
//!    commitment); the last fold equals the final polynomial.
//!
//! The seeds are the domain-separator observations of Plonky3's transcripts: they depend only
//! on the shape, so the circuit takes them as constants (`ss_rap_p3::record` extracts them).
//! All BabyBear arithmetic uses `fp31` (lazy reduction); every value that is hashed or observed
//! is a canonical BabyBear value (< p), enforced where it enters.

use super::challenger_var::{ChallengerVar, P};
use super::fp31::{E4, M31};
use super::poseidon2_var::verify_batch_var;
use ark_bn254::Fr;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::select::CondSelectGadget;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use num_bigint::BigUint;
use ss_rap_v2::Extension4;

/// `BabyBear::two_adic_generator(k)` for k = 0..=27.
pub const TWO_ADIC_GENERATORS: [u32; 28] = [
    0x1, 0x78000000, 0x67055c21, 0x5ee99486, 0xbb4c4e4, 0x2d4cc4da, 0x669d6090, 0x17b56c64, 0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226, 0x4c734715, 0x11c33e2a,
    0x62c3d2b1, 0x77cad399, 0x54c131f4, 0x4cabd6a6, 0x5cf5713f, 0x3e9430e8, 0xba067a3, 0x18adc27d, 0x21fd55bc, 0x4b859b3d, 0x3bd57996, 0x4483d85a, 0x3a26eef8, 0x1a427a41,
];
/// `BabyBear::GENERATOR` (the coset shift of the LDE domains).
pub const GENERATOR: u32 = 31;
const CH: usize = 0; // fp31 channel 0 is BabyBear, extension u^4 - 11 (as Plonky3)

fn mulp(a: u32, b: u32) -> u32 {
    ((a as u64 * b as u64) % P) as u32
}

fn powp(mut a: u32, mut e: u64) -> u32 {
    let mut r = 1u32;
    while e > 0 {
        if e & 1 == 1 {
            r = mulp(r, a);
        }
        a = mulp(a, a);
        e >>= 1;
    }
    r
}

// ---------------------------------------------------------------------------------------------
// canonical BabyBear values
// ---------------------------------------------------------------------------------------------

/// A canonical BabyBear witness (< p) and its 31 bits: 32 constraints + 3.
pub fn bb_witness(cs: &ConstraintSystemRef<Fr>, x: Option<u32>) -> Result<M31, SynthesisError> {
    let bits: Vec<Boolean<Fr>> = (0..31).map(|b| Boolean::new_witness(cs.clone(), || x.map(|v| (v >> b) & 1 == 1).ok_or(SynthesisError::AssignmentMissing))).collect::<Result<_, _>>()?;
    Ok(M31 { v: bb_from_bits(&bits)?, bound: BigUint::from(P), ch: CH })
}

/// The value of 31 bits, constrained < p (p - 1 = 15 * 2^27).
pub fn bb_from_bits(bits: &[Boolean<Fr>]) -> Result<FpVar<Fr>, SynthesisError> {
    let top = &(&(&bits[27] & &bits[28]) & &bits[29]) & &bits[30];
    let low = Boolean::le_bits_to_fp(&bits[..27])?;
    (FpVar::from(top) * &low).enforce_equal(&FpVar::Constant(Fr::from(0u64)))?;
    Boolean::le_bits_to_fp(bits)
}

/// Reduces to the canonical representative: x = q p + r, r < p.
pub fn canon(cs: &ConstraintSystemRef<Fr>, x: &M31) -> Result<M31, SynthesisError> {
    let val = x.value_big();
    let p = BigUint::from(P);
    let r = bb_witness(cs, val.as_ref().map(|v| (v % &p).to_u32_digits().first().copied().unwrap_or(0)))?;
    let qb = (&x.bound / &p).bits() + 1;
    let q = super::fp31::range_witness(cs, val.as_ref().map(|v| v / &p), qb)?;
    (q * Fr::from(P) + &r.v).enforce_equal(&x.v)?;
    Ok(r)
}

pub fn e4_witness(cs: &ConstraintSystemRef<Fr>, x: Option<[u32; 4]>) -> Result<E4, SynthesisError> {
    let c: Vec<M31> = (0..4).map(|k| bb_witness(cs, x.map(|v| v[k]))).collect::<Result<_, _>>()?;
    Ok(E4 { c: [c[0].clone(), c[1].clone(), c[2].clone(), c[3].clone()] })
}

pub fn e4_canon(cs: &ConstraintSystemRef<Fr>, x: &E4) -> Result<E4, SynthesisError> {
    let c: Vec<M31> = x.c.iter().map(|m| canon(cs, m)).collect::<Result<_, _>>()?;
    Ok(E4 { c: [c[0].clone(), c[1].clone(), c[2].clone(), c[3].clone()] })
}

fn e4_const(x: [u32; 4]) -> E4 {
    E4 { c: x.map(|v| M31::constant(v, CH)) }
}

fn e4_select(b: &Boolean<Fr>, t: &E4, f: &E4) -> Result<E4, SynthesisError> {
    let c: Vec<M31> = (0..4)
        .map(|k| {
            let v = FpVar::conditionally_select(b, &t.c[k].v, &f.c[k].v)?;
            Ok(M31 { v, bound: t.c[k].bound.clone().max(f.c[k].bound.clone()), ch: CH })
        })
        .collect::<Result<_, SynthesisError>>()?;
    Ok(E4 { c: [c[0].clone(), c[1].clone(), c[2].clone(), c[3].clone()] })
}

/// 1 / x for x != 0 (witness, checked by x * inv = 1).
pub fn e4_inverse(cs: &ConstraintSystemRef<Fr>, x: &E4) -> Result<E4, SynthesisError> {
    let inv = x.value().map(|v| Extension4::new(v[0], v[1], v[2], v[3]).inverse(CH).c);
    let iv = e4_witness(cs, inv)?;
    x.mul(&iv).sub(&e4_const([1, 0, 0, 0])).assert_zero(cs)?;
    Ok(iv)
}

/// 1 / x in the base field.
fn bb_inverse(cs: &ConstraintSystemRef<Fr>, x: &M31) -> Result<M31, SynthesisError> {
    let inv = x.value().map(|v| powp(v, P - 2));
    let iv = bb_witness(cs, inv)?;
    x.mul(&iv).sub(&M31::constant(1, CH)).assert_zero(cs)?;
    Ok(iv)
}

/// prod_i (base^(2^i))^(bits[i]) for a constant base, reduced after every step.
fn pow_bits(cs: &ConstraintSystemRef<Fr>, base: u32, bits: &[Boolean<Fr>]) -> Result<M31, SynthesisError> {
    let mut acc = M31::constant(1, CH);
    let mut b = base;
    for bit in bits {
        // acc * (1 + bit (b - 1))
        let factor = M31 { v: FpVar::from(bit.clone()) * Fr::from((b as u64 + P - 1) % P) + Fr::from(1u64), bound: BigUint::from(P), ch: CH };
        acc = acc.mul(&factor).reduce(cs)?;
        b = mulp(b, b);
    }
    Ok(acc)
}

fn observe_e4(ch: &mut ChallengerVar, x: &E4) -> Result<(), SynthesisError> {
    for c in &x.c {
        ch.observe(&c.v)?;
    }
    Ok(())
}

fn sample_e4(ch: &mut ChallengerVar) -> Result<E4, SynthesisError> {
    let c: Vec<M31> = (0..4).map(|_| ch.sample().map(|s| M31 { v: s.value, bound: BigUint::from(P), ch: CH })).collect::<Result<_, _>>()?;
    Ok(E4 { c: [c[0].clone(), c[1].clone(), c[2].clone(), c[3].clone()] })
}

// ---------------------------------------------------------------------------------------------
// shape and witness
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct MatShape {
    /// log2 of the trace domain size (the LDE has `log_size + log_blowup`).
    pub log_size: usize,
    pub width: usize,
    pub num_points: usize,
}

#[derive(Clone, Debug)]
pub struct FriShape {
    pub batches: Vec<Vec<MatShape>>,
    pub log_blowup: usize,
    pub queries: usize,
    pub pcs_seed: Vec<u32>,
    pub fri_seed: Vec<u32>,
}

impl FriShape {
    pub fn log_max(&self) -> usize {
        self.batches.iter().flatten().map(|m| m.log_size).max().unwrap() + self.log_blowup
    }
    pub fn rounds(&self) -> usize {
        self.log_max() - self.log_blowup
    }
}

/// The FRI part of a Plonky3 PCS proof, in plain values (Merkle paths expanded per query).
#[derive(Clone, Debug)]
pub struct FriWitness {
    pub commit_phase_commits: Vec<Fr>,
    pub final_poly: [u32; 4],
    /// [query][batch][matrix] -> opened row
    pub input_rows: Vec<Vec<Vec<Vec<u32>>>>,
    /// [query][batch] -> sibling digests, leaf level first
    pub input_paths: Vec<Vec<Vec<Fr>>>,
    /// [query][round] -> the sibling value
    pub siblings: Vec<Vec<[u32; 4]>>,
    /// [query][round] -> sibling digests
    pub round_paths: Vec<Vec<Vec<Fr>>>,
}

pub struct QueryVar {
    input_rows: Vec<Vec<Vec<M31>>>,
    input_paths: Vec<Vec<FpVar<Fr>>>,
    siblings: Vec<E4>,
    round_paths: Vec<Vec<FpVar<Fr>>>,
}

pub struct FriProofVar {
    pub commit_phase_commits: Vec<FpVar<Fr>>,
    pub final_poly: E4,
    queries: Vec<QueryVar>,
}

impl FriProofVar {
    pub fn witness(cs: &ConstraintSystemRef<Fr>, shape: &FriShape, w: Option<&FriWitness>) -> Result<Self, SynthesisError> {
        let fr = |x: Option<Fr>| FpVar::new_witness(cs.clone(), || x.ok_or(SynthesisError::AssignmentMissing));
        let log_max = shape.log_max();
        let rounds = shape.rounds();
        let commit_phase_commits = (0..rounds).map(|r| fr(w.map(|w| w.commit_phase_commits[r]))).collect::<Result<_, _>>()?;
        let final_poly = e4_witness(cs, w.map(|w| w.final_poly))?;
        let mut queries = Vec::with_capacity(shape.queries);
        for q in 0..shape.queries {
            let mut input_rows = Vec::new();
            let mut input_paths = Vec::new();
            for (b, mats) in shape.batches.iter().enumerate() {
                let rows = mats
                    .iter()
                    .enumerate()
                    .map(|(m, ms)| (0..ms.width).map(|k| bb_witness(cs, w.map(|w| w.input_rows[q][b][m][k]))).collect::<Result<Vec<_>, _>>())
                    .collect::<Result<Vec<_>, _>>()?;
                input_rows.push(rows);
                let hb = mats.iter().map(|m| m.log_size).max().unwrap() + shape.log_blowup;
                input_paths.push((0..hb).map(|i| fr(w.map(|w| w.input_paths[q][b][i]))).collect::<Result<Vec<_>, _>>()?);
            }
            let siblings = (0..rounds).map(|r| e4_witness(cs, w.map(|w| w.siblings[q][r]))).collect::<Result<Vec<_>, _>>()?;
            let round_paths = (0..rounds).map(|r| (0..log_max - r - 1).map(|i| fr(w.map(|w| w.round_paths[q][r][i]))).collect::<Result<Vec<_>, _>>()).collect::<Result<Vec<_>, _>>()?;
            queries.push(QueryVar { input_rows, input_paths, siblings, round_paths });
        }
        Ok(Self { commit_phase_commits, final_poly, queries })
    }
}

// ---------------------------------------------------------------------------------------------
// the verifier
// ---------------------------------------------------------------------------------------------

/// Verifies the claims `(commits[b], points[b][m][i], values[b][m][i][k])` (every value and point
/// canonical) with the FRI proof, continuing the transcript in `ch`.
pub fn verify_pcs(
    cs: &ConstraintSystemRef<Fr>,
    ch: &mut ChallengerVar,
    shape: &FriShape,
    commits: &[FpVar<Fr>],
    points: &[Vec<Vec<E4>>],
    values: &[Vec<Vec<Vec<E4>>>],
    proof: &FriProofVar,
) -> Result<(), SynthesisError> {
    let log_max = shape.log_max();
    let rounds = shape.rounds();
    assert!(shape.batches.iter().flatten().all(|m| m.log_size > 0), "a degree-1 matrix needs the zero check");

    // 1. transcript
    for &s in &shape.pcs_seed {
        ch.observe(&FpVar::Constant(Fr::from(s as u64)))?;
    }
    for b in values {
        for m in b {
            for pt in m {
                for v in pt {
                    observe_e4(ch, v)?;
                }
            }
        }
    }
    let alpha = sample_e4(ch)?;
    for &s in &shape.fri_seed {
        ch.observe(&FpVar::Constant(Fr::from(s as u64)))?;
    }
    let mut betas = Vec::with_capacity(rounds);
    for c in &proof.commit_phase_commits {
        ch.observe_digest(c)?;
        betas.push(sample_e4(ch)?);
    }
    observe_e4(ch, &proof.final_poly)?;
    let mut indices = Vec::with_capacity(shape.queries);
    for _ in 0..shape.queries {
        indices.push(ch.sample_bits(log_max)?);
    }

    // 2. alpha ladder per height and the sums at z (shared by all queries)
    let mut ladder_len = std::collections::BTreeMap::<usize, usize>::new();
    for mats in &shape.batches {
        for m in mats {
            *ladder_len.entry(m.log_size + shape.log_blowup).or_default() += m.width * m.num_points;
        }
    }
    let n_pow = ladder_len.values().copied().max().unwrap_or(0);
    let mut alpha_pow = vec![e4_const([1, 0, 0, 0])];
    for _ in 1..n_pow {
        let next = alpha_pow.last().unwrap().mul(&alpha).reduce(cs)?;
        alpha_pow.push(next);
    }
    // (log_height, offset, sum_at_z) per (batch, matrix, point), in Plonky3's order
    let mut offsets = std::collections::BTreeMap::<usize, usize>::new();
    let mut reductions = Vec::new();
    for (b, mats) in shape.batches.iter().enumerate() {
        for (m, ms) in mats.iter().enumerate() {
            let lh = ms.log_size + shape.log_blowup;
            for i in 0..ms.num_points {
                let off = offsets.entry(lh).or_default();
                let start = *off;
                *off += ms.width;
                let mut s: Option<E4> = None;
                for k in 0..ms.width {
                    let t = alpha_pow[start + k].mul(&values[b][m][i][k]);
                    s = Some(match s {
                        None => t,
                        Some(a) => a.add(&t),
                    });
                }
                reductions.push((lh, start, s.unwrap().reduce(cs)?));
            }
        }
    }

    // 3. queries
    let betas_sq: Vec<E4> = betas.iter().map(|b| b.mul(b).reduce(cs)).collect::<Result<_, _>>()?;
    let half = M31::constant(((P + 1) / 2) as u32, CH);
    for (q, bits) in indices.iter().enumerate() {
        let qv = &proof.queries[q];
        // input openings
        for (b, mats) in shape.batches.iter().enumerate() {
            let hb = mats.iter().map(|m| m.log_size).max().unwrap() + shape.log_blowup;
            let heights: Vec<usize> = mats.iter().map(|m| 1 << (m.log_size + shape.log_blowup)).collect();
            let rows: Vec<Vec<FpVar<Fr>>> = qv.input_rows[b].iter().map(|r| r.iter().map(|x| x.v.clone()).collect()).collect();
            verify_batch_var(&commits[b], &heights, &bits[log_max - hb..], &rows, &qv.input_paths[b])?;
        }
        // reduced openings per height
        let mut ro = std::collections::BTreeMap::<usize, E4>::new();
        let mut red = reductions.iter();
        for (b, mats) in shape.batches.iter().enumerate() {
            for (m, ms) in mats.iter().enumerate() {
                let lh = ms.log_size + shape.log_blowup;
                // x = GENERATOR * g_lh^rev(index >> (log_max - lh), lh)
                let rev_bits: Vec<Boolean<Fr>> = (0..lh).map(|i| bits[log_max - 1 - i].clone()).collect();
                let x = pow_bits(cs, TWO_ADIC_GENERATORS[lh], &rev_bits)?.mul_const(GENERATOR).reduce(cs)?;
                let row = &qv.input_rows[b][m];
                for i in 0..ms.num_points {
                    let (_, start, sum_z) = red.next().unwrap();
                    let inv = e4_inverse(cs, &points[b][m][i].sub(&E4::from_base(&x)))?;
                    let mut sum_x: Option<E4> = None;
                    for k in 0..ms.width {
                        let t = alpha_pow[start + k].mul_base(&row[k]);
                        sum_x = Some(match sum_x {
                            None => t,
                            Some(a) => a.add(&t),
                        });
                    }
                    let term = sum_z.sub(&sum_x.unwrap()).reduce(cs)?.mul(&inv).reduce(cs)?;
                    let e = ro.remove(&lh).map(|a| a.add(&term)).unwrap_or(term);
                    ro.insert(lh, e);
                }
            }
        }
        // folding
        let mut folded = e4_canon(cs, ro.remove(&log_max).as_ref().expect("an opening at the max height"))?;
        for r in 0..rounds {
            let l = log_max - r; // height before this fold
            let bit = &bits[r];
            let sib = &qv.siblings[r];
            let lo = e4_select(bit, sib, &folded)?;
            let hi = e4_select(bit, &folded, sib)?;
            // the pair opens under this round's commitment at index >> (r + 1)
            let leaf: Vec<FpVar<Fr>> = lo.c.iter().chain(hi.c.iter()).map(|x| x.v.clone()).collect();
            verify_batch_var(&proof.commit_phase_commits[r], &[1 << (l - 1)], &bits[r + 1..log_max], &[leaf], &qv.round_paths[r])?;
            // s = g_l^rev(index >> (r + 1), l - 1)
            let rev_bits: Vec<Boolean<Fr>> = (0..l - 1).map(|i| bits[log_max - 1 - i].clone()).collect();
            let s = pow_bits(cs, TWO_ADIC_GENERATORS[l], &rev_bits)?;
            let inv_2s = bb_inverse(cs, &s.mul_const(2).reduce(cs)?)?;
            // (lo + hi) / 2 + (lo - hi) beta / (2 s)
            let sum = lo.add(&hi).mul_base(&half);
            let diff = lo.sub(&hi).reduce(cs)?.mul(&betas[r]).reduce(cs)?.mul_base(&inv_2s);
            let mut next = sum.add(&diff).reduce(cs)?;
            if let Some(o) = ro.remove(&(l - 1)) {
                next = next.add(&betas_sq[r].mul(&o)).reduce(cs)?;
            }
            folded = e4_canon(cs, &next)?;
        }
        assert!(ro.is_empty());
        for k in 0..4 {
            folded.c[k].v.enforce_equal(&proof.final_poly.c[k].v)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use p3_baby_bear::BabyBear;
    use p3_commit::Pcs;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField, PrimeField32, TwoAdicField};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::Dimensions;
    use p3_uni_stark::StarkGenericConfig;
    use ss_rap_p3::record::{self, Op};

    type EF = BinomialExtensionField<BabyBear, 4>;

    fn to_fr(x: p3_bn254::Bn254) -> Fr {
        Fr::from(BigUint::from_bytes_le(&x.as_canonical_biguint().to_bytes_le()))
    }
    fn ef(x: EF) -> [u32; 4] {
        let c: &[BabyBear] = x.as_basis_coefficients_slice();
        [0, 1, 2, 3].map(|i| c[i].as_canonical_u32())
    }

    #[test]
    fn generators_match_plonky3() {
        for k in 0..=27 {
            assert_eq!(BabyBear::two_adic_generator(k).as_canonical_u32(), TWO_ADIC_GENERATORS[k]);
        }
        assert_eq!(BabyBear::GENERATOR.as_canonical_u32(), GENERATOR);
    }

    /// Splits the recorded log into (pcs seed, fri seed) given the known claim and round counts.
    fn seeds(ops: &[Op], n_claim_values: usize) -> (Vec<u32>, Vec<u32>) {
        let first_sample = ops.iter().position(|o| matches!(o, Op::Sample(_))).unwrap();
        let obs: Vec<u32> = ops[..first_sample].iter().map(|o| if let Op::Observe(v) = o { *v } else { panic!("{o:?}") }).collect();
        let pcs_seed = obs[..obs.len() - 4 * n_claim_values].to_vec();
        let after_alpha = first_sample + 4;
        let first_digest = after_alpha + ops[after_alpha..].iter().position(|o| matches!(o, Op::ObserveDigest(_))).unwrap();
        let fri_seed = ops[after_alpha..first_digest].iter().map(|o| if let Op::Observe(v) = o { *v } else { panic!() }).collect();
        (pcs_seed, fri_seed)
    }

    #[test]
    fn verifies_a_plonky3_pcs_proof() {
        let (log_blowup, queries) = (1usize, 6usize);
        let (cfg, log) = record::config(log_blowup, queries);
        let pcs = cfg.pcs();
        // two commitments: (heights 2^5 and 2^3), (2^4)
        let mk = |h: usize, w: usize, seed: u32| RowMajorMatrix::new((0..h * w).map(|i| BabyBear::from_u32((i as u32 * 7919 + seed) % 2013265921)).collect::<Vec<_>>(), w);
        let specs: Vec<Vec<(usize, usize)>> = vec![vec![(5, 3), (3, 2)], vec![(4, 4)]];
        let mut commits = Vec::new();
        let mut datas = Vec::new();
        for (bi, b) in specs.iter().enumerate() {
            let evals: Vec<_> = b.iter().enumerate().map(|(mi, &(lh, w))| (<_ as Pcs<EF, record::Recording>>::natural_domain_for_degree(pcs, 1 << lh), mk(1 << lh, w, (bi * 10 + mi) as u32))).collect();
            let (c, d) = <_ as Pcs<EF, record::Recording>>::commit(pcs, evals).unwrap();
            commits.push(c);
            datas.push(d);
        }
        let z1 = EF::from_basis_coefficients_slice(&[BabyBear::from_u32(5), BabyBear::from_u32(77), BabyBear::from_u32(9), BabyBear::from_u32(1234567)]).unwrap();
        let z2 = z1 * z1 + EF::ONE;
        // points: matrix (5,3) at z1, z2; (3,2) at z1; (4,4) at z2
        let pts: Vec<Vec<Vec<EF>>> = vec![vec![vec![z1, z2], vec![z1]], vec![vec![z2]]];
        let mut pch = cfg.initialise_challenger();
        let reqs = datas.iter().zip(&pts).map(|(d, p)| (d, p.clone()).into()).collect();
        let (opened, proof) = <_ as Pcs<EF, record::Recording>>::open(pcs, reqs, &mut pch).unwrap();
        // verify with Plonky3, recording the transcript
        let domains = |b: usize, m: usize| <_ as Pcs<EF, record::Recording>>::natural_domain_for_degree(pcs, 1 << specs[b][m].0);
        let claims: Vec<_> = (0..2)
            .map(|b| {
                (commits[b].clone(), (0..specs[b].len()).map(|m| (domains(b, m), pts[b][m].iter().copied().zip(opened[b][m].iter().cloned()).collect::<Vec<_>>()).into()).collect::<Vec<_>>()).into()
            })
            .collect();
        log.lock().unwrap().clear();
        let mut vch = cfg.initialise_challenger();
        <_ as Pcs<EF, record::Recording>>::verify(pcs, claims, &proof, &mut vch).unwrap();
        let ops = log.lock().unwrap().clone();

        // shape
        let batches: Vec<Vec<MatShape>> = specs.iter().zip(&pts).map(|(b, p)| b.iter().zip(p).map(|(&(lh, w), pp)| MatShape { log_size: lh, width: w, num_points: pp.len() }).collect()).collect();
        let n_claims: usize = batches.iter().flatten().map(|m| m.width * m.num_points).sum();
        let log_max = 5 + log_blowup;
        let (pcs_seed, fri_seed) = seeds(&ops, n_claims);
        let shape = FriShape { batches, log_blowup, queries, pcs_seed, fri_seed };

        // witness: expand the pruned Merkle proofs per query
        let indices: Vec<usize> = ops.iter().filter_map(|o| if let Op::SampleBits(_, v) = o { Some(*v) } else { None }).collect();
        let mmcs = ss_rap_p3::bn254::config_mmcs::<BabyBear>();
        let mut input_rows = vec![vec![]; queries];
        let mut input_paths = vec![vec![]; queries];
        for (b, bo) in proof.input_openings.iter().enumerate() {
            let hb = specs[b].iter().map(|s| s.0).max().unwrap() + log_blowup;
            let dims: Vec<Dimensions> = specs[b].iter().map(|&(lh, w)| Dimensions { width: w, height: 1 << (lh + log_blowup) }).collect();
            let red: Vec<usize> = indices.iter().map(|i| i >> (log_max - hb)).collect();
            let paths = mmcs.restore_and_recompute_paths(&dims, &red, &bo.opened_values, &bo.opening_proof).unwrap();
            for q in 0..queries {
                input_rows[q].push(bo.opened_values[q].iter().map(|r| r.iter().map(|v| v.as_canonical_u32()).collect()).collect());
                input_paths[q].push(paths[q].siblings.iter().map(|d| to_fr(d[0])).collect());
            }
        }
        let siblings: Vec<Vec<[u32; 4]>> = (0..queries).map(|q| proof.commit_phase_openings.iter().map(|st| ef(st.sibling_values[q][0])).collect()).collect();
        let w = native_fri_witness(&shape, &proof, &indices, &input_rows, &input_paths, &siblings, &pts, &opened, &ops);
        let run = |w: &FriWitness, opened: &Vec<Vec<Vec<Vec<EF>>>>| {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let mut ch = ChallengerVar::new(cs.clone());
            let commit_vars: Vec<FpVar<Fr>> = commits.iter().map(|c| FpVar::new_witness(cs.clone(), || Ok(to_fr(c[0][0]))).unwrap()).collect();
            let point_vars: Vec<Vec<Vec<E4>>> = pts.iter().map(|b| b.iter().map(|m| m.iter().map(|z| e4_witness(&cs, Some(ef(*z))).unwrap()).collect()).collect()).collect();
            let value_vars: Vec<Vec<Vec<Vec<E4>>>> = opened.iter().map(|b| b.iter().map(|m| m.iter().map(|vs| vs.iter().map(|v| e4_witness(&cs, Some(ef(*v))).unwrap()).collect()).collect()).collect()).collect();
            let pv = FriProofVar::witness(&cs, &shape, Some(w)).unwrap();
            verify_pcs(&cs, &mut ch, &shape, &commit_vars, &point_vars, &value_vars, &pv).unwrap();
            (cs.is_satisfied().unwrap(), cs.num_constraints())
        };
        let opened: Vec<Vec<Vec<Vec<EF>>>> = opened.clone();
        let (ok, n) = run(&w, &opened);
        assert!(ok, "honest PCS proof");
        eprintln!("PCS/FRI verifier ({queries} queries, 3 matrices): {n} constraints");
        // a wrong claimed evaluation
        let mut bad = opened.clone();
        bad[0][1][0][1] += EF::ONE;
        assert!(!run(&w, &bad).0, "wrong claimed evaluation");
        // a wrong final polynomial
        let mut bw = w.clone();
        bw.final_poly[2] = (bw.final_poly[2] + 1) % 2013265921;
        assert!(!run(&bw, &opened).0, "wrong final polynomial");
        // a wrong sibling in a fold
        let mut bw = w.clone();
        bw.siblings[3][2][0] ^= 1;
        assert!(!run(&bw, &opened).0, "wrong sibling");
        // a wrong opened input row
        let mut bw = w.clone();
        bw.input_rows[1][1][0][2] ^= 1;
        assert!(!run(&bw, &opened).0, "wrong input row");
    }

    /// The commit-phase Merkle paths need the opened pairs, which contain the verifier's own
    /// folded values: fold natively (same formulas) to get them, then expand the pruned proofs.
    #[allow(clippy::too_many_arguments)]
    fn native_fri_witness(
        shape: &FriShape,
        proof: &<ss_rap_p3::bn254::Pcs<BabyBear> as Pcs<EF, record::Recording>>::Proof,
        indices: &[usize],
        input_rows: &[Vec<Vec<Vec<u32>>>],
        input_paths: &[Vec<Vec<Fr>>],
        siblings: &[Vec<[u32; 4]>],
        pts: &[Vec<Vec<EF>>],
        opened: &[Vec<Vec<Vec<EF>>>],
        ops: &[Op],
    ) -> FriWitness {
        let log_max = shape.log_max();
        let rounds = shape.rounds();
        let samples: Vec<u32> = ops.iter().filter_map(|o| if let Op::Sample(v) = o { Some(*v) } else { None }).collect();
        let e = |s: &[u32]| EF::from_basis_coefficients_slice(&s.iter().map(|&v| BabyBear::from_u32(v)).collect::<Vec<_>>()).unwrap();
        let alpha = e(&samples[0..4]);
        let betas: Vec<EF> = (0..rounds).map(|r| e(&samples[4 + 4 * r..8 + 4 * r])).collect();
        let mut folded_rows: Vec<Vec<Vec<Vec<BabyBear>>>> = vec![vec![]; rounds]; // [round][query] -> row
        for (q, &index) in indices.iter().enumerate() {
            // reduced openings, as Plonky3
            let mut ro = std::collections::BTreeMap::<usize, EF>::new();
            let mut offs = std::collections::BTreeMap::<usize, usize>::new();
            for (b, mats) in shape.batches.iter().enumerate() {
                for (m, ms) in mats.iter().enumerate() {
                    let lh = ms.log_size + shape.log_blowup;
                    let rev = p3_util::reverse_bits_len(index >> (log_max - lh), lh);
                    let x = BabyBear::GENERATOR * BabyBear::two_adic_generator(lh).exp_u64(rev as u64);
                    for i in 0..ms.num_points {
                        let off = offs.entry(lh).or_default();
                        let start = *off;
                        *off += ms.width;
                        let mut acc = EF::ZERO;
                        let mut ap = alpha.exp_u64(start as u64);
                        for k in 0..ms.width {
                            acc += ap * (opened[b][m][i][k] - EF::from(BabyBear::from_u32(input_rows[q][b][m][k])));
                            ap *= alpha;
                        }
                        *ro.entry(lh).or_insert(EF::ZERO) += acc / (pts[b][m][i] - EF::from(x));
                    }
                }
            }
            let mut folded = ro.remove(&log_max).unwrap();
            let mut idx = index;
            for r in 0..rounds {
                let l = log_max - r;
                let sib = e(&siblings[q][r]);
                let (lo, hi) = if idx & 1 == 1 { (sib, folded) } else { (folded, sib) };
                folded_rows[r].push(vec![[lo, hi].iter().flat_map(|v| v.as_basis_coefficients_slice().to_vec()).collect()]);
                idx >>= 1;
                let s = BabyBear::two_adic_generator(l).exp_u64(p3_util::reverse_bits_len(idx, l - 1) as u64);
                folded = (lo + hi).halve() + (lo - hi) * betas[r] * (s.double()).inverse();
                if let Some(o) = ro.remove(&(l - 1)) {
                    folded += betas[r] * betas[r] * o;
                }
            }
            assert_eq!(folded, proof.final_poly[0]);
        }
        let mmcs = ss_rap_p3::bn254::config_mmcs::<BabyBear>();
        let mut round_paths = vec![vec![]; shape.queries];
        for (r, step) in proof.commit_phase_openings.iter().enumerate() {
            let lf = log_max - r - 1;
            let idx: Vec<usize> = indices.iter().map(|i| i >> (r + 1)).collect();
            let dims = [Dimensions { width: 8, height: 1 << lf }];
            let paths = mmcs.restore_and_recompute_paths(&dims, &idx, &folded_rows[r], &step.opening_proof).unwrap();
            for q in 0..shape.queries {
                round_paths[q].push(paths[q].siblings.iter().map(|d| to_fr(d[0])).collect());
            }
        }
        FriWitness {
            commit_phase_commits: proof.commit_phase_commits.iter().map(|c| to_fr(c[0][0])).collect(),
            final_poly: ef(proof.final_poly[0]),
            input_rows: input_rows.to_vec(),
            input_paths: input_paths.to_vec(),
            siblings: siblings.to_vec(),
            round_paths,
        }
    }
}
