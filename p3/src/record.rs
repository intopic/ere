//! A challenger that forwards to Plonky3's `MultiField32Challenger` (Poseidon2-BN254) and logs
//! every operation in order. The log of a verification is the exact Fiat-Shamir schedule the
//! Groth16 circuit must replay: the circuit runs the same operations on the same sponge, so it
//! agrees with Plonky3 by construction, and a test compares every sampled value.
use crate::bn254::{self, Challenger, Perm, ValMmcs};
use p3_baby_bear::BabyBear;
use p3_bn254::Bn254;
use p3_challenger::{CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_field::{BasedVectorSpace, PrimeField32};
use p3_symmetric::MerkleCap;
use std::sync::{Arc, Mutex};

type F = BabyBear;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    /// observe one BabyBear value
    Observe(u32),
    /// observe one Merkle root (a commitment with cap height 0)
    ObserveDigest(Bn254),
    /// sample one BabyBear value (the value Plonky3 got)
    Sample(u32),
    /// sample `bits` low bits (the value Plonky3 got)
    SampleBits(usize, usize),
}

#[derive(Clone)]
pub struct Recording {
    pub inner: Challenger<F>,
    pub log: Arc<Mutex<Vec<Op>>>,
}

impl Recording {
    pub fn new() -> Self {
        Self { inner: Challenger::<F>::new(bn254::perm()).unwrap(), log: Arc::default() }
    }
    fn push(&self, op: Op) {
        self.log.lock().unwrap().push(op);
    }
}

impl Default for Recording {
    fn default() -> Self {
        Self::new()
    }
}

impl CanObserve<F> for Recording {
    fn observe(&mut self, v: F) {
        self.push(Op::Observe(v.as_canonical_u32()));
        self.inner.observe(v);
    }
}

impl<const N: usize> CanObserve<[F; N]> for Recording {
    fn observe(&mut self, v: [F; N]) {
        for x in v {
            self.observe(x);
        }
    }
}

impl CanObserve<MerkleCap<F, [Bn254; 1]>> for Recording {
    fn observe(&mut self, cap: MerkleCap<F, [Bn254; 1]>) {
        for d in cap.roots() {
            self.push(Op::ObserveDigest(d[0]));
        }
        self.inner.observe(cap);
    }
}

impl CanObserve<&MerkleCap<F, [Bn254; 1]>> for Recording {
    fn observe(&mut self, cap: &MerkleCap<F, [Bn254; 1]>) {
        self.observe(cap.clone());
    }
}

impl<EF: BasedVectorSpace<F>> CanSample<EF> for Recording {
    /// One base value per coefficient, exactly as `MultiField32Challenger::sample`.
    fn sample(&mut self) -> EF {
        EF::from_basis_coefficients_fn(|_| {
            let v: F = self.inner.sample();
            self.push(Op::Sample(v.as_canonical_u32()));
            v
        })
    }
}

impl CanSampleBits<usize> for Recording {
    fn sample_bits(&mut self, bits: usize) -> usize {
        let v = self.inner.sample_bits(bits);
        self.push(Op::SampleBits(bits, v));
        v
    }
}

impl FieldChallenger<F> for Recording {}

impl GrindingChallenger for Recording {
    type Witness = F;
    fn grind(&mut self, bits: usize) -> F {
        assert_eq!(bits, 0, "the recorded configuration has no proof of work");
        F::default()
    }
}


pub use p3_uni_stark::{StarkConfig, StarkGenericConfig};
pub type Config = StarkConfig<bn254::Pcs<F>, bn254::Challenge<F>, Recording>;

/// The Poseidon2-BN254 configuration of `bn254::config`, with the recording challenger.
pub fn config(log_blowup: usize, queries: usize) -> (Config, Arc<Mutex<Vec<Op>>>) {
    let base = bn254::config::<F>(log_blowup, queries);
    let rec = Recording::new();
    let log = rec.log.clone();
    (StarkConfig::new(base.pcs().clone(), rec), log)
}

#[allow(dead_code)]
fn _types(_: Perm, _: ValMmcs<F>) {}

use crate::state::{all_airs, all_instance, Params};
use p3_batch_stark::{prove_batch, verify_batch, BatchProof, ProverData, StarkInstance};
use p3_matrix::dense::RowMajorMatrix;
use ss_rap_v2::state::StateStatement;

fn all_degrees(st: &StateStatement, p: &Params) -> Vec<usize> {
    let mut d = vec![p.log_rows; 5];
    d.push(8);
    d.extend((0..5).map(|l| crate::state::PublicAir::<F>::new(st, l).log_rows));
    d
}

/// `poseidon2_bn254::prove_one` with the recording challenger.
pub fn prove_one(st: &StateStatement, traces: &[Vec<Vec<u32>>; 5], p: &Params) -> BatchProof<Config> {
    let (cfg, _) = config(p.log_blowup, p.queries);
    let (airs, traces, degs) = all_instance::<F>(st, traces);
    let pd = ProverData::<Config>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &degs, &vec![p.budget; airs.len()], p.log_blowup).unwrap();
    let refs: Vec<&RowMajorMatrix<F>> = traces.iter().collect();
    let pv = crate::state::public_values(st, &airs);
    let inst = StarkInstance::new_multiple(&airs, &refs, &pv);
    prove_batch(&cfg, &inst, &pd).expect("prove")
}

/// Verifies like `poseidon2_bn254::verify_one` (without the statement checks) and returns the
/// Fiat-Shamir log of the verification.
pub fn verify_one(st: &StateStatement, proof: &BatchProof<Config>, p: &Params) -> (bool, Vec<Op>) {
    let (cfg, log) = config(p.log_blowup, p.queries);
    let airs = all_airs::<F>(st);
    let pd = ProverData::<Config>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &all_degrees(st, p), &vec![p.budget; airs.len()], p.log_blowup).unwrap();
    log.lock().unwrap().clear();
    let ok = verify_batch(&cfg, &airs, proof, &crate::state::public_values(st, &airs), &pd.common).is_ok();
    let ops = log.lock().unwrap().clone();
    (ok, ops)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recorded_verification_log() {
        let (st, traces) = crate::state::tests_case(1100, 8);
        let p = Params { log_rows: 8, log_blowup: 1, queries: 20, budget: 3 };
        let proof = prove_one(&st, &traces, &p);
        let (ok, ops) = verify_one(&st, &proof, &p);
        assert!(ok);
        let count = |f: fn(&Op) -> bool| ops.iter().filter(|o| f(o)).count();
        eprintln!(
            "ops {}: observe {} digests {} samples {} sample_bits {}",
            ops.len(),
            count(|o| matches!(o, Op::Observe(_))),
            count(|o| matches!(o, Op::ObserveDigest(_))),
            count(|o| matches!(o, Op::Sample(_))),
            count(|o| matches!(o, Op::SampleBits(..)))
        );
        let mut last = String::new();
        let mut n = 0;
        for o in &ops {
            let k = format!("{:?}", std::mem::discriminant(o));
            let name = match o { Op::Observe(_) => "O", Op::ObserveDigest(_) => "D", Op::Sample(_) => "S", Op::SampleBits(b, _) => if *b > 0 { "B" } else { "B0" } };
            if k != last && n > 0 { eprint!("x{n} "); n = 0; }
            if n == 0 { eprint!("{name}"); }
            n += 1;
            last = k;
        }
        eprintln!("x{n}");
    }
}
