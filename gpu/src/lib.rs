//! Groth16 prover of the SS-RAP settlement circuits with the multi-scalar multiplications
//! (the bulk of the proving time) on ICICLE: the CUDA backend on a GPU, the CPU backend in tests.
//!
//! The prover is arkworks' `create_proof_with_reduction_and_matrices` step for step: the same
//! QAP witness map (`LibsnarkReduction`, NTTs on the CPU for now), the same five MSMs, the same
//! r, s blinding. Only the MSMs move, so for the same r, s the proof is identical to arkworks'
//! (`tests::matches_arkworks`), and every GPU proof is checked with the ordinary verifier.

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{BigInteger, PrimeField, Zero};
use ark_groth16::r1cs_to_qap::{LibsnarkReduction, R1CSToQAP};
use ark_groth16::{Proof, ProvingKey};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::r1cs::ConstraintMatrices;
use icicle_bn254::curve::{BaseField, CurveCfg, G2BaseField, G2CurveCfg, ScalarField};
use icicle_core::curve::{Affine, Projective};
use icicle_core::msm::{msm, MSMConfig};
use icicle_core::traits::FieldImpl;
use icicle_runtime::memory::HostSlice;
use rayon::prelude::*;
use std::time::{Duration, Instant};

/// Where the MSMs run.
pub enum Backend {
    /// arkworks on the CPU (the reference).
    Ark,
    /// ICICLE on the device set with `init` (CUDA or CPU).
    Icicle,
}

/// Loads the ICICLE backends (`ICICLE_BACKEND_INSTALL_DIR`, else the default location) and
/// selects `device` ("CUDA" or "CPU"). Returns the device actually selected.
pub fn init(device: &str) -> Result<String, String> {
    let _ = icicle_runtime::load_backend_from_env_or_default();
    let d = icicle_runtime::Device::new(device, 0);
    if !icicle_runtime::is_device_available(&d) {
        return Err(format!("ICICLE device {device} is not available (backend not loaded?)"));
    }
    icicle_runtime::set_device(&d).map_err(|e| format!("{e:?}"))?;
    Ok(device.to_string())
}

fn fq(x: &Fq) -> BaseField {
    BaseField::from_bytes_le(&x.into_bigint().to_bytes_le())
}

fn fq2(x: &Fq2) -> G2BaseField {
    let mut b = x.c0.into_bigint().to_bytes_le();
    b.extend(x.c1.into_bigint().to_bytes_le());
    G2BaseField::from_bytes_le(&b)
}

fn fq_back(x: &BaseField) -> Fq {
    Fq::from_le_bytes_mod_order(&x.to_bytes_le())
}

fn fq2_back(x: &G2BaseField) -> Fq2 {
    let b = x.to_bytes_le();
    Fq2::new(Fq::from_le_bytes_mod_order(&b[..32]), Fq::from_le_bytes_mod_order(&b[32..]))
}

fn g1(p: &G1Affine) -> Affine<CurveCfg> {
    match p.xy() {
        Some((x, y)) => Affine { x: fq(&x), y: fq(&y) },
        None => Affine::zero(),
    }
}

fn g2(p: &G2Affine) -> Affine<G2CurveCfg> {
    match p.xy() {
        Some((x, y)) => Affine { x: fq2(&x), y: fq2(&y) },
        None => Affine::zero(),
    }
}

fn g1_back(p: &Projective<CurveCfg>) -> G1Projective {
    let a: Affine<CurveCfg> = (*p).into();
    if a == Affine::zero() {
        return G1Projective::zero();
    }
    G1Affine::new_unchecked(fq_back(&a.x), fq_back(&a.y)).into()
}

fn g2_back(p: &Projective<G2CurveCfg>) -> G2Projective {
    let a: Affine<G2CurveCfg> = (*p).into();
    if a == Affine::zero() {
        return G2Projective::zero();
    }
    G2Affine::new_unchecked(fq2_back(&a.x), fq2_back(&a.y)).into()
}

fn scalars(s: &[Fr]) -> Vec<ScalarField> {
    s.par_iter().map(|x| ScalarField::from_bytes_le(&x.into_bigint().to_bytes_le())).collect()
}

/// The proving key's points in ICICLE's layout, converted once per key.
pub struct GpuKey {
    a: Vec<Affine<CurveCfg>>,
    b_g1: Vec<Affine<CurveCfg>>,
    b_g2: Vec<Affine<G2CurveCfg>>,
    h: Vec<Affine<CurveCfg>>,
    l: Vec<Affine<CurveCfg>>,
}

impl GpuKey {
    pub fn new(pk: &ProvingKey<Bn254>) -> Self {
        let c1 = |v: &[G1Affine]| v.par_iter().map(g1).collect::<Vec<_>>();
        Self {
            a: c1(&pk.a_query),
            b_g1: c1(&pk.b_g1_query),
            b_g2: pk.b_g2_query.par_iter().map(g2).collect(),
            h: c1(&pk.h_query),
            l: c1(&pk.l_query),
        }
    }
}

fn msm_g1(points: &[Affine<CurveCfg>], s: &[ScalarField]) -> G1Projective {
    let n = points.len().min(s.len());
    if n == 0 {
        return G1Projective::zero();
    }
    let mut out = vec![Projective::<CurveCfg>::zero(); 1];
    msm(HostSlice::from_slice(&s[..n]), HostSlice::from_slice(&points[..n]), &MSMConfig::default(), HostSlice::from_mut_slice(&mut out)).expect("ICICLE G1 MSM");
    g1_back(&out[0])
}

fn msm_g2(points: &[Affine<G2CurveCfg>], s: &[ScalarField]) -> G2Projective {
    let n = points.len().min(s.len());
    if n == 0 {
        return G2Projective::zero();
    }
    let mut out = vec![Projective::<G2CurveCfg>::zero(); 1];
    msm(HostSlice::from_slice(&s[..n]), HostSlice::from_slice(&points[..n]), &MSMConfig::default(), HostSlice::from_mut_slice(&mut out)).expect("ICICLE G2 MSM");
    g2_back(&out[0])
}

/// Where the time of one proof went.
#[derive(Clone, Debug, Default)]
pub struct ProveTimes {
    /// QAP witness map (7 NTTs of the domain size, CPU).
    pub witness_map: Duration,
    /// Scalar conversion for ICICLE (zero for `Backend::Ark`).
    pub convert: Duration,
    /// The four G1 MSMs (h, l, a, b_g1).
    pub msm_g1: Duration,
    /// The G2 MSM (b_g2).
    pub msm_g2: Duration,
    pub total: Duration,
}

/// Groth16 proof of `assignment` (instance then witness, `[0] = 1`) for the circuit `mx`,
/// with blinding r, s. `key` is required for `Backend::Icicle`.
pub fn prove(pk: &ProvingKey<Bn254>, key: Option<&GpuKey>, mx: &ConstraintMatrices<Fr>, assignment: &[Fr], r: Fr, s: Fr, backend: &Backend) -> (Proof<Bn254>, ProveTimes) {
    let t_all = Instant::now();
    let mut t = ProveTimes::default();
    let ni = mx.num_instance_variables;
    let t0 = Instant::now();
    let h = LibsnarkReduction::witness_map_from_matrices::<Fr, GeneralEvaluationDomain<Fr>>(mx, ni, mx.num_constraints, assignment).expect("witness map");
    t.witness_map = t0.elapsed();
    let rest = &assignment[1..]; // inputs then witness, without the constant 1
    let aux = &assignment[ni..];

    let (h_acc, l_acc, a_acc, b1_acc, b2_acc) = match backend {
        Backend::Ark => {
            let t0 = Instant::now();
            let m1 = |q: &[G1Affine], v: &[Fr]| {
                let n = q.len().min(v.len());
                G1Projective::msm(&q[..n], &v[..n]).unwrap()
            };
            let r = (m1(&pk.h_query, &h), m1(&pk.l_query, aux), m1(&pk.a_query[1..], rest), m1(&pk.b_g1_query[1..], rest));
            t.msm_g1 = t0.elapsed();
            let t0 = Instant::now();
            let n = (pk.b_g2_query.len() - 1).min(rest.len());
            let b2 = G2Projective::msm(&pk.b_g2_query[1..1 + n], &rest[..n]).unwrap();
            t.msm_g2 = t0.elapsed();
            (r.0, r.1, r.2, r.3, b2)
        }
        Backend::Icicle => {
            let k = key.expect("GpuKey for the ICICLE backend");
            let t0 = Instant::now();
            let (hs, rs) = (scalars(&h), scalars(rest));
            t.convert = t0.elapsed();
            let aux_s = &rs[ni - 1..];
            let t0 = Instant::now();
            let r = (msm_g1(&k.h, &hs), msm_g1(&k.l, aux_s), msm_g1(&k.a[1..], &rs), msm_g1(&k.b_g1[1..], &rs));
            t.msm_g1 = t0.elapsed();
            let t0 = Instant::now();
            let b2 = msm_g2(&k.b_g2[1..], &rs);
            t.msm_g2 = t0.elapsed();
            (r.0, r.1, r.2, r.3, b2)
        }
    };

    // the rest is arkworks' create_proof_with_assignment, unchanged
    let g_a = pk.delta_g1 * r + pk.a_query[0] + a_acc + pk.vk.alpha_g1;
    let g1_b = if r.is_zero() { G1Projective::zero() } else { pk.delta_g1 * s + pk.b_g1_query[0] + b1_acc + pk.beta_g1 };
    let g2_b = pk.vk.delta_g2 * s + pk.b_g2_query[0] + b2_acc + pk.vk.beta_g2;
    let g_c = g_a * s + g1_b * r - pk.delta_g1 * (r * s) + l_acc + h_acc;
    t.total = t_all.elapsed();
    (Proof { a: g_a.into_affine(), b: g2_b.into_affine(), c: g_c.into_affine() }, t)
}

/// r, s exactly as `ss_rap_settlement::groth16::p3_prove_with` draws them for `seed`.
pub fn blinding(seed: u64) -> (Fr, Fr) {
    use ark_std::UniformRand;
    use rand_chacha::rand_core::SeedableRng;
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(seed);
    (Fr::rand(&mut rng), Fr::rand(&mut rng))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_groth16::Groth16;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError};
    use ark_relations::lc;

    /// x^(2^k) = y, with y public: about 2^k constraints.
    struct Pow {
        k: usize,
        x: Fr,
    }

    impl ConstraintSynthesizer<Fr> for Pow {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
            let mut v = self.x;
            for _ in 0..self.k {
                v.square_in_place();
            }
            let y = cs.new_input_variable(|| Ok(v))?;
            let mut cur = cs.new_witness_variable(|| Ok(self.x))?;
            let mut val = self.x;
            for i in 0..self.k {
                val = val * val;
                let next = if i + 1 == self.k { y } else { cs.new_witness_variable(|| Ok(val))? };
                cs.enforce_constraint(lc!() + cur, lc!() + cur, lc!() + next)?;
                cur = next;
            }
            Ok(())
        }
    }

    use ark_ff::Field;

    fn setup(k: usize) -> (ProvingKey<Bn254>, ConstraintMatrices<Fr>, Vec<Fr>) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        Pow { k, x: Fr::from(3u64) }.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        let mx = cs.to_matrices().unwrap();
        let b = cs.borrow().unwrap();
        let z: Vec<Fr> = [b.instance_assignment.clone(), b.witness_assignment.clone()].concat();
        drop(b);
        let pk = ss_rap_settlement::groth16::p3_setup_from_matrices(&mx, &mut <rand_chacha::ChaCha20Rng as rand_chacha::rand_core::SeedableRng>::seed_from_u64(7)).0;
        (pk, mx, z)
    }

    #[test]
    fn matches_arkworks() {
        init("CPU").unwrap();
        let (pk, mx, z) = setup(3000);
        let (r, s) = blinding(5);
        let want = Groth16::<Bn254>::create_proof_with_reduction_and_matrices(&pk, r, s, &mx, mx.num_instance_variables, mx.num_constraints, &z).unwrap();
        let (ark, _) = prove(&pk, None, &mx, &z, r, s, &Backend::Ark);
        assert_eq!(ark, want, "reference path");
        let key = GpuKey::new(&pk);
        let (ic, _) = prove(&pk, Some(&key), &mx, &z, r, s, &Backend::Icicle);
        assert_eq!(ic, want, "ICICLE path");
        let pvk = ark_groth16::prepare_verifying_key(&pk.vk);
        assert!(Groth16::<Bn254>::verify_proof(&pvk, &ic, &z[1..mx.num_instance_variables]).unwrap());
        // a wrong witness gives a proof that does not verify
        let mut bad = z.clone();
        bad[5] += Fr::from(1u64);
        let (p, _) = prove(&pk, Some(&key), &mx, &bad, r, s, &Backend::Icicle);
        assert!(!Groth16::<Bn254>::verify_proof(&pvk, &p, &z[1..mx.num_instance_variables]).unwrap());
    }

    #[test]
    fn points_round_trip() {
        use ark_std::UniformRand;
        let mut rng = <rand_chacha::ChaCha20Rng as rand_chacha::rand_core::SeedableRng>::seed_from_u64(1);
        for _ in 0..10 {
            let p = G1Projective::rand(&mut rng);
            assert_eq!(g1_back(&g1(&p.into_affine()).to_projective()), p);
            let q = G2Projective::rand(&mut rng);
            assert_eq!(g2_back(&g2(&q.into_affine()).to_projective()), q);
        }
        assert!(g1_back(&g1(&G1Affine::zero()).to_projective()).is_zero());
    }
}
