//! The whole Plonky3 batch-STARK verifier (`p3_batch_stark::verify_batch`) for the 5-lane state
//! proof (`ss_rap_p3::state::*::prove_one`, Poseidon2-BN254 configuration) in R1CS:
//!
//! 1. transcript: the shape seed, main and preprocessed commitments, lookup challenges, the
//!    permutation commitment and terminals, the constraint challenge, the quotient commitment,
//!    zeta;
//! 2. the opening argument (`p3fri_var::verify_pcs`) for main (zeta, g zeta), quotient chunks
//!    (zeta), preprocessed (zeta) and permutation (zeta, g zeta) claims, in Plonky3's order;
//! 3. per instance: sum_k alpha^k C_k(zeta) / Z_H(zeta) equals the quotient recomposed from its
//!    chunks (`p3air_eval`, the AIR and LogUp constraints from p3's symbolic lists);
//! 4. the lookup terminals sum to zero.
//!
//! The preprocessed commitment (the byte table) and every shape value are constants of the
//! circuit; the statement enters through the periodic columns of the public AIRs.

use super::challenger_var::ChallengerVar;
use super::fp31::{E4, M31};
use super::p3air_eval::{periodic_at, recompose, selectors, Ctx, Eval, Point, EF, F, R};
use super::p3fri_var::{bn_to_fr, e4_const, e4_inverse, e4_witness, ef_u32, fri_witness, observe_e4, sample_e4, verify_pcs, FriProofVar, FriShape, FriWitness, MatShape, TWO_ADIC_GENERATORS};
use ark_bn254::Fr;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::ConstraintSystemRef;
use num_bigint::BigUint;
use p3_air::symbolic::{AirLayout, SymbolicExpression, SymbolicExpressionExt};
use p3_air::BaseAir;
use p3_batch_stark::{BatchProof, ProverData, StarkGenericConfig};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32};
use p3_lookup::logup::LogUpGadget;
use ss_rap_p3::record::{self, Op};
use ss_rap_p3::state::{all_airs, Params};
use ss_rap_v2::state::StateStatement;

// ---------------------------------------------------------------------------------------------
// R1CS arithmetic for the constraint interpreter
// ---------------------------------------------------------------------------------------------

pub struct CircuitCtx {
    pub cs: ConstraintSystemRef<Fr>,
}

fn bits(x: &E4) -> u64 {
    x.c.iter().map(|m| m.bound.bits()).max().unwrap()
}

impl CircuitCtx {
    fn tame(&self, x: &E4, max_bits: u64) -> R<E4> {
        if bits(x) > max_bits {
            x.reduce(&self.cs)
        } else {
            Ok(x.clone())
        }
    }
}

impl Ctx for CircuitCtx {
    type E = E4;
    fn add(&mut self, a: &E4, b: &E4) -> R<E4> {
        Ok(self.tame(a, 200)?.add(&self.tame(b, 200)?))
    }
    fn sub(&mut self, a: &E4, b: &E4) -> R<E4> {
        Ok(self.tame(a, 200)?.sub(&self.tame(b, 200)?))
    }
    fn neg(&mut self, a: &E4) -> R<E4> {
        Ok(e4_const([0; 4]).sub(&self.tame(a, 200)?))
    }
    fn mul(&mut self, a: &E4, b: &E4) -> R<E4> {
        self.tame(a, 100)?.mul(&self.tame(b, 100)?).reduce(&self.cs)
    }
    fn scale(&mut self, a: &E4, c: u32) -> R<E4> {
        let a = self.tame(a, 150)?;
        Ok(E4 { c: std::array::from_fn(|k| a.c[k].mul_const(c)) })
    }
    fn inv(&mut self, a: &E4) -> R<E4> {
        e4_inverse(&self.cs, &self.tame(a, 100)?)
    }
    fn base(&mut self, c: u32) -> E4 {
        e4_const([c, 0, 0, 0])
    }
    fn ext(&mut self, c: [u32; 4]) -> E4 {
        e4_const(c)
    }
    fn mul_x(&mut self, a: &E4) -> R<E4> {
        let a = self.tame(a, 150)?;
        Ok(E4 { c: [a.c[3].mul_const(11), a.c[0].clone(), a.c[1].clone(), a.c[2].clone()] })
    }
}

// ---------------------------------------------------------------------------------------------
// shape
// ---------------------------------------------------------------------------------------------

pub struct InstShape {
    pub log_n: usize,
    pub width: usize,
    pub pre_width: usize,
    pub main_next: bool,
    pub pre_next: bool,
    /// permutation columns as extension elements (0: no lookups)
    pub perm_cols: usize,
    pub n_chunks: usize,
    /// 1 / shift of every quotient chunk domain
    pub chunk_shift_inv: Vec<u32>,
    /// [k][j] = 1 / Z_{D_j}(first point of D_k)
    pub chunk_cross: Vec<Vec<u32>>,
    pub base: Vec<SymbolicExpression<F>>,
    pub ext: Vec<SymbolicExpressionExt<F, EF>>,
    pub periodic: Vec<Vec<u32>>,
    pub bus: Vec<usize>,
}

pub struct BatchShape {
    pub inst: Vec<InstShape>,
    /// widest lookup tuple (the bus offset is beta^width)
    pub lookup_width: usize,
    pub seed: Vec<u32>,
    pub pre_commit: Fr,
    /// preprocessed matrix -> instance
    pub pre_instances: Vec<usize>,
    pub fri: FriShape,
}

fn observes(ops: &[Op]) -> Vec<u32> {
    ops.iter().map(|o| if let Op::Observe(v) = o { *v } else { panic!("expected observations, got {o:?}") }).collect()
}

/// The circuit's shape for statement `st` (its periodic columns) with parameters `p`. `ops` is
/// the transcript log of any verification of the same shape: the seeds of Plonky3's three
/// transcripts are read from it (they depend on the shape only).
pub fn batch_shape(st: &StateStatement, p: &Params, degree_bits: &[usize], ops: &[Op]) -> BatchShape {
    let (cfg, _) = record::config(p.log_blowup, p.queries);
    let pcs = cfg.pcs();
    let airs = all_airs::<F>(st);
    let pd = ProverData::<record::Config>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, degree_bits, &vec![p.budget; airs.len()], p.log_blowup).unwrap();
    let lookups = &pd.common.lookups;
    // bus ids as lay_out_lookup_challenges
    let mut names: Vec<String> = vec![];
    let mut next = 0usize;
    let mut lookup_width = 1usize;
    let mut inst = Vec::new();
    for (i, air) in airs.iter().enumerate() {
        let bus: Vec<usize> = lookups[i]
            .iter()
            .map(|l| {
                lookup_width = lookup_width.max(l.elements[0].len());
                match &l.kind {
                    p3_lookup::Kind::Global(n) => names.iter().position(|x| x == n).unwrap_or_else(|| {
                        names.push(n.clone());
                        next += 1;
                        next - 1
                    }),
                    p3_lookup::Kind::Local => {
                        next += 1;
                        next - 1
                    }
                }
            })
            .collect();
        let pre_width = air.preprocessed_width();
        let layout = AirLayout { preprocessed_width: pre_width, main_width: air.width(), num_public_values: 0, num_periodic_columns: air.num_periodic_columns(), ..Default::default() };
        let (base, ext) = p3_batch_stark::symbolic::get_symbolic_constraints::<F, EF, _, _>(air, layout, &lookups[i], &LogUpGadget::new());
        let log_n = degree_bits[i];
        let n_chunks = 1usize << p3_batch_stark::symbolic::get_log_num_quotient_chunks_for_domain::<F, EF, _, _>(air, layout, <_ as Pcs<EF, record::Recording>>::natural_domain_for_degree(pcs, 1 << log_n), &lookups[i], 0, &LogUpGadget::new());
        let ext_dom = <_ as Pcs<EF, record::Recording>>::natural_domain_for_degree(pcs, 1 << log_n);
        let doms = ext_dom.try_create_disjoint_domain(n_chunks << log_n).unwrap().split_domains(n_chunks);
        let chunk_shift_inv = doms.iter().map(|d| d.first_point().inverse().as_canonical_u32()).collect();
        let chunk_cross = doms.iter().map(|dk| doms.iter().map(|dj| dj.vanishing_poly_at_point(dk.first_point()).try_inverse().map(|v| v.as_canonical_u32()).unwrap_or(0)).collect()).collect();
        inst.push(InstShape {
            log_n,
            width: air.width(),
            pre_width,
            main_next: !air.main_next_row_columns().is_empty(),
            pre_next: !air.preprocessed_next_row_columns().is_empty(),
            perm_cols: if lookups[i].is_empty() { 0 } else { lookups[i].len() + 1 },
            n_chunks,
            chunk_shift_inv,
            chunk_cross,
            base,
            ext,
            periodic: air.periodic_columns().iter().map(|c| c.iter().map(|v| v.as_canonical_u32()).collect()).collect(),
            bus,
        });
    }
    let pre = pd.common.preprocessed.as_ref().expect("the byte table is preprocessed");
    let pre_instances = pre.matrix_to_instance.clone();
    let pre_commit = bn_to_fr(pre.commitment[0][0]);
    // PCS batches in Plonky3's order: main, quotient chunks, preprocessed, permutation
    let mut batches = vec![
        inst.iter().map(|s| MatShape { log_size: s.log_n, width: s.width, num_points: 1 + s.main_next as usize }).collect::<Vec<_>>(),
        inst.iter().flat_map(|s| (0..s.n_chunks).map(move |_| MatShape { log_size: s.log_n, width: 4, num_points: 1 })).collect(),
        pre_instances.iter().map(|&i| MatShape { log_size: inst[i].log_n, width: inst[i].pre_width, num_points: 1 + inst[i].pre_next as usize }).collect(),
    ];
    let perm: Vec<MatShape> = inst.iter().filter(|s| s.perm_cols > 0).map(|s| MatShape { log_size: s.log_n, width: 4 * s.perm_cols, num_points: 2 }).collect();
    if !perm.is_empty() {
        batches.push(perm);
    }
    // seeds
    let first_digest = ops.iter().position(|o| matches!(o, Op::ObserveDigest(_))).unwrap();
    let seed = observes(&ops[..first_digest]);
    let sample_pos: Vec<usize> = ops.iter().enumerate().filter(|(_, o)| matches!(o, Op::Sample(_))).map(|(k, _)| k).collect();
    let after_zeta = sample_pos[15] + 1; // la, lb, alpha, zeta
    let pcs_alpha = sample_pos[16];
    let n_claims: usize = batches.iter().flatten().map(|m| m.width * m.num_points).sum();
    let obs = observes(&ops[after_zeta..pcs_alpha]);
    let pcs_seed = obs[..obs.len() - 4 * n_claims].to_vec();
    let after_alpha = pcs_alpha + 4;
    let fri_digest = after_alpha + ops[after_alpha..].iter().position(|o| matches!(o, Op::ObserveDigest(_))).unwrap();
    let fri_seed = observes(&ops[after_alpha..fri_digest]);
    let fri = FriShape { batches, log_blowup: p.log_blowup, queries: p.queries, pcs_seed, fri_seed };
    BatchShape { inst, lookup_width, seed, pre_commit, pre_instances, fri }
}

// ---------------------------------------------------------------------------------------------
// witness
// ---------------------------------------------------------------------------------------------

#[derive(Clone)]
pub struct InstWitness {
    pub main_local: Vec<[u32; 4]>,
    pub main_next: Vec<[u32; 4]>,
    pub pre_local: Vec<[u32; 4]>,
    pub pre_next: Vec<[u32; 4]>,
    pub perm_local: Vec<[u32; 4]>,
    pub perm_next: Vec<[u32; 4]>,
    pub chunks: Vec<Vec<[u32; 4]>>,
    pub terminal: Option<[u32; 4]>,
}

#[derive(Clone)]
pub struct BatchWitness {
    pub main: Fr,
    pub perm: Fr,
    pub quotient: Fr,
    pub inst: Vec<InstWitness>,
    pub fri: FriWitness,
}

/// The witness of a proof from `ss_rap_p3::record::prove_one`, with its verification log.
pub fn batch_witness(shape: &BatchShape, proof: &BatchProof<record::Config>, ops: &[Op]) -> BatchWitness {
    let v = |x: &[EF]| x.iter().map(|e| ef_u32(*e)).collect::<Vec<_>>();
    let inst: Vec<InstWitness> = proof
        .opened_values
        .instances
        .iter()
        .enumerate()
        .map(|(i, o)| {
            let b = &o.base_opened_values;
            InstWitness {
                main_local: v(&b.trace_local),
                main_next: b.trace_next.as_deref().map(v).unwrap_or_default(),
                pre_local: b.preprocessed.as_ref().map(|p| v(&p.local)).unwrap_or_default(),
                pre_next: b.preprocessed.as_ref().and_then(|p| p.next.as_deref().map(v)).unwrap_or_default(),
                perm_local: v(&o.permutation_local),
                perm_next: v(&o.permutation_next),
                chunks: b.quotient_chunks.iter().map(|c| v(c)).collect(),
                terminal: proof.lookup_terminals[i].as_ref().map(|t| ef_u32(t.0)),
            }
        })
        .collect();
    let s: Vec<u32> = ops.iter().filter_map(|o| if let Op::Sample(v) = o { Some(*v) } else { None }).collect();
    let e = |k: usize| EF::from_basis_coefficients_slice(&s[k..k + 4].iter().map(|&v| F::from_u32(v)).collect::<Vec<_>>()).unwrap();
    let zeta = e(12);
    let indices: Vec<usize> = ops.iter().filter_map(|o| if let Op::SampleBits(_, v) = o { Some(*v) } else { None }).collect();
    let alpha = e(16);
    let betas: Vec<EF> = (0..shape.fri.rounds()).map(|r| e(20 + 4 * r)).collect();
    let (pts, opened) = claims_native(shape, proof, zeta);
    let fri = fri_witness(&shape.fri, &proof.opening_proof, &indices, alpha, &betas, &pts, &opened);
    BatchWitness { main: bn_to_fr(proof.commitments.main[0][0]), perm: bn_to_fr(proof.commitments.permutation.as_ref().unwrap()[0][0]), quotient: bn_to_fr(proof.commitments.quotient_chunks[0][0]), inst, fri }
}

type Claims<T> = (Vec<Vec<Vec<T>>>, Vec<Vec<Vec<Vec<T>>>>);

fn claims_native(shape: &BatchShape, proof: &BatchProof<record::Config>, zeta: EF) -> Claims<EF> {
    let next = |s: &InstShape| zeta * F::from_u32(TWO_ADIC_GENERATORS[s.log_n]);
    let ov = &proof.opened_values.instances;
    let mut pts = vec![vec![], vec![], vec![], vec![]];
    let mut vals = vec![vec![], vec![], vec![], vec![]];
    for (i, s) in shape.inst.iter().enumerate() {
        let b = &ov[i].base_opened_values;
        let mut p = vec![zeta];
        let mut v = vec![b.trace_local.clone()];
        if s.main_next {
            p.push(next(s));
            v.push(b.trace_next.clone().unwrap());
        }
        pts[0].push(p);
        vals[0].push(v);
        for c in &b.quotient_chunks {
            pts[1].push(vec![zeta]);
            vals[1].push(vec![c.clone()]);
        }
    }
    for &i in &shape.pre_instances {
        let pr = ov[i].base_opened_values.preprocessed.as_ref().unwrap();
        let mut p = vec![zeta];
        let mut v = vec![pr.local.clone()];
        if shape.inst[i].pre_next {
            p.push(next(&shape.inst[i]));
            v.push(pr.next.clone().unwrap());
        }
        pts[2].push(p);
        vals[2].push(v);
    }
    for (i, s) in shape.inst.iter().enumerate() {
        if s.perm_cols > 0 {
            pts[3].push(vec![zeta, next(s)]);
            vals[3].push(vec![ov[i].permutation_local.clone(), ov[i].permutation_next.clone()]);
        }
    }
    if pts[3].is_empty() {
        pts.pop();
        vals.pop();
    }
    (pts, vals)
}

// ---------------------------------------------------------------------------------------------
// the verifier circuit
// ---------------------------------------------------------------------------------------------

struct InstVars {
    main_local: Vec<E4>,
    main_next: Vec<E4>,
    pre_local: Vec<E4>,
    pre_next: Vec<E4>,
    perm_local: Vec<E4>,
    perm_next: Vec<E4>,
    chunks: Vec<Vec<E4>>,
    terminal: Option<E4>,
}

fn alloc_vec(cs: &ConstraintSystemRef<Fr>, n: usize, w: Option<&Vec<[u32; 4]>>) -> R<Vec<E4>> {
    (0..n).map(|k| e4_witness(cs, w.map(|w| w[k]))).collect()
}

/// Enforces that the witness is a valid Plonky3 batch proof of `shape`'s statement.
pub fn verify_batch_var(cs: &ConstraintSystemRef<Fr>, shape: &BatchShape, w: Option<&BatchWitness>) -> R<()> {
    let fr = |x: Option<Fr>| FpVar::new_witness(cs.clone(), || x.ok_or(ark_relations::r1cs::SynthesisError::AssignmentMissing));
    let main = fr(w.map(|w| w.main))?;
    let perm = fr(w.map(|w| w.perm))?;
    let quot = fr(w.map(|w| w.quotient))?;
    let pre = FpVar::Constant(shape.pre_commit);
    let mut iv = Vec::new();
    for (i, s) in shape.inst.iter().enumerate() {
        let wi = w.map(|w| &w.inst[i]);
        iv.push(InstVars {
            main_local: alloc_vec(cs, s.width, wi.map(|x| &x.main_local))?,
            main_next: if s.main_next { alloc_vec(cs, s.width, wi.map(|x| &x.main_next))? } else { vec![] },
            pre_local: alloc_vec(cs, s.pre_width, wi.map(|x| &x.pre_local))?,
            pre_next: if s.pre_next { alloc_vec(cs, s.pre_width, wi.map(|x| &x.pre_next))? } else { vec![] },
            perm_local: alloc_vec(cs, 4 * s.perm_cols, wi.map(|x| &x.perm_local))?,
            perm_next: alloc_vec(cs, 4 * s.perm_cols, wi.map(|x| &x.perm_next))?,
            chunks: (0..s.n_chunks).map(|k| alloc_vec(cs, 4, wi.map(|x| &x.chunks[k]))).collect::<R<_>>()?,
            terminal: if s.perm_cols > 0 { Some(e4_witness(cs, wi.map(|x| x.terminal.unwrap()))?) } else { None },
        });
    }
    let fri = FriProofVar::witness(cs, &shape.fri, w.map(|w| &w.fri))?;

    // 1. transcript
    let mut ch = ChallengerVar::new(cs.clone());
    for &v in &shape.seed {
        ch.observe(&FpVar::Constant(Fr::from(v as u64)))?;
    }
    ch.observe_digest(&main)?;
    ch.observe_digest(&pre)?;
    let la = sample_e4(&mut ch)?;
    let lb = sample_e4(&mut ch)?;
    ch.observe_digest(&perm)?;
    for v in &iv {
        if let Some(t) = &v.terminal {
            observe_e4(&mut ch, t)?;
        }
    }
    let alpha = sample_e4(&mut ch)?;
    ch.observe_digest(&quot)?;
    let zeta = sample_e4(&mut ch)?;

    // 2. opening argument
    let mut ctx = CircuitCtx { cs: cs.clone() };
    let nexts: Vec<E4> = shape.inst.iter().map(|s| ctx.scale(&zeta, TWO_ADIC_GENERATORS[s.log_n]).and_then(|x| x.reduce(cs))).collect::<R<_>>()?;
    let mut pts: Vec<Vec<Vec<E4>>> = vec![vec![], vec![], vec![], vec![]];
    let mut vals: Vec<Vec<Vec<Vec<E4>>>> = vec![vec![], vec![], vec![], vec![]];
    for (i, s) in shape.inst.iter().enumerate() {
        let mut p = vec![zeta.clone()];
        let mut v = vec![iv[i].main_local.clone()];
        if s.main_next {
            p.push(nexts[i].clone());
            v.push(iv[i].main_next.clone());
        }
        pts[0].push(p);
        vals[0].push(v);
        for c in &iv[i].chunks {
            pts[1].push(vec![zeta.clone()]);
            vals[1].push(vec![c.clone()]);
        }
    }
    for &i in &shape.pre_instances {
        let mut p = vec![zeta.clone()];
        let mut v = vec![iv[i].pre_local.clone()];
        if shape.inst[i].pre_next {
            p.push(nexts[i].clone());
            v.push(iv[i].pre_next.clone());
        }
        pts[2].push(p);
        vals[2].push(v);
    }
    for (i, s) in shape.inst.iter().enumerate() {
        if s.perm_cols > 0 {
            pts[3].push(vec![zeta.clone(), nexts[i].clone()]);
            vals[3].push(vec![iv[i].perm_local.clone(), iv[i].perm_next.clone()]);
        }
    }
    let mut commits = vec![main, quot, pre, perm];
    if pts[3].is_empty() {
        pts.pop();
        vals.pop();
        commits.pop();
    }
    verify_pcs(cs, &mut ch, &shape.fri, &commits, &pts, &vals, &fri)?;

    // 3. constraints at zeta
    let mut gamma = lb.clone();
    for _ in 1..shape.lookup_width {
        gamma = ctx.mul(&gamma, &lb)?;
    }
    let n_bus = shape.inst.iter().flat_map(|s| s.bus.iter()).max().map_or(0, |m| m + 1);
    let mut prefix = Vec::with_capacity(n_bus);
    let mut acc = la.clone();
    for _ in 0..n_bus {
        acc = ctx.add(&acc, &gamma)?.reduce(cs)?;
        prefix.push(acc.clone());
    }
    for (i, s) in shape.inst.iter().enumerate() {
        let v = &iv[i];
        let [first, last, trans, inv_van] = selectors(&mut ctx, &zeta, s.log_n)?;
        let periodic = periodic_at(&mut ctx, &s.periodic, &zeta, s.log_n)?;
        let rec = |ctx: &mut CircuitCtx, flat: &[E4]| flat.chunks(4).map(|c| recompose(ctx, c)).collect::<R<Vec<_>>>();
        let pt = Point {
            main_local: v.main_local.clone(),
            main_next: if s.main_next { v.main_next.clone() } else { vec![e4_const([0; 4]); s.width] },
            pre_local: v.pre_local.clone(),
            pre_next: if s.pre_next { v.pre_next.clone() } else { vec![e4_const([0; 4]); s.pre_width] },
            perm_local: rec(&mut ctx, &v.perm_local)?,
            perm_next: rec(&mut ctx, &v.perm_next)?,
            challenges: s.bus.iter().flat_map(|&b| [prefix[b].clone(), lb.clone()]).collect(),
            perm_values: v.terminal.iter().cloned().collect(),
            periodic,
            is_first_row: first,
            is_last_row: last,
            is_transition: trans,
        };
        let folded = Eval::new(&mut ctx, &pt).fold(&s.base, &s.ext, &alpha)?;
        let lhs = ctx.mul(&folded, &inv_van)?;
        // quotient = sum_k zp_k chunk_k, zp_k = prod_{j != k} Z_j(zeta) / Z_j(first_k)
        let mut vz = Vec::with_capacity(s.n_chunks);
        for j in 0..s.n_chunks {
            let mut x = ctx.scale(&zeta, s.chunk_shift_inv[j])?;
            for _ in 0..s.log_n {
                x = ctx.mul(&x, &x)?;
            }
            let one = ctx.base(1);
            vz.push(ctx.sub(&x, &one)?);
        }
        let mut quotient = ctx.base(0);
        for k in 0..s.n_chunks {
            let mut zp = ctx.base(1);
            for j in 0..s.n_chunks {
                if j != k {
                    let t = ctx.scale(&vz[j], s.chunk_cross[k][j])?;
                    zp = ctx.mul(&zp, &t)?;
                }
            }
            let c = recompose(&mut ctx, &v.chunks[k])?;
            let t = ctx.mul(&zp, &c)?;
            quotient = ctx.add(&quotient, &t)?;
        }
        lhs.sub(&quotient).assert_zero(cs)?;
    }

    // 4. terminals sum to zero
    let mut sum = e4_const([0; 4]);
    for v in &iv {
        if let Some(t) = &v.terminal {
            sum = sum.add(t);
        }
    }
    sum.assert_zero(cs)?;
    let _ = M31::constant(0, 0);
    let _ = BigUint::from(0u32);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn verifies_the_five_lane_plonky3_proof_in_r1cs() {
        let (st, traces) = ss_rap_p3::state::tests_case(600, 8);
        let p = Params { log_rows: 8, log_blowup: 1, queries: 20, budget: 3 };
        let proof = record::prove_one(&st, &traces, &p);
        let (ok, ops) = record::verify_one(&st, &proof, &p);
        assert!(ok);
        let shape = batch_shape(&st, &p, &proof.degree_bits, &ops);
        let w = batch_witness(&shape, &proof, &ops);
        let run = |shape: &BatchShape, w: &BatchWitness| {
            let cs = ConstraintSystem::<Fr>::new_ref();
            verify_batch_var(&cs, shape, Some(w)).unwrap();
            (cs.is_satisfied().unwrap(), cs.num_constraints())
        };
        let (ok, n) = run(&shape, &w);
        assert!(ok, "honest proof");
        eprintln!("Plonky3 batch verifier, 600 transfers, 5 lanes x 2^8 rows, blowup 2 x 20 queries: {n} constraints");
        // another statement (a different transfer amount in lane 0): the periodic columns change
        let mut st2 = st.clone();
        st2.lanes[0][3].amount += 1;
        let shape2 = batch_shape(&st2, &p, &proof.degree_bits, &ops);
        assert!(!run(&shape2, &w).0, "proof of another statement");
        // a forged opened value
        let mut bw = w.clone();
        bw.inst[0].main_local[7][0] = (bw.inst[0].main_local[7][0] + 1) % 2013265921;
        assert!(!run(&shape, &bw).0, "forged opening");
        // a forged terminal
        let mut bw = w.clone();
        bw.inst[2].terminal.as_mut().unwrap()[1] ^= 1;
        assert!(!run(&shape, &bw).0, "forged terminal");
    }
}
