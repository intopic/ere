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
//! circuit. The statement enters as a witness (`PublicIo`): the periodic columns of the public
//! AIRs, evaluated at zeta from witness values, and the statement digest, which Plonky3 observes
//! as the lane-0 public values right after the main commitment (so every challenge depends on
//! the statement).

use super::challenger_var::ChallengerVar;
use super::fp31::{E4, M31};
use super::par::{he4, hm31, slot_e4, Io, Par, HE4, HM31};
use super::p3air_eval::{pow_u32, recompose, selectors, Ctx, Eval, Point, EF, F, R};
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
    /// Lazy: the product of two reduced values (about 66 bits) stays unreduced, so a sum of
    /// products (the AIRs' integer convolutions) pays one reduction instead of one per product.
    fn mul(&mut self, a: &E4, b: &E4) -> R<E4> {
        let p = self.tame(a, 100)?.mul(&self.tame(b, 100)?);
        if bits(&p) > 80 {
            p.reduce(&self.cs)
        } else {
            Ok(p)
        }
    }
    /// a * c, as -(a * (m - c)) when m - c is the smaller one (Poseidon2's diagonal holds
    /// constants like 2^-27 = -15), so the bound grows by the smaller constant.
    fn scale(&mut self, a: &E4, c: u32) -> R<E4> {
        let a = self.tame(a, 150)?;
        let m = a.c[0].m();
        if c > m / 2 {
            let t = E4 { c: std::array::from_fn(|k| a.c[k].mul_const(m - c)) };
            return Ok(e4_const([0; 4]).sub(&t));
        }
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
    fn mul_lazy(&mut self, a: &E4, b: &E4) -> R<E4> {
        let (mut a, mut b) = (a.clone(), b.clone());
        while bits(&a) + bits(&b) + 6 > 150 {
            if bits(&a) >= bits(&b) {
                a = a.reduce(&self.cs)?;
            } else {
                b = b.reduce(&self.cs)?;
            }
        }
        Ok(a.mul(&b))
    }
    fn prep(&mut self, a: &E4) -> R<E4> {
        self.tame(a, 40)
    }
    fn dot(&mut self, a: &[E4], b: &[E4]) -> R<E4> {
        let mut acc: Option<E4> = None;
        for (x, y) in a.iter().zip(b) {
            let p = self.tame(x, 190)?.mul(&self.tame(y, 40)?);
            acc = Some(match acc {
                None => p,
                Some(s) if bits(&s) > 225 => s.reduce(&self.cs)?.add(&p),
                Some(s) => s.add(&p),
            });
        }
        match acc {
            None => Ok(e4_const([0; 4])),
            Some(s) => s.reduce(&self.cs),
        }
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
    /// the lane of a public AIR (whose periodic columns come from the statement)
    pub public_lane: Option<usize>,
    /// the blob AIR (whose public values are the blob claim)
    pub blob: bool,
    /// the address table (whose periodic columns come from the statement's addresses)
    pub addr_table: bool,
    pub bus: Vec<usize>,
}

pub struct BatchShape {
    pub inst: Vec<InstShape>,
    /// instances with public values (observed after the main commitment), with their count
    pub public_values: Vec<(usize, usize)>,
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
    let (cfg, _) = record::config(p.log_blowup, p.queries, p.query_pow);
    let pcs = cfg.pcs();
    let slots = 1usize << (degree_bits[degree_bits.len() - 1] - ss_rap_p3::blob_eval::LOG_ROWS);
    let airs = all_airs::<F>(st, p.log_rows, slots);
    assert_eq!(airs.len(), degree_bits.len(), "a proof of another shape");
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
        let layout = AirLayout { preprocessed_width: pre_width, main_width: air.width(), num_public_values: air.num_public_values(), num_periodic_columns: air.num_periodic_columns(), ..Default::default() };
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
            public_lane: if let ss_rap_p3::state::LaneAirs::Public(a) = air { Some(a.lane as usize) } else { None },
            blob: matches!(air, ss_rap_p3::state::LaneAirs::Blob(_)),
            addr_table: matches!(air, ss_rap_p3::state::LaneAirs::Addr(_)),
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
    // between the main and preprocessed commitments: the public values, instance by instance
    let second_digest = first_digest + 1 + ops[first_digest + 1..].iter().position(|o| matches!(o, Op::ObserveDigest(_))).unwrap();
    let public_values: Vec<(usize, usize)> = airs.iter().enumerate().filter(|(_, a)| a.num_public_values() > 0).map(|(i, a)| (i, a.num_public_values())).collect();
    assert_eq!(observes(&ops[first_digest + 1..second_digest]).len(), public_values.iter().map(|x| x.1).sum::<usize>(), "public values are observed as plain scalars");
    let sample_pos: Vec<usize> = ops.iter().enumerate().filter(|(_, o)| matches!(o, Op::Sample(_))).map(|(k, _)| k).collect();
    let after_zeta = sample_pos[15] + 1; // la, lb, alpha, zeta
    let pcs_alpha = sample_pos[16];
    let n_claims: usize = batches.iter().flatten().map(|m| m.width * m.num_points).sum();
    let obs = observes(&ops[after_zeta..pcs_alpha]);
    let pcs_seed = obs[..obs.len() - 4 * n_claims].to_vec();
    let after_alpha = pcs_alpha + 4;
    let fri_digest = after_alpha + ops[after_alpha..].iter().position(|o| matches!(o, Op::ObserveDigest(_))).unwrap();
    let fri_seed = observes(&ops[after_alpha..fri_digest]);
    let fri = FriShape { batches, log_blowup: p.log_blowup, queries: p.queries, pcs_seed, fri_seed, query_pow: p.query_pow };
    BatchShape { inst, public_values, lookup_width, seed, pre_commit, pre_instances, fri }
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
    // the query indices are the last `queries` bit samples (a grinding check samples before them)
    let bit_samples: Vec<usize> = ops.iter().filter_map(|o| if let Op::SampleBits(_, v) = o { Some(*v) } else { None }).collect();
    let indices = bit_samples[bit_samples.len() - shape.fri.queries..].to_vec();
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
/// The statement side of the verifier: the public values of each instance listed in
/// `BatchShape::public_values` (canonical BabyBear values, in order) and the periodic columns of
/// every instance (empty for instances without them), as circuit values.
pub struct PublicIo {
    pub public_values: Vec<Vec<FpVar<Fr>>>,
    pub periodic: Vec<Vec<Vec<M31>>>,
}

impl PublicIo {
    /// The statement and the blob claim as circuit constants (natively).
    pub fn constant(shape: &BatchShape, st: &StateStatement, blobs: &ss_rap_p3::blob_eval::BlobClaim) -> Self {
        let limbs = ss_rap_p3::state::digest_limbs(st);
        let blob_pv: Vec<u32> = blobs.public_values::<F>().iter().map(|v| v.as_canonical_u32()).collect();
        Self {
            public_values: shape.public_values.iter().map(|&(i, _)| if shape.inst[i].blob { &blob_pv } else { &limbs }.iter().map(|&v| FpVar::Constant(Fr::from(v as u64))).collect()).collect(),
            periodic: shape.inst.iter().map(|s| s.periodic.iter().map(|c| c.iter().map(|&v| M31::constant(v, 0)).collect()).collect()).collect(),
        }
    }
}

fn is_const_zero(m: &M31) -> bool {
    use ark_ff::Zero;
    matches!(&m.v, FpVar::Constant(c) if c.is_zero())
}

/// 1 / (w - g^i) for the subgroup of size 2^log_p and (w^p - 1) / p, w = zeta^(2^(log_n - log_p)).
fn periodic_weights(ctx: &mut CircuitCtx, zeta: &E4, log_n: usize, log_p: usize) -> R<(Vec<E4>, E4)> {
    let p = 1usize << log_p;
    let g = TWO_ADIC_GENERATORS[log_p];
    let mut w = zeta.clone();
    for _ in log_p..log_n {
        w = ctx.mul(&w, &w)?;
    }
    let mut wp = w.clone();
    for _ in 0..log_p {
        wp = ctx.mul(&wp, &wp)?;
    }
    let one = ctx.base(1);
    let num = ctx.sub(&wp, &one)?;
    let factor = ctx.scale(&num, pow_u32(p as u32, (super::challenger_var::P - 2) as u64))?.reduce(&ctx.cs)?;
    let mut invs = Vec::with_capacity(p);
    let mut gi = 1u32;
    for _ in 0..p {
        let c = ctx.base(gi);
        let d = ctx.sub(&w, &c)?;
        invs.push(ctx.inv(&d)?);
        gi = ((gi as u64 * g as u64) % super::challenger_var::P) as u32;
    }
    Ok((invs, factor))
}

/// `periodic_weights` natively (canonical values).
fn periodic_weights_native(zeta: [u32; 4], log_n: usize, log_p: usize) -> (Vec<[u32; 4]>, [u32; 4]) {
    let z = EF::from_basis_coefficients_slice(&zeta.map(F::from_u32)).unwrap();
    let mut w = z;
    for _ in log_p..log_n {
        w = w * w;
    }
    let p = 1usize << log_p;
    let wp = w.exp_power_of_2(log_p);
    let factor = (wp - EF::ONE) * F::from_u32(p as u32).inverse();
    let g = F::from_u32(TWO_ADIC_GENERATORS[log_p]);
    let mut gi = F::ONE;
    let mut invs = Vec::with_capacity(p);
    for _ in 0..p {
        invs.push(ef_u32((w - EF::from(gi)).inverse()));
        gi *= g;
    }
    (invs, ef_u32(factor))
}

/// Periodic columns at zeta from the weights: (w^p - 1)/p * sum_i v_i g^i / (w - g^i).
fn periodic_sums(ctx: &mut CircuitCtx, cols: &[Vec<M31>], invs: &[E4], factor: &E4) -> R<Vec<E4>> {
    let mut out = Vec::with_capacity(cols.len());
    for col in cols {
        assert_eq!(col.len(), invs.len());
        let g = TWO_ADIC_GENERATORS[col.len().trailing_zeros() as usize];
        let mut acc = e4_const([0; 4]);
        let mut gi = 1u32;
        for (v, inv) in col.iter().zip(invs) {
            if !is_const_zero(v) {
                acc = acc.add(&inv.mul_base(&v.mul_const(gi)));
            }
            gi = ((gi as u64 * g as u64) % super::challenger_var::P) as u32;
        }
        out.push(ctx.mul(&acc, factor)?);
    }
    Ok(out)
}

/// An instance's opened values as handles.
struct InstH {
    main_local: Vec<HE4>,
    main_next: Vec<HE4>,
    pre_local: Vec<HE4>,
    pre_next: Vec<HE4>,
    perm_local: Vec<HE4>,
    perm_next: Vec<HE4>,
    chunks: Vec<Vec<HE4>>,
    terminal: Option<HE4>,
}

impl InstH {
    fn import(&self, io: &mut Io) -> R<InstVars> {
        let e = |io: &mut Io, v: &[HE4]| v.iter().map(|x| io.import_e4(x)).collect::<R<Vec<_>>>();
        Ok(InstVars {
            main_local: e(io, &self.main_local)?,
            main_next: e(io, &self.main_next)?,
            pre_local: e(io, &self.pre_local)?,
            pre_next: e(io, &self.pre_next)?,
            perm_local: e(io, &self.perm_local)?,
            perm_next: e(io, &self.perm_next)?,
            chunks: self.chunks.iter().map(|c| e(io, c)).collect::<R<_>>()?,
            terminal: self.terminal.as_ref().map(|t| io.import_e4(t)).transpose()?,
        })
    }
}

/// sum_k alpha^k C_k(zeta) / Z_H(zeta) equals the quotient recomposed from its chunks.
#[allow(clippy::too_many_arguments)]
fn check_instance(ctx: &mut CircuitCtx, s: &InstShape, v: &InstVars, zeta: &E4, alpha: &E4, lb: &E4, prefix: &[E4], periodic: Vec<E4>, public: Vec<E4>) -> R<()> {
    let [first, last, trans, inv_van] = selectors(ctx, zeta, s.log_n)?;
    let rec = |ctx: &mut CircuitCtx, flat: &[E4]| flat.chunks(4).map(|c| recompose(ctx, c)).collect::<R<Vec<_>>>();
    let pt = Point {
        main_local: v.main_local.clone(),
        main_next: if s.main_next { v.main_next.clone() } else { vec![e4_const([0; 4]); s.width] },
        pre_local: v.pre_local.clone(),
        pre_next: if s.pre_next { v.pre_next.clone() } else { vec![e4_const([0; 4]); s.pre_width] },
        perm_local: rec(ctx, &v.perm_local)?,
        perm_next: rec(ctx, &v.perm_next)?,
        challenges: prefix.iter().flat_map(|p| [p.clone(), lb.clone()]).collect(),
        perm_values: v.terminal.iter().cloned().collect(),
        periodic,
        public,
        is_first_row: first,
        is_last_row: last,
        is_transition: trans,
    };
    let folded = Eval::new(ctx, &pt).fold(&s.base, &s.ext, alpha)?;
    let lhs = ctx.mul(&folded, &inv_van)?;
    // quotient = sum_k zp_k chunk_k, zp_k = prod_{j != k} Z_j(zeta) / Z_j(first_k)
    let mut vz = Vec::with_capacity(s.n_chunks);
    for j in 0..s.n_chunks {
        let mut x = ctx.scale(zeta, s.chunk_shift_inv[j])?;
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
        let c = recompose(ctx, &v.chunks[k])?;
        let t = ctx.mul(&zp, &c)?;
        quotient = ctx.add(&quotient, &t)?;
    }
    lhs.sub(&quotient).assert_zero(&ctx.cs)
}

/// The commitments of the proof as circuit values: main, permutation, quotient, then the FRI
/// commit-phase commitments (what `v_umt_root` binds).
pub struct ProofCommits(pub Vec<FpVar<Fr>>);

pub fn verify_batch_var<'s, 'e: 's>(cs: &ConstraintSystemRef<Fr>, shape: &'e BatchShape, w: Option<&'e BatchWitness>, io: &PublicIo, par: &Par<'s, 'e>) -> R<ProofCommits> {
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

    let mut t0 = std::time::Instant::now();
    let mut stage = |name: &str, n0: &mut usize| {
        if std::env::var("P3_STAGES").is_ok() {
            eprintln!("  {name:28} {:>10} constraints {:>7.2} s", cs.num_constraints() - *n0, t0.elapsed().as_secs_f64());
        }
        *n0 = cs.num_constraints();
        t0 = std::time::Instant::now();
    };
    let mut n0 = 0usize;
    stage("witness allocation", &mut n0);
    // 1. transcript
    let mut ch = ChallengerVar::new(cs.clone());
    for &v in &shape.seed {
        ch.observe(&FpVar::Constant(Fr::from(v as u64)))?;
    }
    ch.observe_digest(&main)?;
    assert_eq!(io.public_values.len(), shape.public_values.len());
    for (vals, &(_, n)) in io.public_values.iter().zip(&shape.public_values) {
        assert_eq!(vals.len(), n);
        for v in vals {
            ch.observe(v)?;
        }
    }
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

    stage("transcript (before PCS)", &mut n0);
    // 2. opening argument
    let mut ctx = CircuitCtx { cs: cs.clone() };
    // g zeta per trace height (one variable per height, so the opening argument can share
    // 1 / (g zeta - x) between instances of the same height)
    let mut by_height = std::collections::BTreeMap::<usize, E4>::new();
    for s in &shape.inst {
        if !by_height.contains_key(&s.log_n) {
            let x = ctx.scale(&zeta, TWO_ADIC_GENERATORS[s.log_n])?.reduce(cs)?;
            by_height.insert(s.log_n, x);
        }
    }
    let nexts: Vec<E4> = shape.inst.iter().map(|s| by_height[&s.log_n].clone()).collect();
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
    let bound_commits = ProofCommits([vec![main.clone(), perm.clone(), quot.clone()], fri.commit_phase_commits.clone()].concat());
    let mut commits = vec![main, quot, pre, perm];
    if pts[3].is_empty() {
        pts.pop();
        vals.pop();
        commits.pop();
    }
    verify_pcs(cs, &mut ch, &shape.fri, &commits, &pts, &vals, &fri, w.map(|w| &w.fri), par)?;
    stage("opening argument (PCS/FRI)", &mut n0);

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
    // barycentric weights per (trace height, period): a child computes them, the parent holds
    // them in slots (values computed natively) so every instance child can import them
    let zeta_val = zeta.value();
    let mut weights: Vec<((usize, usize), Vec<HE4>, HE4)> = Vec::new();
    for (i, s) in shape.inst.iter().enumerate() {
        if io.periodic[i].is_empty() {
            continue;
        }
        assert_eq!(io.periodic[i].len(), s.periodic.len());
        assert!(io.periodic[i].iter().zip(&s.periodic).all(|(a, b)| a.len() == b.len()), "periodic columns of another shape");
        let log_p = io.periodic[i][0].len().trailing_zeros() as usize;
        let key = (s.log_n, log_p);
        if weights.iter().any(|w| w.0 == key) {
            continue;
        }
        let native = zeta_val.map(|z| periodic_weights_native(z, s.log_n, log_p));
        let p31 = BigUint::from(super::challenger_var::P);
        let invs: Vec<E4> = (0..1usize << log_p).map(|k| slot_e4(cs, native.as_ref().map(|n| n.0[k]), p31.clone())).collect::<R<_>>()?;
        let factor = slot_e4(cs, native.as_ref().map(|n| n.1), BigUint::from(1u64 << 31))?;
        let (invs_h, factor_h): (Vec<HE4>, HE4) = (invs.iter().map(|x| he4(cs, x)).collect::<R<_>>()?, he4(cs, &factor)?);
        let zeta_h = he4(cs, &zeta)?;
        let (ih, fh) = (invs_h.clone(), factor_h.clone());
        par.spawn(move |io: &mut Io| {
            let z = io.import_e4(&zeta_h)?;
            let mut ctx = CircuitCtx { cs: io.cs.clone() };
            let (invs, factor) = periodic_weights(&mut ctx, &z, key.0, key.1)?;
            for (x, t) in invs.iter().zip(&ih) {
                io.export_e4(x, t)?;
            }
            io.export_e4(&factor, &fh)
        })?;
        weights.push((key, invs_h, factor_h));
    }
    // one child per instance: selectors, periodic columns, AIR + LogUp constraints, quotient
    let zeta_h = he4(cs, &zeta)?;
    let alpha_h = he4(cs, &alpha)?;
    let lb_h = he4(cs, &lb)?;
    let prefix_h: Vec<HE4> = prefix.iter().map(|x| he4(cs, x)).collect::<R<_>>()?;
    for (i, s) in shape.inst.iter().enumerate() {
        let v = &iv[i];
        let hv = |xs: &[E4]| xs.iter().map(|x| he4(cs, x)).collect::<R<Vec<_>>>();
        let vh = InstH {
            main_local: hv(&v.main_local)?,
            main_next: hv(&v.main_next)?,
            pre_local: hv(&v.pre_local)?,
            pre_next: hv(&v.pre_next)?,
            perm_local: hv(&v.perm_local)?,
            perm_next: hv(&v.perm_next)?,
            chunks: v.chunks.iter().map(|c| hv(c)).collect::<R<_>>()?,
            terminal: v.terminal.as_ref().map(|t| he4(cs, t)).transpose()?,
        };
        let cols: Vec<Vec<HM31>> = io.periodic[i].iter().map(|c| c.iter().map(|m| hm31(cs, m)).collect::<R<_>>()).collect::<R<_>>()?;
        // public values (canonical BabyBear, below 2^31) as base-field values of the instance
        let public_h: Vec<HM31> = match shape.public_values.iter().position(|&(j, _)| j == i) {
            None => vec![],
            Some(k) => io.public_values[k].iter().map(|v| hm31(cs, &M31 { v: v.clone(), bound: BigUint::from(1u64 << 31), ch: 0 })).collect::<R<_>>()?,
        };
        let wts = if cols.is_empty() { None } else { weights.iter().find(|w| w.0 == (s.log_n, cols[0].len().trailing_zeros() as usize)).map(|w| (w.1.clone(), w.2.clone())) };
        let (zeta_h, alpha_h, lb_h) = (zeta_h.clone(), alpha_h.clone(), lb_h.clone());
        let prefix_i: Vec<HE4> = s.bus.iter().map(|&b| prefix_h[b].clone()).collect();
        par.spawn(move |io: &mut Io| {
            let zeta = io.import_e4(&zeta_h)?;
            let alpha = io.import_e4(&alpha_h)?;
            let lb = io.import_e4(&lb_h)?;
            let prefix: Vec<E4> = prefix_i.iter().map(|x| io.import_e4(x)).collect::<R<_>>()?;
            let v = vh.import(io)?;
            let cols: Vec<Vec<M31>> = cols.iter().map(|c| c.iter().map(|m| io.import_m31(m)).collect::<R<_>>()).collect::<R<_>>()?;
            let zero = M31::constant(0, 0);
            let public: Vec<E4> = public_h.iter().map(|m| Ok(E4 { c: [io.import_m31(m)?, zero.clone(), zero.clone(), zero.clone()] })).collect::<R<_>>()?;
            let mut ctx = CircuitCtx { cs: io.cs.clone() };
            let periodic = match &wts {
                None => vec![],
                Some((ih, fh)) => {
                    let invs: Vec<E4> = ih.iter().map(|x| io.import_e4(x)).collect::<R<_>>()?;
                    let factor = io.import_e4(fh)?;
                    periodic_sums(&mut ctx, &cols, &invs, &factor)?
                }
            };
            check_instance(&mut ctx, s, &v, &zeta, &alpha, &lb, &prefix, periodic, public)
        })?;
    }

    stage("constraints at zeta", &mut n0);
    // 4. terminals sum to zero
    let mut sum = e4_const([0; 4]);
    for v in &iv {
        if let Some(t) = &v.terminal {
            sum = sum.add(t);
        }
    }
    sum.assert_zero(cs)?;
    let _ = BigUint::from(0u32);
    Ok(bound_commits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn verifies_the_five_lane_plonky3_proof_in_r1cs() {
        let _heavy = crate::heavy_test_lock();
        let (st, traces) = ss_rap_p3::state::tests_case(600, 8);
        let p = Params { log_rows: 8, log_blowup: 1, queries: 6, budget: 3, query_pow: 0 };
        let blobs = ss_rap_p3::state::tests_blobs(&st);
        let claim = blobs.claim();
        let proof = record::prove_one(&st, &traces, &blobs, &p);
        let (ok, ops) = record::verify_one(&st, &proof, &claim, &p);
        assert!(ok);
        let shape = batch_shape(&st, &p, &proof.degree_bits, &ops);
        let w = batch_witness(&shape, &proof, &ops);
        let run_with = |io_st: &StateStatement, claim: &ss_rap_p3::blob_eval::BlobClaim, w: &BatchWitness| {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let io = PublicIo::constant(&batch_shape(io_st, &p, &proof.degree_bits, &ops), io_st, claim);
            verify_batch_var(&cs, &shape, Some(w), &io, &super::super::par::Par::Inline(cs.clone())).unwrap();
            (cs.is_satisfied().unwrap(), cs.num_constraints())
        };
        let run = |io_st: &StateStatement, w: &BatchWitness| run_with(io_st, &claim, w);
        let (ok, n) = run(&st, &w);
        assert!(ok, "honest proof");
        eprintln!("Plonky3 batch verifier, 600 transfers, 5 lanes x 2^8 rows, blowup 2 x 6 queries: {n} constraints");
        // another statement (a different balance in the table after lane 0): periodic columns and digest change
        let mut st2 = st.clone();
        st2.states[1][3].balance += 1;
        assert!(!run(&st2, &w).0, "proof of another statement");
        // the transfers are private: another transfer list is the same statement
        let mut st3 = st.clone();
        st3.lanes[0][3].amount += 1;
        assert!(run(&st3, &w).0, "transfers are not part of the statement");
        // a forged opened value
        let mut bw = w.clone();
        bw.inst[0].main_local[7][0] = (bw.inst[0].main_local[7][0] + 1) % 2013265921;
        assert!(!run(&st, &bw).0, "forged opening");
        // a forged terminal
        let mut bw = w.clone();
        bw.inst[2].terminal.as_mut().unwrap()[1] ^= 1;
        assert!(!run(&st, &bw).0, "forged terminal");
        // another blob claim (sum, digest, point)
        let mut c2 = claim.clone();
        c2.s[0] += 1u32;
        assert!(!run_with(&st, &c2, &w).0, "blob sum");
        let mut c2 = claim.clone();
        c2.d[0][5] ^= 1;
        assert!(!run_with(&st, &c2, &w).0, "blob digest");
        let mut c2 = claim.clone();
        c2.z += 1u32;
        assert!(!run_with(&st, &c2, &w).0, "blob point");
    }
}
