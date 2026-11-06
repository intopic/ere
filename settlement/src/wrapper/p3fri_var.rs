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
use super::par::{h, hbool, he4, Io, Par, H, HE4};
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

pub fn e4_const(x: [u32; 4]) -> E4 {
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

pub fn observe_e4(ch: &mut ChallengerVar, x: &E4) -> Result<(), SynthesisError> {
    for c in &x.c {
        ch.observe(&c.v)?;
    }
    Ok(())
}

pub fn sample_e4(ch: &mut ChallengerVar) -> Result<E4, SynthesisError> {
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
    /// grinding bits before the query indices (0: none)
    pub query_pow: usize,
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
    pub query_pow_witness: u32,
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
    pub query_pow_witness: M31,
}

impl FriProofVar {
    /// The proof's non-query part (the query openings are allocated by `query_witness`, in
    /// whichever constraint system checks that query).
    pub fn witness(cs: &ConstraintSystemRef<Fr>, shape: &FriShape, w: Option<&FriWitness>) -> Result<Self, SynthesisError> {
        let fr = |x: Option<Fr>| FpVar::new_witness(cs.clone(), || x.ok_or(SynthesisError::AssignmentMissing));
        let rounds = shape.rounds();
        let commit_phase_commits = (0..rounds).map(|r| fr(w.map(|w| w.commit_phase_commits[r]))).collect::<Result<_, _>>()?;
        let final_poly = e4_witness(cs, w.map(|w| w.final_poly))?;
        let query_pow_witness = bb_witness(cs, w.map(|w| w.query_pow_witness))?;
        Ok(Self { commit_phase_commits, final_poly, query_pow_witness })
    }
}

/// The openings of query `q`.
pub fn query_witness(cs: &ConstraintSystemRef<Fr>, shape: &FriShape, w: Option<&FriWitness>, q: usize) -> Result<QueryVar, SynthesisError> {
    let fr = |x: Option<Fr>| FpVar::new_witness(cs.clone(), || x.ok_or(SynthesisError::AssignmentMissing));
    let log_max = shape.log_max();
    let rounds = shape.rounds();
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
    Ok(QueryVar { input_rows, input_paths, siblings, round_paths })
}

/// Identity of a point: the variables (or constants) of its coordinates.
type PointKey = Vec<(Option<ark_relations::r1cs::Variable>, Option<Fr>)>;

fn point_key(z: &E4) -> PointKey {
    z.c.iter()
        .map(|m| match &m.v {
            FpVar::Var(a) => (Some(a.variable), None),
            FpVar::Constant(c) => (None, Some(*c)),
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------
// the verifier
// ---------------------------------------------------------------------------------------------

/// Verifies the claims `(commits[b], points[b][m][i], values[b][m][i][k])` (every value and point
/// canonical) with the FRI proof, continuing the transcript in `ch`.
pub fn verify_pcs<'s, 'e: 's>(
    cs: &ConstraintSystemRef<Fr>,
    ch: &mut ChallengerVar,
    shape: &'e FriShape,
    commits: &[FpVar<Fr>],
    points: &[Vec<Vec<E4>>],
    values: &[Vec<Vec<Vec<E4>>>],
    proof: &FriProofVar,
    fw: Option<&'e FriWitness>,
    par: &Par<'s, 'e>,
) -> Result<(), SynthesisError> {
    let log_max = shape.log_max();
    let rounds = shape.rounds();
    assert!(shape.batches.iter().flatten().all(|m| m.log_size > 0), "a degree-1 matrix needs the zero check");
    let mut tally = [0usize; 5];
    let mut secs = [0f64; 5];
    let mut mark = cs.num_constraints();
    let mut tmark = std::time::Instant::now();
    let mut tick = |k: usize, tally: &mut [usize; 5]| {
        let n = cs.num_constraints();
        tally[k] += n - mark;
        mark = n;
        secs[k] += tmark.elapsed().as_secs_f64();
        tmark = std::time::Instant::now();
    };

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
    if shape.query_pow > 0 {
        // check_witness: observe the witness, the next `query_pow` sampled bits are all zero
        ch.observe(&proof.query_pow_witness.v)?;
        for b in ch.sample_bits(shape.query_pow)? {
            b.enforce_equal(&Boolean::FALSE)?;
        }
    }
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

    tick(0, &mut tally);
    // 3. queries, in groups that run as children (each allocates its own query openings)
    let betas_sq: Vec<E4> = betas.iter().map(|b| b.mul(b).reduce(cs)).collect::<Result<_, _>>()?;
    let mut point_table: Vec<(PointKey, &E4)> = Vec::new();
    let mut point_ids = Vec::new();
    for b in points {
        for m in b {
            for z in m {
                let k = point_key(z);
                let id = match point_table.iter().position(|(pk, _)| *pk == k) {
                    Some(i) => i,
                    None => {
                        point_table.push((k, z));
                        point_table.len() - 1
                    }
                };
                point_ids.push(id);
            }
        }
    }
    let ctx = QueryCtxH {
        commits: commits.iter().map(|c| h(cs, c)).collect::<Result<_, _>>()?,
        cp_commits: proof.commit_phase_commits.iter().map(|c| h(cs, c)).collect::<Result<_, _>>()?,
        final_poly: he4(cs, &proof.final_poly)?,
        alpha_pow: alpha_pow.iter().map(|a| he4(cs, a)).collect::<Result<_, _>>()?,
        reductions: reductions.iter().map(|(lh, st, e)| Ok((*lh, *st, he4(cs, e)?))).collect::<Result<_, SynthesisError>>()?,
        points: point_table.iter().map(|(_, z)| he4(cs, z)).collect::<Result<_, _>>()?,
        point_ids,
        betas: betas.iter().map(|b| he4(cs, b)).collect::<Result<_, _>>()?,
        betas_sq: betas_sq.iter().map(|b| he4(cs, b)).collect::<Result<_, _>>()?,
    };
    let bits_h: Vec<Vec<H>> = indices.iter().map(|bs| bs.iter().map(|b| hbool(cs, b)).collect::<Result<_, _>>()).collect::<Result<_, _>>()?;
    tick(0, &mut tally);
    let groups = if par.is_inline() { 1 } else { query_groups() };
    let per = shape.queries.div_ceil(groups.max(1));
    let ctx = std::sync::Arc::new(ctx);
    for g in 0..shape.queries.div_ceil(per.max(1)) {
        let qs: Vec<usize> = (g * per..((g + 1) * per).min(shape.queries)).collect();
        let ctx = ctx.clone();
        let bits_g: Vec<Vec<H>> = qs.iter().map(|&q| bits_h[q].clone()).collect();
        par.spawn(move |io: &mut Io| {
            let c = ctx.import(io)?;
            for (k, &q) in qs.iter().enumerate() {
                let bits: Vec<Boolean<Fr>> = bits_g[k].iter().map(|b| io.import_bool(b)).collect::<Result<_, _>>()?;
                let qv = query_witness(&io.cs, shape, fw, q)?;
                check_query(&io.cs, shape, &c, &qv, &bits)?;
            }
            Ok(())
        })?;
    }
    tick(1, &mut tally);
    if std::env::var("P3_STAGES").is_ok() {
        for (k, name) in ["pcs transcript + sums at z", "queries (inline or spawned)"].iter().enumerate() {
            eprintln!("    {name:28} {:>10} {:>7.2} s", tally[k], secs[k]);
        }
    }
    Ok(())
}


/// What every query check shares, as handles a child can import.
struct QueryCtxH {
    commits: Vec<H>,
    cp_commits: Vec<H>,
    final_poly: HE4,
    alpha_pow: Vec<HE4>,
    reductions: Vec<(usize, usize, HE4)>,
    points: Vec<HE4>,
    point_ids: Vec<usize>,
    betas: Vec<HE4>,
    betas_sq: Vec<HE4>,
}

struct QueryCtx {
    commits: Vec<FpVar<Fr>>,
    cp_commits: Vec<FpVar<Fr>>,
    final_poly: E4,
    alpha_pow: Vec<E4>,
    reductions: Vec<(usize, usize, E4)>,
    points: Vec<E4>,
    point_ids: Vec<usize>,
    betas: Vec<E4>,
    betas_sq: Vec<E4>,
}

impl QueryCtxH {
    fn import(&self, io: &mut Io) -> Result<QueryCtx, SynthesisError> {
        let e4s = |io: &mut Io, v: &[HE4]| v.iter().map(|x| io.import_e4(x)).collect::<Result<Vec<_>, _>>();
        Ok(QueryCtx {
            commits: self.commits.iter().map(|x| io.import(x)).collect::<Result<_, _>>()?,
            cp_commits: self.cp_commits.iter().map(|x| io.import(x)).collect::<Result<_, _>>()?,
            final_poly: io.import_e4(&self.final_poly)?,
            alpha_pow: e4s(io, &self.alpha_pow)?,
            reductions: self.reductions.iter().map(|(a, b, e)| Ok((*a, *b, io.import_e4(e)?))).collect::<Result<_, SynthesisError>>()?,
            points: e4s(io, &self.points)?,
            point_ids: self.point_ids.clone(),
            betas: e4s(io, &self.betas)?,
            betas_sq: e4s(io, &self.betas_sq)?,
        })
    }
}

/// Number of query groups when synthesising in parallel (P3_QUERY_GROUPS, default 4).
fn query_groups() -> usize {
    std::env::var("P3_QUERY_GROUPS").ok().and_then(|v| v.parse().ok()).unwrap_or(4)
}

/// One FRI query: input Merkle openings, reduced openings, folding to the final polynomial.
fn check_query(cs: &ConstraintSystemRef<Fr>, shape: &FriShape, c: &QueryCtx, qv: &QueryVar, bits: &[Boolean<Fr>]) -> Result<(), SynthesisError> {
    let log_max = shape.log_max();
    let rounds = shape.rounds();
    let half = M31::constant(((P + 1) / 2) as u32, CH);
    // input openings
    for (b, mats) in shape.batches.iter().enumerate() {
        let hb = mats.iter().map(|m| m.log_size).max().unwrap() + shape.log_blowup;
        let heights: Vec<usize> = mats.iter().map(|m| 1 << (m.log_size + shape.log_blowup)).collect();
        let rows: Vec<Vec<FpVar<Fr>>> = qv.input_rows[b].iter().map(|r| r.iter().map(|x| x.v.clone()).collect()).collect();
        verify_batch_var(&c.commits[b], &heights, &bits[log_max - hb..], &rows, &qv.input_paths[b])?;
    }
    // reduced openings per height: sum over (matrix, point) of (sum_z - sum_x) / (z - x).
    // Terms with the same height and the same point variable share 1 / (z - x) and one
    // reduction; x depends on the height only.
    // s_0 = g_{log_max}^rev(index >> 1, log_max - 1) (the first fold's twiddle) and
    // y_max = g_{log_max}^rev(index, log_max) = (-1)^bit0 s_0; for a lower height lh,
    // y_lh = y_max^(2^(log_max - lh)) and x = GENERATOR * y_lh.
    let rev_bits: Vec<Boolean<Fr>> = (0..log_max - 1).map(|i| bits[log_max - 1 - i].clone()).collect();
    let s0 = pow_bits(cs, TWO_ADIC_GENERATORS[log_max], &rev_bits)?;
    let sign = M31 { v: FpVar::from(bits[0].clone()) * Fr::from(P - 2) + Fr::from(1u64), bound: BigUint::from(P), ch: CH };
    let mut ys = std::collections::BTreeMap::<usize, M31>::new();
    let mut y = s0.mul(&sign).reduce(cs)?;
    for lh in (1..=log_max).rev() {
        ys.insert(lh, y.clone());
        if lh > 1 {
            y = y.mul(&y).reduce(cs)?;
        }
    }
    let mut xs = std::collections::BTreeMap::<usize, M31>::new();
    let mut groups: Vec<((usize, usize), &E4, E4)> = Vec::new();
    let mut red = c.reductions.iter();
    let mut pid = c.point_ids.iter();
    for (b, mats) in shape.batches.iter().enumerate() {
        for (m, ms) in mats.iter().enumerate() {
            let lh = ms.log_size + shape.log_blowup;
            if !xs.contains_key(&lh) {
                xs.insert(lh, ys[&lh].mul_const(GENERATOR).reduce(cs)?);
            }
            let row = &qv.input_rows[b][m];
            for _ in 0..ms.num_points {
                let (_, start, sum_z) = red.next().unwrap();
                let mut d = sum_z.clone();
                for k in 0..ms.width {
                    d = d.sub(&c.alpha_pow[start + k].mul_base(&row[k]));
                }
                let key = (lh, *pid.next().unwrap());
                match groups.iter_mut().find(|g| g.0 == key) {
                    Some(g) => g.2 = g.2.add(&d),
                    None => groups.push((key, &c.points[key.1], d)),
                }
            }
        }
    }
    let mut ro = std::collections::BTreeMap::<usize, E4>::new();
    for ((lh, _), z, d) in groups {
        let inv = e4_inverse(cs, &z.sub(&E4::from_base(&xs[&lh])))?;
        let term = d.reduce(cs)?.mul(&inv);
        let e = ro.remove(&lh).map(|a| a.add(&term)).unwrap_or(term);
        ro.insert(lh, e);
    }
    let ro_n = ro.len();
    let mut ro: std::collections::BTreeMap<usize, E4> = ro.into_iter().map(|(k, v)| Ok((k, v.reduce(cs)?))).collect::<Result<_, SynthesisError>>()?;
    assert_eq!(ro.len(), ro_n);
    // folding
    let mut folded = e4_canon(cs, ro.remove(&log_max).as_ref().expect("an opening at the max height"))?;
    // 1 / s_r from 1 / s_0: s_{r+1} = s_r^2 (-1)^bit_{r+1}
    let mut inv_s = bb_inverse(cs, &s0)?;
    for r in 0..rounds {
        let l = log_max - r; // height before this fold
        let bit = &bits[r];
        let sib = &qv.siblings[r];
        let lo = e4_select(bit, sib, &folded)?;
        let hi = e4_select(bit, &folded, sib)?;
        // the pair opens under this round's commitment at index >> (r + 1)
        let leaf: Vec<FpVar<Fr>> = lo.c.iter().chain(hi.c.iter()).map(|x| x.v.clone()).collect();
        verify_batch_var(&c.cp_commits[r], &[1 << (l - 1)], &bits[r + 1..log_max], &[leaf], &qv.round_paths[r])?;
        // (lo + hi) / 2 + (lo - hi) beta / (2 s), s = g_l^rev(index >> (r + 1), l - 1)
        let inv_2s = inv_s.mul(&half);
        let sum = lo.add(&hi).mul_base(&half);
        let diff = lo.sub(&hi).mul(&c.betas[r]).mul_base(&inv_2s);
        let mut next = sum.add(&diff);
        if let Some(o) = ro.remove(&(l - 1)) {
            next = next.add(&c.betas_sq[r].mul(&o));
        }
        folded = e4_canon(cs, &next)?;
        if r + 1 < rounds {
            let f = M31 { v: FpVar::from(bits[r + 1].clone()) * Fr::from(P - 2) + Fr::from(1u64), bound: BigUint::from(P), ch: CH };
            inv_s = inv_s.mul(&inv_s).mul(&f).reduce(cs)?;
        }
    }
    assert!(ro.is_empty());
    for k in 0..4 {
        folded.c[k].v.enforce_equal(&c.final_poly.c[k].v)?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// witness generation from a Plonky3 proof
// ---------------------------------------------------------------------------------------------

use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField, PrimeField32, TwoAdicField};
use p3_matrix::Dimensions;

type EFp = BinomialExtensionField<BabyBear, 4>;
pub type PcsProof = <ss_rap_p3::bn254::Pcs<BabyBear> as p3_commit::Pcs<EFp, ss_rap_p3::record::Recording>>::Proof;

pub fn bn_to_fr(x: p3_bn254::Bn254) -> Fr {
    Fr::from(BigUint::from_bytes_le(&x.as_canonical_biguint().to_bytes_le()))
}

pub fn ef_u32(x: EFp) -> [u32; 4] {
    let c: &[BabyBear] = x.as_basis_coefficients_slice();
    [0, 1, 2, 3].map(|i| c[i].as_canonical_u32())
}

/// Expands Plonky3's pruned Merkle proofs per query and recomputes the verifier's folded values
/// (the commit-phase leaves contain them), with the challenges the transcript gives.
pub fn fri_witness(shape: &FriShape, proof: &PcsProof, indices: &[usize], alpha: EFp, betas: &[EFp], pts: &[Vec<Vec<EFp>>], opened: &[Vec<Vec<Vec<EFp>>>]) -> FriWitness {
    let log_max = shape.log_max();
    let rounds = shape.rounds();
    let queries = shape.queries;
    let mmcs = ss_rap_p3::bn254::config_mmcs::<BabyBear>();
    let mut input_rows: Vec<Vec<Vec<Vec<u32>>>> = vec![vec![]; queries];
    let mut input_paths: Vec<Vec<Vec<Fr>>> = vec![vec![]; queries];
    for (b, bo) in proof.input_openings.iter().enumerate() {
        let mats = &shape.batches[b];
        let hb = mats.iter().map(|m| m.log_size).max().unwrap() + shape.log_blowup;
        let dims: Vec<Dimensions> = mats.iter().map(|m| Dimensions { width: m.width, height: 1 << (m.log_size + shape.log_blowup) }).collect();
        let red: Vec<usize> = indices.iter().map(|i| i >> (log_max - hb)).collect();
        let paths = mmcs.restore_and_recompute_paths(&dims, &red, &bo.opened_values, &bo.opening_proof).unwrap();
        for q in 0..queries {
            input_rows[q].push(bo.opened_values[q].iter().map(|r| r.iter().map(|v| v.as_canonical_u32()).collect()).collect());
            input_paths[q].push(paths[q].siblings.iter().map(|d| bn_to_fr(d[0])).collect());
        }
    }
    let siblings: Vec<Vec<[u32; 4]>> = (0..queries).map(|q| proof.commit_phase_openings.iter().map(|st| ef_u32(st.sibling_values[q][0])).collect()).collect();
    let e = |s: &[u32; 4]| EFp::from_basis_coefficients_slice(&s.map(BabyBear::from_u32)).unwrap();
    let mut folded_rows: Vec<Vec<Vec<Vec<BabyBear>>>> = vec![vec![]; rounds];
    for (q, &index) in indices.iter().enumerate() {
        let mut ro = std::collections::BTreeMap::<usize, EFp>::new();
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
                    let mut acc = EFp::ZERO;
                    let mut ap = alpha.exp_u64(start as u64);
                    for k in 0..ms.width {
                        acc += ap * (opened[b][m][i][k] - EFp::from(BabyBear::from_u32(input_rows[q][b][m][k])));
                        ap *= alpha;
                    }
                    *ro.entry(lh).or_insert(EFp::ZERO) += acc / (pts[b][m][i] - EFp::from(x));
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
        assert_eq!(folded, proof.final_poly[0], "native fold");
    }
    let mut round_paths = vec![vec![]; queries];
    for (r, step) in proof.commit_phase_openings.iter().enumerate() {
        let lf = log_max - r - 1;
        let idx: Vec<usize> = indices.iter().map(|i| i >> (r + 1)).collect();
        let dims = [Dimensions { width: 8, height: 1 << lf }];
        let paths = mmcs.restore_and_recompute_paths(&dims, &idx, &folded_rows[r], &step.opening_proof).unwrap();
        for q in 0..queries {
            round_paths[q].push(paths[q].siblings.iter().map(|d| bn_to_fr(d[0])).collect());
        }
    }
    FriWitness {
        commit_phase_commits: proof.commit_phase_commits.iter().map(|c| bn_to_fr(c[0][0])).collect(),
        final_poly: ef_u32(proof.final_poly[0]),
        input_rows,
        input_paths,
        siblings,
        round_paths,
        query_pow_witness: proof.query_pow_witness.as_canonical_u32(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use p3_baby_bear::BabyBear;
    use p3_commit::Pcs;
    use p3_field::extension::BinomialExtensionField;
    use p3_matrix::dense::RowMajorMatrix;
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
        let (cfg, log) = record::config(log_blowup, queries, 0);
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
        let (pcs_seed, fri_seed) = seeds(&ops, n_claims);
        let shape = FriShape { batches, log_blowup, queries, pcs_seed, fri_seed, query_pow: 0 };

        let indices: Vec<usize> = ops.iter().filter_map(|o| if let Op::SampleBits(_, v) = o { Some(*v) } else { None }).collect();
        let samples: Vec<u32> = ops.iter().filter_map(|o| if let Op::Sample(v) = o { Some(*v) } else { None }).collect();
        let e = |s: &[u32]| EF::from_basis_coefficients_slice(&s.iter().map(|&v| BabyBear::from_u32(v)).collect::<Vec<_>>()).unwrap();
        let alpha = e(&samples[0..4]);
        let betas: Vec<EF> = (0..shape.rounds()).map(|r| e(&samples[4 + 4 * r..8 + 4 * r])).collect();
        let w = fri_witness(&shape, &proof, &indices, alpha, &betas, &pts, &opened);
        let run = |w: &FriWitness, opened: &Vec<Vec<Vec<Vec<EF>>>>| {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let mut ch = ChallengerVar::new(cs.clone());
            let commit_vars: Vec<FpVar<Fr>> = commits.iter().map(|c| FpVar::new_witness(cs.clone(), || Ok(to_fr(c[0][0]))).unwrap()).collect();
            let point_vars: Vec<Vec<Vec<E4>>> = pts.iter().map(|b| b.iter().map(|m| m.iter().map(|z| e4_witness(&cs, Some(ef(*z))).unwrap()).collect()).collect()).collect();
            let value_vars: Vec<Vec<Vec<Vec<E4>>>> = opened.iter().map(|b| b.iter().map(|m| m.iter().map(|vs| vs.iter().map(|v| e4_witness(&cs, Some(ef(*v))).unwrap()).collect()).collect()).collect()).collect();
            let pv = FriProofVar::witness(&cs, &shape, Some(w)).unwrap();
            verify_pcs(&cs, &mut ch, &shape, &commit_vars, &point_vars, &value_vars, &pv, Some(w), &super::super::par::Par::Inline(cs.clone())).unwrap();
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
}
