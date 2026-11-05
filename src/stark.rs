//! STARK engine over the 5 RNS lanes, generic over an AIR (Phase A of docs/PLANI_MVP.md).
//!
//! It connects every piece of the PDF architecture into one non-interactive proof:
//!   an AIR (`Air` trait: MULMOD rows in `uint256.rs`, account transfers in `state.rs`)
//!   + LogUp byte range check as AIR (inverse columns + running sum, `logup.rs` idea)
//!   + LogUp buses (offline memory checking, public inputs) on the same running sum
//!   + Fiat-Shamir (`transcript.rs`)
//!   + coset LDE with the PDF's 2^24 roots (`ntt.rs`)
//!   + V-UMT commitments: one Merkle tree per stage for all 5 lanes
//!   + unified FRI (`fri.rs`) on a random linear combination of all columns and the quotient.
//!
//! Each RNS channel j is a lane: it runs the AIR over its own field F_{m_j} (challenges in
//! F_{m_j}^4) on its own share of the work. Commitments in different fields cannot be tied to
//! the same integers, so every lane must be sound alone: every AIR here keeps its integer
//! identities below m_j / 2. The 5 lanes are proven in parallel and share one FRI.
//!
//! Stages:
//!  1. main trace  (AIR columns + 1 multiplicity column)                   -> root_main -> alpha, beta, rho
//!  2. aux trace   (1/(alpha - byte) per byte column, 1/(alpha - T), 1/bus_k, running sum h) -> root_aux -> gamma
//!  3. quotient    Q = C / (X^N - 1), C = sum_k gamma^k * constraint_k  -> root_q -> delta
//!  4. FRI on      f = Q + sum_k delta^(k+1) * column_k                -> query indices
//!  5. openings of all three trees at x, -x and their next rows, for every FRI query.
//!
//! The lookup table T(x) = 0..255 repeating is a periodic column the verifier evaluates itself.
//! The running sum h steps by (row's LogUp terms) - S/N on every row of the cyclic domain, so the
//! row terms sum to S, the public part of the buses that the verifier computes itself
//! (S = 0 when the AIR has no bus: plain LogUp).
//!
//! Not zero-knowledge (no masking); not needed for settlement proofs of public data.

use crate::fri::{self, FriParams, FriProof, Hash, Layer, Tree};
use crate::logup::batch_inverse_ext4;
use crate::ntt::{intt, ntt, root_of_unity};
use crate::transcript::Transcript;
use crate::uint256::{eval_columns, p_columns, Modulus256, MulModRow, CONSTRAINTS_PER_CHANNEL, NUM_COLUMNS};
use crate::{mod_inv_single, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, EXTENSION_BETA, RNS_MODULI};
use crate::hash::{hash_leaf, HashMode};
use rayon::prelude::*;

/// Runs `f` for the 5 RNS lanes in parallel: the lanes share no data (PDF: carry-free,
/// independent residues), so each can live on its own core or GPU.
pub(crate) fn per_channel<T: Send, F: Fn(usize) -> T + Sync + Send>(f: F) -> [T; DEFAULT_RNS_CHANNELS] {
    let v: Vec<T> = (0..DEFAULT_RNS_CHANNELS).into_par_iter().map(f).collect();
    v.try_into().unwrap_or_else(|_| unreachable!())
}

pub const TABLE: usize = 256;

// ---------------------------------------------------------------------------------------------
// AIR interface
// ---------------------------------------------------------------------------------------------

/// Random challenges of one lane, drawn after the main trace is committed.
#[derive(Clone, Copy, Debug)]
pub struct Challenges {
    /// LogUp byte range check.
    pub alpha: Extension4,
    /// Bus offset and fingerprint base: a tuple (v_0..v_k) is sent as beta - sum rho^i v_i.
    pub beta: Extension4,
    pub rho: Extension4,
}

impl Challenges {
    /// Bus fingerprint denominator beta - sum_i rho^(i+1) v_i (+ a tag so that buses never mix).
    pub fn fingerprint(&self, tag: u32, values: &[u32], ch: usize) -> Extension4 {
        let mut acc = Extension4::ZERO;
        for &v in values.iter().rev() {
            acc = acc.add(&Extension4::from_base(v), ch).mul(&self.rho, ch);
        }
        acc = acc.add(&Extension4::from_base(tag), ch).mul(&self.rho, ch);
        self.beta.sub(&acc, ch)
    }
}

/// Values of public helper polynomials at a point x of the evaluation domain.
#[derive(Clone, Copy, Debug)]
pub struct Point {
    /// (x^N - 1) / (x - 1): non-zero only at the first trace row (where it equals N).
    pub first_row: u32,
    /// x - w^(N-1): zero only at the last trace row (gates transition constraints).
    pub not_last: u32,
}

/// One LogUp bus term of a row: adds weight / den to the running sum.
#[derive(Clone, Copy, Debug)]
pub struct BusTerm {
    pub den: Extension4,
    pub weight: u32,
}

/// An algebraic intermediate representation, evaluated independently in every lane (= channel).
/// The first `byte_cols()` main columns are range-checked to [0, 256) by the engine.
pub trait Air: Sync {
    /// Public statement (absorbed into the transcript before anything else).
    fn statement(&self) -> Vec<u8>;
    fn width(&self) -> usize;
    fn byte_cols(&self) -> usize;
    fn num_constraints(&self) -> usize;
    /// Base-field constraints of the row (degree <= 2 overall, including `Point` factors).
    fn eval(&self, cur: &[u32], next: &[u32], pt: &Point, ch: usize, out: &mut Vec<u32>);
    fn num_bus(&self) -> usize {
        0
    }
    fn bus(&self, _cur: &[u32], _c: &Challenges, _ch: usize, _out: &mut Vec<BusTerm>) {}
    /// sum over all rows of the lane's bus terms, computed from public data.
    fn bus_sum(&self, _c: &Challenges, _ch: usize) -> Extension4 {
        Extension4::ZERO
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StarkParams {
    pub log_rows: u32,
    pub log_blowup: u32,
    pub num_queries: usize,
}

impl StarkParams {
    fn fri(&self) -> FriParams {
        FriParams { log_degree: self.log_rows, log_blowup: self.log_blowup, num_queries: self.num_queries }
    }
    fn check(&self) {
        assert!(self.log_rows >= 8, "need at least 256 rows for the byte table");
        assert!(self.log_blowup >= 2, "constraint degree 2 needs blowup >= 2; use 4");
    }
}

#[derive(Clone, Debug)]
pub struct Opening {
    pub main: [Vec<u32>; DEFAULT_RNS_CHANNELS],
    pub aux: [Vec<Extension4>; DEFAULT_RNS_CHANNELS],
    pub quotient: [Extension4; DEFAULT_RNS_CHANNELS],
    pub main_path: Vec<Hash>,
    pub aux_path: Vec<Hash>,
    pub q_path: Vec<Hash>,
}

#[derive(Clone, Debug)]
pub struct StarkProof {
    pub rows: usize,
    pub main_root: Hash,
    pub aux_root: Hash,
    pub q_root: Hash,
    pub fri: FriProof,
    /// Per FRI query: openings at i, i + n/2, next(i), next(i + n/2).
    pub openings: Vec<[Opening; 4]>,
}

impl StarkProof {
    pub fn size_bytes(&self) -> usize {
        let opens: usize = self
            .openings
            .iter()
            .flatten()
            .map(|o| {
                let vals: usize = (0..DEFAULT_RNS_CHANNELS).map(|ch| o.main[ch].len() * 4 + o.aux[ch].len() * 16 + 16).sum();
                vals + 32 * (o.main_path.len() + o.aux_path.len() + o.q_path.len())
            })
            .sum();
        8 + 3 * 32 + self.fri.size_bytes() + opens
    }
}

struct Layout {
    width: usize,
    bytes: usize,
    bus: usize,
}

impl Layout {
    fn of<A: Air>(air: &A) -> Self {
        assert!(air.byte_cols() <= air.width());
        Self { width: air.width(), bytes: air.byte_cols(), bus: air.num_bus() }
    }
    fn main_cols(&self) -> usize {
        self.width + 1
    }
    fn mult(&self) -> usize {
        self.width
    }
    fn inv_t(&self) -> usize {
        self.bytes
    }
    fn bus0(&self) -> usize {
        self.bytes + 1
    }
    fn sum(&self) -> usize {
        self.bytes + 1 + self.bus
    }
    fn aux_cols(&self) -> usize {
        self.sum() + 1
    }
}

fn shift(ch: usize) -> u32 {
    EXTENSION_BETA[ch] // a quadratic non-residue: the coset never meets the trace domain
}

pub(crate) fn pow(mut b: u32, mut e: u64, ch: usize) -> u32 {
    let mut r = 1u32;
    while e > 0 {
        if e & 1 == 1 {
            r = mul_mod_channel(r, b, ch);
        }
        b = mul_mod_channel(b, b, ch);
        e >>= 1;
    }
    r
}

/// Values on the trace domain (size N) -> evaluations on the coset g * <w_{N*blowup}>.
fn coset_lde(values: &[u32], blowup: usize, ch: usize) -> Vec<u32> {
    let mut c = values.to_vec();
    intt(&mut c, ch);
    let g = shift(ch);
    let mut gk = 1u32;
    for x in c.iter_mut() {
        *x = mul_mod_channel(*x, gk, ch);
        gk = mul_mod_channel(gk, g, ch);
    }
    c.resize(values.len() * blowup, 0);
    ntt(&mut c, ch);
    c
}

fn coset_lde_ext(values: &[Extension4], blowup: usize, ch: usize) -> Vec<Extension4> {
    let coords: Vec<Vec<u32>> = (0..4).map(|k| coset_lde(&values.iter().map(|e| e.c[k]).collect::<Vec<_>>(), blowup, ch)).collect();
    (0..coords[0].len()).map(|i| Extension4::new(coords[0][i], coords[1][i], coords[2][i], coords[3][i])).collect()
}

/// Coefficients of t, the degree < 256 polynomial with t(w_256^i) = i.
fn table_coeffs(ch: usize) -> Vec<u32> {
    let mut coeffs: Vec<u32> = (0..TABLE as u32).collect();
    intt(&mut coeffs, ch);
    coeffs
}

/// The lookup table as a periodic column: T(x) = t(x^(N/256)), t interpolating 0..255.
fn table_value(coeffs: &[u32], x: u32, rows: usize, ch: usize) -> u32 {
    let y = pow(x, (rows / TABLE) as u64, ch);
    let m = RNS_MODULI[ch];
    coeffs.iter().rev().fold(0, |acc, &c| crate::add_mod(mul_mod_channel(acc, y, ch), c, m))
}

fn point(x: u32, n_rows: usize, ch: usize) -> Point {
    let m = RNS_MODULI[ch];
    let xn1 = sub_mod(pow(x, n_rows as u64, ch), 1, m);
    let last = pow(root_of_unity(n_rows, ch), (n_rows - 1) as u64, ch);
    Point { first_row: mul_mod_channel(xn1, mod_inv_single(sub_mod(x, 1, m), m), ch), not_last: sub_mod(x, last, m) }
}

/// Everything a lane needs to evaluate the composition at one point.
struct LaneCtx {
    c: Challenges,
    gamma: Extension4,
    s_over_n: Extension4,
}

/// C(x) = sum_k gamma^k * constraint_k at one point of one lane.
#[allow(clippy::too_many_arguments)]
fn composition<A: Air>(air: &A, l: &Layout, main: &[u32], main_next: &[u32], aux: &[Extension4], h_next: &Extension4, t: u32, pt: &Point, cx: &LaneCtx, ch: usize, base: &mut Vec<u32>, bus: &mut Vec<BusTerm>) -> Extension4 {
    let (alpha, gamma) = (&cx.c.alpha, &cx.gamma);
    let mut acc = Extension4::ZERO;
    let mut push = |v: Extension4| acc = acc.mul(gamma, ch).add(&v, ch);
    base.clear();
    air.eval(&main[..l.width], &main_next[..l.width], pt, ch, base);
    debug_assert_eq!(base.len(), air.num_constraints());
    for &c in base.iter() {
        push(Extension4::from_base(c));
    }
    let mut sum = Extension4::ZERO;
    for c in 0..l.bytes {
        let den = alpha.sub(&Extension4::from_base(main[c]), ch);
        push(aux[c].mul(&den, ch).sub(&Extension4::ONE, ch));
        sum = sum.add(&aux[c], ch);
    }
    let den_t = alpha.sub(&Extension4::from_base(t), ch);
    push(aux[l.inv_t()].mul(&den_t, ch).sub(&Extension4::ONE, ch));
    sum = sum.sub(&aux[l.inv_t()].mul_scalar(main[l.mult()], ch), ch);
    bus.clear();
    air.bus(&main[..l.width], &cx.c, ch, bus);
    debug_assert_eq!(bus.len(), l.bus);
    for (k, b) in bus.iter().enumerate() {
        let inv = &aux[l.bus0() + k];
        push(inv.mul(&b.den, ch).sub(&Extension4::ONE, ch));
        sum = sum.add(&inv.mul_scalar(b.weight, ch), ch);
    }
    // h(wx) - h(x) - (row's LogUp terms) + S/N = 0
    push(h_next.sub(&aux[l.sum()], ch).sub(&sum, ch).add(&cx.s_over_n, ch));
    acc
}

fn fri_combination(main: &[u32], aux: &[Extension4], q: &Extension4, delta: &Extension4, ch: usize) -> Extension4 {
    let mut acc = Extension4::ZERO;
    for v in aux.iter().rev() {
        acc = acc.mul(delta, ch).add(v, ch);
    }
    for &v in main.iter().rev() {
        acc = acc.mul(delta, ch).add(&Extension4::from_base(v), ch);
    }
    q.add(&acc.mul(delta, ch), ch)
}

fn main_values(cols: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS], i: usize) -> Vec<u32> {
    cols.iter().flat_map(|ch_cols| ch_cols.iter().map(move |c| c[i])).collect()
}

fn aux_values(cols: &[Vec<Vec<Extension4>>; DEFAULT_RNS_CHANNELS], i: usize) -> Vec<u32> {
    cols.iter().flat_map(|ch_cols| ch_cols.iter().flat_map(move |c| c[i].c)).collect()
}

pub fn main_leaf_from(mode: HashMode, o: &Opening) -> Hash {
    hash_leaf(mode, b"SS-RAP/v2/main", &o.main.iter().flatten().copied().collect::<Vec<_>>())
}

pub fn aux_leaf_from(mode: HashMode, o: &Opening) -> Hash {
    hash_leaf(mode, b"SS-RAP/v2/aux", &o.aux.iter().flatten().flat_map(|e| e.c).collect::<Vec<_>>())
}

pub fn q_leaf(mode: HashMode, q: &[Extension4; DEFAULT_RNS_CHANNELS]) -> Hash {
    hash_leaf(mode, b"SS-RAP/v2/quotient", &q.iter().flat_map(|e| e.c).collect::<Vec<_>>())
}

fn start_transcript<A: Air>(t: &mut Transcript, air: &A, params: &StarkParams, rows: usize) {
    t.absorb(b"stark/statement", &air.statement());
    t.absorb(b"stark/shape", &[params.log_rows as u8, params.log_blowup as u8, params.num_queries as u8]);
    t.absorb(b"stark/rows", &(rows as u64).to_le_bytes());
}

fn lane_ctx<A: Air>(air: &A, c: Challenges, gamma: Extension4, n_rows: usize, ch: usize) -> LaneCtx {
    let n_inv = mod_inv_single(n_rows as u32 % RNS_MODULI[ch], RNS_MODULI[ch]);
    LaneCtx { c, gamma, s_over_n: air.bus_sum(&c, ch).mul_scalar(n_inv, ch) }
}

fn draw_challenges(t: &mut Transcript) -> [Challenges; DEFAULT_RNS_CHANNELS] {
    let a = t.challenge_ext4_all(b"stark/alpha");
    let b = t.challenge_ext4_all(b"stark/beta");
    let r = t.challenge_ext4_all(b"stark/rho");
    std::array::from_fn(|ch| Challenges { alpha: a[ch], beta: b[ch], rho: r[ch] })
}

/// Proves one trace per lane (RNS channel). Each trace has 2^log_rows rows of `air.width()`
/// values; `rows` is the public count of real work items (absorbed into the transcript).
pub fn prove_air<A: Air>(air: &A, traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS], rows: usize, params: &StarkParams, t: &mut Transcript) -> StarkProof {
    params.check();
    let l = Layout::of(air);
    let n_rows = 1usize << params.log_rows;
    let blowup = 1usize << params.log_blowup;
    let n = n_rows * blowup;
    start_transcript(t, air, params, rows);

    // ---- 1. main trace: AIR columns + byte multiplicities (per lane)
    let main_hs: [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] = per_channel(|ch| {
        let trace = &traces[ch];
        assert_eq!(trace.len(), n_rows);
        let m = RNS_MODULI[ch];
        let mut mult = vec![0u32; n_rows];
        for row in trace {
            assert_eq!(row.len(), l.width);
            for &v in &row[..l.bytes] {
                if (v as usize) < TABLE {
                    mult[v as usize] += 1;
                }
            }
        }
        let mut cols: Vec<Vec<u32>> = (0..l.width).map(|c| trace.iter().map(|r| r[c] % m).collect()).collect();
        cols.push(mult);
        cols
    });
    let main_lde: [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] = per_channel(|ch| main_hs[ch].iter().map(|col| coset_lde(col, blowup, ch)).collect());
    let mode = t.mode();
    let main_tree = Tree::from_leaves(mode, crate::par_map(n, |i| hash_leaf(mode, b"SS-RAP/v2/main", &main_values(&main_lde, i))));
    t.absorb(b"stark/main", &main_tree.root());
    let chals = draw_challenges(t);

    // ---- 2. aux trace on the trace domain, then LDE
    let aux_lde: [Vec<Vec<Extension4>>; DEFAULT_RNS_CHANNELS] = per_channel(|ch| {
        let c = chals[ch];
        let main_h = &main_hs[ch];
        let mut cols: Vec<Vec<Extension4>> = Vec::with_capacity(l.aux_cols());
        for col in main_h.iter().take(l.bytes) {
            let den: Vec<Extension4> = col.iter().map(|&v| c.alpha.sub(&Extension4::from_base(v), ch)).collect();
            cols.push(batch_inverse_ext4(&den, ch).expect("alpha hit a trace value"));
        }
        let den_t: Vec<Extension4> = (0..n_rows).map(|r| c.alpha.sub(&Extension4::from_base((r % TABLE) as u32), ch)).collect();
        cols.push(batch_inverse_ext4(&den_t, ch).unwrap());
        // bus inverses
        let mut terms: Vec<Vec<BusTerm>> = Vec::with_capacity(n_rows);
        let mut row = vec![0u32; l.width];
        let mut buf = Vec::new();
        for r in 0..n_rows {
            for k in 0..l.width {
                row[k] = main_h[k][r];
            }
            buf.clear();
            air.bus(&row, &c, ch, &mut buf);
            terms.push(buf.clone());
        }
        for k in 0..l.bus {
            let den: Vec<Extension4> = terms.iter().map(|ts| ts[k].den).collect();
            cols.push(batch_inverse_ext4(&den, ch).expect("beta hit a fingerprint"));
        }
        let cx = lane_ctx(air, c, Extension4::ZERO, n_rows, ch);
        let mut h = vec![Extension4::ZERO; n_rows];
        for r in 0..n_rows - 1 {
            let mut step = Extension4::ZERO;
            for col in cols.iter().take(l.bytes) {
                step = step.add(&col[r], ch);
            }
            step = step.sub(&cols[l.inv_t()][r].mul_scalar(main_h[l.mult()][r], ch), ch);
            for (k, term) in terms[r].iter().enumerate() {
                step = step.add(&cols[l.bus0() + k][r].mul_scalar(term.weight, ch), ch);
            }
            h[r + 1] = h[r].add(&step, ch).sub(&cx.s_over_n, ch);
        }
        cols.push(h);
        cols.iter().map(|col| coset_lde_ext(col, blowup, ch)).collect()
    });
    let aux_tree = Tree::from_leaves(mode, crate::par_map(n, |i| hash_leaf(mode, b"SS-RAP/v2/aux", &aux_values(&aux_lde, i))));
    t.absorb(b"stark/aux", &aux_tree.root());
    let gammas = t.challenge_ext4_all(b"stark/gamma");

    // ---- 3. quotient Q = C / (X^N - 1) on the LDE coset
    let quotient: Layer = per_channel(|ch| {
        let m = RNS_MODULI[ch];
        let cx = lane_ctx(air, chals[ch], gammas[ch], n_rows, ch);
        let w = root_of_unity(n, ch);
        let g = shift(ch);
        let g_n = pow(g, n_rows as u64, ch);
        let w_b = root_of_unity(blowup, ch);
        let z_inv: Vec<u32> = (0..blowup).map(|k| mod_inv_single(sub_mod(mul_mod_channel(g_n, pow(w_b, k as u64, ch), ch), 1, m), m)).collect();
        let tc = table_coeffs(ch);
        let last = pow(root_of_unity(n_rows, ch), (n_rows - 1) as u64, ch);
        let xs: Vec<u32> = std::iter::successors(Some(g), |&x| Some(mul_mod_channel(x, w, ch))).take(n).collect();
        let x_minus_1_inv = crate::batch_inverse_channel(&xs.iter().map(|&x| sub_mod(x, 1, m)).collect::<Vec<_>>(), ch);
        let (mut main_pt, mut main_nx) = (vec![0u32; l.main_cols()], vec![0u32; l.main_cols()]);
        let mut aux_pt = vec![Extension4::ZERO; l.aux_cols()];
        let (mut base, mut bus) = (Vec::new(), Vec::new());
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            let nx = (i + blowup) % n;
            for c in 0..l.main_cols() {
                main_pt[c] = main_lde[ch][c][i];
                main_nx[c] = main_lde[ch][c][nx];
            }
            for c in 0..l.aux_cols() {
                aux_pt[c] = aux_lde[ch][c][i];
            }
            let x = xs[i];
            let xn1 = sub_mod(mul_mod_channel(g_n, pow(w_b, (i % blowup) as u64, ch), ch), 1, m);
            let pt = Point { first_row: mul_mod_channel(xn1, x_minus_1_inv[i], ch), not_last: sub_mod(x, last, m) };
            let h_next = aux_lde[ch][l.sum()][nx];
            let tv = table_value(&tc, x, n_rows, ch);
            let c = composition(air, &l, &main_pt, &main_nx, &aux_pt, &h_next, tv, &pt, &cx, ch, &mut base, &mut bus);
            out.push(c.mul_scalar(z_inv[i % blowup], ch));
        }
        out
    });
    let q_tree = Tree::from_leaves(mode, crate::par_map(n, |i| q_leaf(mode, &std::array::from_fn(|ch| quotient[ch][i]))));
    t.absorb(b"stark/quotient", &q_tree.root());
    let deltas = t.challenge_ext4_all(b"stark/delta");

    // ---- 4. FRI on the random combination
    let f: Layer = per_channel(|ch| {
        let mut main_pt = vec![0u32; l.main_cols()];
        let mut aux_pt = vec![Extension4::ZERO; l.aux_cols()];
        (0..n)
            .map(|i| {
                for c in 0..l.main_cols() {
                    main_pt[c] = main_lde[ch][c][i];
                }
                for c in 0..l.aux_cols() {
                    aux_pt[c] = aux_lde[ch][c][i];
                }
                fri_combination(&main_pt, &aux_pt, &quotient[ch][i], &deltas[ch], ch)
            })
            .collect()
    });
    let shifts: [u32; DEFAULT_RNS_CHANNELS] = std::array::from_fn(shift);
    let (fri_proof, indices) = fri::prove_coset(f, &shifts, &params.fri(), t);

    // ---- 5. openings
    let open = |pos: usize| Opening {
        main: std::array::from_fn(|ch| (0..l.main_cols()).map(|c| main_lde[ch][c][pos]).collect()),
        aux: std::array::from_fn(|ch| (0..l.aux_cols()).map(|c| aux_lde[ch][c][pos]).collect()),
        quotient: std::array::from_fn(|ch| quotient[ch][pos]),
        main_path: main_tree.path(pos),
        aux_path: aux_tree.path(pos),
        q_path: q_tree.path(pos),
    };
    let openings = indices
        .iter()
        .map(|&i| {
            let j = i + n / 2;
            [open(i), open(j), open((i + blowup) % n), open((j + blowup) % n)]
        })
        .collect();

    StarkProof { rows, main_root: main_tree.root(), aux_root: aux_tree.root(), q_root: q_tree.root(), fri: fri_proof, openings }
}

/// Verifies a proof for `air`. `max_rows` bounds the public row count.
pub fn verify_air<A: Air>(air: &A, proof: &StarkProof, max_rows: usize, params: &StarkParams, t: &mut Transcript) -> bool {
    params.check();
    let l = Layout::of(air);
    let n_rows = 1usize << params.log_rows;
    let blowup = 1usize << params.log_blowup;
    let n = n_rows * blowup;
    if proof.openings.len() != params.num_queries || proof.rows > max_rows {
        return false;
    }
    start_transcript(t, air, params, proof.rows);
    t.absorb(b"stark/main", &proof.main_root);
    let chals = draw_challenges(t);
    t.absorb(b"stark/aux", &proof.aux_root);
    let gammas = t.challenge_ext4_all(b"stark/gamma");
    t.absorb(b"stark/quotient", &proof.q_root);
    let deltas = t.challenge_ext4_all(b"stark/delta");
    let shifts: [u32; DEFAULT_RNS_CHANNELS] = std::array::from_fn(shift);
    let tcs: [Vec<u32>; DEFAULT_RNS_CHANNELS] = std::array::from_fn(table_coeffs);
    let ctxs: [LaneCtx; DEFAULT_RNS_CHANNELS] = std::array::from_fn(|ch| lane_ctx(air, chals[ch], gammas[ch], n_rows, ch));
    let Some(indices) = fri::verify_coset(&proof.fri, &shifts, &params.fri(), t) else {
        return false;
    };
    let (mut base, mut bus) = (Vec::new(), Vec::new());
    let mode = t.mode();

    for (q, (&i, opens)) in indices.iter().zip(&proof.openings).enumerate() {
        let j = i + n / 2;
        let positions = [i, j, (i + blowup) % n, (j + blowup) % n];
        for (o, &pos) in opens.iter().zip(&positions) {
            let shape_ok = (0..DEFAULT_RNS_CHANNELS).all(|ch| o.main[ch].len() == l.main_cols() && o.aux[ch].len() == l.aux_cols());
            if !shape_ok
                || !fri::verify_path(mode, &proof.main_root, main_leaf_from(mode, o), pos, &o.main_path)
                || !fri::verify_path(mode, &proof.aux_root, aux_leaf_from(mode, o), pos, &o.aux_path)
                || !fri::verify_path(mode, &proof.q_root, q_leaf(mode, &o.quotient), pos, &o.q_path)
            {
                return false;
            }
        }
        for slot in 0..2 {
            let (here, next, pos) = (&opens[slot], &opens[slot + 2], positions[slot]);
            for ch in 0..DEFAULT_RNS_CHANNELS {
                let m = RNS_MODULI[ch];
                let x = mul_mod_channel(shift(ch), pow(root_of_unity(n, ch), pos as u64, ch), ch);
                let tv = table_value(&tcs[ch], x, n_rows, ch);
                let pt = point(x, n_rows, ch);
                let c = composition(air, &l, &here.main[ch], &next.main[ch], &here.aux[ch], &next.aux[ch][l.sum()], tv, &pt, &ctxs[ch], ch, &mut base, &mut bus);
                let z = sub_mod(pow(x, n_rows as u64, ch), 1, m);
                if c != here.quotient[ch].mul_scalar(z, ch) {
                    return false;
                }
                let f = fri_combination(&here.main[ch], &here.aux[ch], &here.quotient[ch], &deltas[ch], ch);
                if f != proof.fri.queries[q][0].pair[ch][slot] {
                    return false;
                }
            }
        }
    }
    true
}

// ---------------------------------------------------------------------------------------------
// MULMOD AIR
// ---------------------------------------------------------------------------------------------

/// Batch of uint256 MULMOD rows modulo `p` (see `uint256.rs`).
pub struct MulModAir<'a> {
    pub p: &'a Modulus256,
}

impl Air for MulModAir<'_> {
    fn statement(&self) -> Vec<u8> {
        [b"uint256-mulmod-v2".as_slice(), &self.p.bytes].concat()
    }
    fn width(&self) -> usize {
        NUM_COLUMNS
    }
    fn byte_cols(&self) -> usize {
        NUM_COLUMNS
    }
    fn num_constraints(&self) -> usize {
        CONSTRAINTS_PER_CHANNEL
    }
    fn eval(&self, cur: &[u32], _next: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        out.extend_from_slice(&eval_columns(cur, &p_columns(self.p, ch), ch));
    }
}

/// Rows per lane needed for `rows` MULMOD rows spread over the 5 lanes.
pub fn lane_rows(rows: usize) -> usize {
    rows.div_ceil(DEFAULT_RNS_CHANNELS)
}

/// Proves a batch of MULMOD rows. The rows are split into 5 lanes, one per RNS channel: lane j
/// holds rows [j*N, (j+1)*N) with N = 2^log_rows, padded with 0 * 0 rows. Each lane is a full,
/// independently sound STARK instance in its own field; all lanes share the commitments, the
/// transcript and one unified FRI, and are proven in parallel.
pub fn prove(rows: &[MulModRow], p: &Modulus256, params: &StarkParams, t: &mut Transcript) -> StarkProof {
    let n_rows = 1usize << params.log_rows;
    assert!(rows.len() <= n_rows * DEFAULT_RNS_CHANNELS, "too many rows for params");
    let pad = MulModRow::generate(&0u32.into(), &0u32.into(), p);
    let traces: [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] = std::array::from_fn(|lane| {
        rows.iter().skip(lane * n_rows).chain(std::iter::repeat(&pad)).take(n_rows).map(|r| r.limbs()).collect()
    });
    prove_trace_channels(&traces, rows.len(), p, params, t)
}

/// Proves an arbitrary byte trace, the same in every lane (used directly by the attack tests).
pub fn prove_trace(trace: &[Vec<u32>], real_rows: usize, p: &Modulus256, params: &StarkParams, t: &mut Transcript) -> StarkProof {
    let traces: [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] = std::array::from_fn(|_| trace.to_vec());
    prove_trace_channels(&traces, real_rows, p, params, t)
}

/// Proves one byte trace per lane (RNS channel).
pub fn prove_trace_channels(traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS], real_rows: usize, p: &Modulus256, params: &StarkParams, t: &mut Transcript) -> StarkProof {
    prove_air(&MulModAir { p }, traces, real_rows, params, t)
}

/// Verifies a MULMOD batch proof.
pub fn verify(proof: &StarkProof, p: &Modulus256, params: &StarkParams, t: &mut Transcript) -> bool {
    verify_air(&MulModAir { p }, proof, DEFAULT_RNS_CHANNELS << params.log_rows, params, t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    const PARAMS: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };

    fn rows(p: &Modulus256, count: usize, seed: u64) -> Vec<MulModRow> {
        let mut s = seed;
        let mut next = || {
            let words: Vec<u32> = (0..8)
                .map(|_| {
                    s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    (s >> 32) as u32
                })
                .collect();
            BigUint::new(words) % &p.value
        };
        (0..count).map(|_| MulModRow::generate(&next(), &next(), p)).collect()
    }

    #[test]
    fn honest_batch_verifies_secp256k1_and_bn254() {
        for p in [Modulus256::secp256k1(), Modulus256::bn254()] {
            let batch = rows(&p, 100, 1);
            let proof = prove(&batch, &p, &PARAMS, &mut Transcript::new(b"stark-test"));
            assert!(verify(&proof, &p, &PARAMS, &mut Transcript::new(b"stark-test")));
            // A proof for one modulus does not verify for another.
            let other = if p.bytes == Modulus256::bn254().bytes { Modulus256::secp256k1() } else { Modulus256::bn254() };
            assert!(!verify(&proof, &other, &PARAMS, &mut Transcript::new(b"stark-test")));
        }
    }

    #[test]
    fn forged_result_is_rejected() {
        let p = Modulus256::secp256k1();
        let mut trace: Vec<Vec<u32>> = rows(&p, 256, 2).iter().map(|r| r.limbs()).collect();
        // Row 17 claims r + 1 (canonical s adjusted) without refitting anything else.
        let r_byte = 96; // first byte of r
        let s_byte = 128;
        if trace[17][r_byte] < 255 && trace[17][s_byte] > 0 {
            trace[17][r_byte] += 1;
            trace[17][s_byte] -= 1;
        } else {
            trace[17][r_byte] ^= 1;
        }
        let proof = prove_trace(&trace, 256, &p, &PARAMS, &mut Transcript::new(b"stark-test"));
        assert!(!verify(&proof, &p, &PARAMS, &mut Transcript::new(b"stark-test")));
    }

    #[test]
    fn out_of_range_byte_is_rejected_by_logup() {
        // Rewrite a carry as (byte7 + 256, byte8 - 1): the same integer, so every MULMOD column
        // identity still holds; only the LogUp range check can catch it.
        let p = Modulus256::bn254();
        let mut trace: Vec<Vec<u32>> = rows(&p, 256, 3).iter().map(|r| r.limbs()).collect();
        let c0 = 160;
        assert!(trace[5][c0 + 1] >= 1);
        trace[5][c0] += 256;
        trace[5][c0 + 1] -= 1;
        for ch in 0..DEFAULT_RNS_CHANNELS {
            assert!(eval_columns(&trace[5], &p_columns(&p, ch), ch).iter().all(|&x| x == 0), "MULMOD AIR alone accepts it");
        }
        let proof = prove_trace(&trace, 256, &p, &PARAMS, &mut Transcript::new(b"stark-test"));
        assert!(!verify(&proof, &p, &PARAMS, &mut Transcript::new(b"stark-test")));
    }

    /// The 5 channels are not bound to each other (different fields), so they are used as 5
    /// independent lanes: different rows in every lane verify, and a forgery in a single lane
    /// is rejected by that lane alone.
    #[test]
    fn lanes_are_independent_and_each_is_sound() {
        let p = Modulus256::secp256k1();
        let mut traces: [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] =
            std::array::from_fn(|ch| rows(&p, 256, 100 + ch as u64).iter().map(|r| r.limbs()).collect());
        let proof = prove_trace_channels(&traces, 5 * 256, &p, &PARAMS, &mut Transcript::new(b"stark-test"));
        assert!(verify(&proof, &p, &PARAMS, &mut Transcript::new(b"stark-test")));

        // Forge r in lane 3 only and refit every carry; the identities can hold mod m_3 only if
        // they hold over Z, which they do not.
        let mut row = rows(&p, 1, 100 + 3)[0].clone();
        let fake = (row.r_value() + 1u32) % &p.value;
        row.r = crate::uint256::to_bytes32(&fake);
        row.s = crate::uint256::to_bytes32(&(&p.value - &fake - 1u32));
        traces[3][0] = row.limbs();
        assert!(!row.is_satisfied_in(&p, 3));
        let proof = prove_trace_channels(&traces, 5 * 256, &p, &PARAMS, &mut Transcript::new(b"stark-test"));
        assert!(!verify(&proof, &p, &PARAMS, &mut Transcript::new(b"stark-test")));
    }

    #[test]
    fn full_batch_uses_all_lanes() {
        let p = Modulus256::bn254();
        let batch = rows(&p, 5 * 256, 9);
        let proof = prove(&batch, &p, &PARAMS, &mut Transcript::new(b"stark-test"));
        assert_eq!(proof.rows, 5 * 256);
        assert!(verify(&proof, &p, &PARAMS, &mut Transcript::new(b"stark-test")));
    }

    #[test]
    fn tampered_proof_is_rejected() {
        let p = Modulus256::secp256k1();
        let proof = prove(&rows(&p, 50, 4), &p, &PARAMS, &mut Transcript::new(b"stark-test"));
        assert!(verify(&proof, &p, &PARAMS, &mut Transcript::new(b"stark-test")));

        let mut bad = proof.clone();
        bad.openings[0][0].main[0][3] ^= 1;
        assert!(!verify(&bad, &p, &PARAMS, &mut Transcript::new(b"stark-test")));

        let mut bad = proof.clone();
        bad.openings[1][1].quotient[2] = bad.openings[1][1].quotient[2].add(&Extension4::ONE, 2);
        assert!(!verify(&bad, &p, &PARAMS, &mut Transcript::new(b"stark-test")));

        let mut bad = proof.clone();
        bad.main_root[0] ^= 1;
        assert!(!verify(&bad, &p, &PARAMS, &mut Transcript::new(b"stark-test")));

        let mut bad = proof.clone();
        bad.rows = 51;
        assert!(!verify(&bad, &p, &PARAMS, &mut Transcript::new(b"stark-test")));
    }
}
