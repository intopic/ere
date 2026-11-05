//! End-to-end STARK for a batch of EVM `MULMOD` operations (Phase A of docs/PLANI_MVP.md).
//!
//! It connects every piece of the PDF architecture into one non-interactive proof:
//!   trace of `uint256` MULMOD rows (byte limbs, sound per channel, `uint256.rs`)
//!   + LogUp byte range check as AIR (inverse columns + running sum, `logup.rs` idea)
//!   + Fiat-Shamir (`transcript.rs`)
//!   + coset LDE with the PDF's 2^24 roots (`ntt.rs`)
//!   + V-UMT commitments: one Merkle tree per stage for all 5 channels
//!   + unified FRI (`fri.rs`) on a random linear combination of all columns and the quotient.
//!
//! Each RNS channel j is a lane: it runs the same AIR over its own field F_{m_j} (challenges in
//! F_{m_j}^4) on its own share of the rows. Commitments in different fields cannot be tied to
//! the same integers, so every lane must be sound alone; the byte-limb MULMOD AIR is (all its
//! identities stay below m_j / 2). The 5 lanes are proven in parallel and share one FRI.
//!
//! Stages:
//!  1. main trace  (315 byte columns + 1 multiplicity column)       -> root_main -> alpha_j
//!  2. aux trace   (315 inverses 1/(alpha - byte), 1/(alpha - T), running sum h) -> root_aux -> gamma_j
//!  3. quotient    Q = C / (X^N - 1), C = sum_k gamma^k * constraint_k  -> root_q -> delta_j
//!  4. FRI on      f = Q + sum_k delta^(k+1) * column_k                -> query indices
//!  5. openings of all three trees at x, -x and their next rows, for every FRI query.
//!
//! The lookup table T(x) = 0..255 repeating is a periodic column the verifier evaluates itself.
//! The running-sum constraint holds on every row of the cyclic domain, so its increments sum to
//! zero, which is exactly the LogUp identity (no boundary constraint needed).
//!
//! Not zero-knowledge (no masking); not needed for settlement proofs of public data.

use crate::fri::{self, FriParams, FriProof, Hash, Layer, Tree};
use crate::logup::batch_inverse_ext4;
use crate::ntt::{intt, ntt, root_of_unity};
use crate::transcript::Transcript;
use crate::uint256::{eval_columns, p_columns, Modulus256, MulModRow, PColumns, CONSTRAINTS_PER_CHANNEL, NUM_COLUMNS};
use crate::{mod_inv_single, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, EXTENSION_BETA, RNS_MODULI};
use blake3::Hasher;
use rayon::prelude::*;

/// Runs `f` for the 5 RNS channels in parallel: the channels share no data (PDF: carry-free,
/// independent residues), so each can live on its own core or GPU.
fn per_channel<T: Send, F: Fn(usize) -> T + Sync + Send>(f: F) -> [T; DEFAULT_RNS_CHANNELS] {
    let v: Vec<T> = (0..DEFAULT_RNS_CHANNELS).into_par_iter().map(f).collect();
    v.try_into().unwrap_or_else(|_| unreachable!())
}

pub const MAIN_COLS: usize = NUM_COLUMNS + 1; // bytes + multiplicity
pub const AUX_COLS: usize = NUM_COLUMNS + 2; // inverses + table inverse + running sum
const MULT: usize = NUM_COLUMNS;
const INV_T: usize = NUM_COLUMNS;
const SUM: usize = NUM_COLUMNS + 1;
pub const TABLE: usize = 256;
pub const CONSTRAINTS: usize = CONSTRAINTS_PER_CHANNEL + NUM_COLUMNS + 2;

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
        let per_open = DEFAULT_RNS_CHANNELS * (MAIN_COLS * 4 + AUX_COLS * 16 + 16);
        let paths: usize = self.openings.iter().flatten().map(|o| 32 * (o.main_path.len() + o.aux_path.len() + o.q_path.len())).sum();
        3 * 32 + self.fri.size_bytes() + self.openings.len() * 4 * per_open + paths
    }
}

fn shift(ch: usize) -> u32 {
    EXTENSION_BETA[ch] // a quadratic non-residue: the coset never meets the trace domain
}

fn pow(mut b: u32, mut e: u64, ch: usize) -> u32 {
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

/// C(x) = sum_k gamma^k * constraint_k at one point of one channel.
#[allow(clippy::too_many_arguments)]
fn composition(main: &[u32], aux: &[Extension4], h_next: &Extension4, t: u32, alpha: &Extension4, gamma: &Extension4, pc: &PColumns, ch: usize) -> Extension4 {
    let mut acc = Extension4::ZERO;
    let mut push = |v: Extension4| acc = acc.mul(gamma, ch).add(&v, ch);
    for c in eval_columns(&main[..NUM_COLUMNS], pc, ch) {
        push(Extension4::from_base(c));
    }
    let mut sum_inv = Extension4::ZERO;
    for c in 0..NUM_COLUMNS {
        let den = alpha.sub(&Extension4::from_base(main[c]), ch);
        push(aux[c].mul(&den, ch).sub(&Extension4::ONE, ch));
        sum_inv = sum_inv.add(&aux[c], ch);
    }
    let den_t = alpha.sub(&Extension4::from_base(t), ch);
    push(aux[INV_T].mul(&den_t, ch).sub(&Extension4::ONE, ch));
    // h(wx) - h(x) - sum_c 1/(alpha - col_c) + mult/(alpha - T) = 0
    let step = h_next.sub(&aux[SUM], ch).sub(&sum_inv, ch).add(&aux[INV_T].mul_scalar(main[MULT], ch), ch);
    push(step);
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

fn main_leaf(cols: &[[Vec<u32>; MAIN_COLS]; DEFAULT_RNS_CHANNELS], i: usize) -> Hash {
    let mut h = Hasher::new();
    h.update(b"SS-RAP/v2/main");
    for ch_cols in cols {
        for c in ch_cols {
            h.update(&c[i].to_le_bytes());
        }
    }
    *h.finalize().as_bytes()
}

fn aux_leaf(cols: &[Vec<Vec<Extension4>>; DEFAULT_RNS_CHANNELS], i: usize) -> Hash {
    let mut h = Hasher::new();
    h.update(b"SS-RAP/v2/aux");
    for ch_cols in cols {
        for c in ch_cols {
            h.update(&c[i].to_bytes());
        }
    }
    *h.finalize().as_bytes()
}

fn main_leaf_from(o: &Opening) -> Hash {
    let mut h = Hasher::new();
    h.update(b"SS-RAP/v2/main");
    for ch in 0..DEFAULT_RNS_CHANNELS {
        for v in &o.main[ch] {
            h.update(&v.to_le_bytes());
        }
    }
    *h.finalize().as_bytes()
}

fn aux_leaf_from(o: &Opening) -> Hash {
    let mut h = Hasher::new();
    h.update(b"SS-RAP/v2/aux");
    for ch in 0..DEFAULT_RNS_CHANNELS {
        for v in &o.aux[ch] {
            h.update(&v.to_bytes());
        }
    }
    *h.finalize().as_bytes()
}

fn q_leaf(q: &[Extension4; DEFAULT_RNS_CHANNELS]) -> Hash {
    let mut h = Hasher::new();
    h.update(b"SS-RAP/v2/quotient");
    for v in q {
        h.update(&v.to_bytes());
    }
    *h.finalize().as_bytes()
}

fn start_transcript(t: &mut Transcript, p: &Modulus256, params: &StarkParams, rows: usize) {
    t.absorb(b"stark/air", b"uint256-mulmod-v1");
    t.absorb(b"stark/modulus", &p.bytes);
    t.absorb(b"stark/shape", &[params.log_rows as u8, params.log_blowup as u8, params.num_queries as u8]);
    t.absorb(b"stark/rows", &(rows as u64).to_le_bytes());
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

/// Proves an arbitrary byte trace (used directly by the attack tests).
pub fn prove_trace(trace: &[Vec<u32>], real_rows: usize, p: &Modulus256, params: &StarkParams, t: &mut Transcript) -> StarkProof {
    let traces: [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] = std::array::from_fn(|_| trace.to_vec());
    prove_trace_channels(&traces, real_rows, p, params, t)
}

/// Proves one byte trace per lane (RNS channel).
pub fn prove_trace_channels(traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS], real_rows: usize, p: &Modulus256, params: &StarkParams, t: &mut Transcript) -> StarkProof {
    params.check();
    let n_rows = 1usize << params.log_rows;
    let blowup = 1usize << params.log_blowup;
    let n = n_rows * blowup;
    start_transcript(t, p, params, real_rows);

    // ---- 1. main trace: byte columns + multiplicities (per channel)
    let main_hs: [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] = std::array::from_fn(|ch| {
        let trace = &traces[ch];
        assert_eq!(trace.len(), n_rows);
        let mut mult = vec![0u32; n_rows];
        for row in trace {
            for &v in row {
                if (v as usize) < TABLE {
                    mult[v as usize] += 1;
                }
            }
        }
        (0..MAIN_COLS).map(|c| if c < NUM_COLUMNS { trace.iter().map(|r| r[c]).collect() } else { mult.clone() }).collect()
    });
    let main_lde: [[Vec<u32>; MAIN_COLS]; DEFAULT_RNS_CHANNELS] = per_channel(|ch| {
        let v: Vec<Vec<u32>> = main_hs[ch].iter().map(|col| coset_lde(&col.iter().map(|x| x % RNS_MODULI[ch]).collect::<Vec<_>>(), blowup, ch)).collect();
        v.try_into().unwrap()
    });
    let main_tree = Tree::from_leaves((0..n).map(|i| main_leaf(&main_lde, i)).collect());
    t.absorb(b"stark/main", &main_tree.root());
    let alphas = t.challenge_ext4_all(b"stark/alpha");

    // ---- 2. aux trace on the trace domain, then LDE
    let aux_lde: [Vec<Vec<Extension4>>; DEFAULT_RNS_CHANNELS] = per_channel(|ch| {
        let m = RNS_MODULI[ch];
        let alpha = alphas[ch];
        let main_h = &main_hs[ch];
        let mult = &main_h[MULT];
        let mut cols: Vec<Vec<Extension4>> = Vec::with_capacity(AUX_COLS);
        for c in 0..NUM_COLUMNS {
            let den: Vec<Extension4> = main_h[c].iter().map(|&v| alpha.sub(&Extension4::from_base(v % m), ch)).collect();
            cols.push(batch_inverse_ext4(&den, ch).expect("alpha hit a trace value"));
        }
        let den_t: Vec<Extension4> = (0..n_rows).map(|r| alpha.sub(&Extension4::from_base((r % TABLE) as u32), ch)).collect();
        cols.push(batch_inverse_ext4(&den_t, ch).unwrap());
        let mut h = vec![Extension4::ZERO; n_rows];
        for r in 0..n_rows - 1 {
            let mut step = Extension4::ZERO;
            for col in cols.iter().take(NUM_COLUMNS) {
                step = step.add(&col[r], ch);
            }
            step = step.sub(&cols[INV_T][r].mul_scalar(mult[r] % m, ch), ch);
            h[r + 1] = h[r].add(&step, ch);
        }
        cols.push(h);
        cols.iter().map(|col| coset_lde_ext(col, blowup, ch)).collect()
    });
    let aux_tree = Tree::from_leaves((0..n).map(|i| aux_leaf(&aux_lde, i)).collect());
    t.absorb(b"stark/aux", &aux_tree.root());
    let gammas = t.challenge_ext4_all(b"stark/gamma");

    // ---- 3. quotient Q = C / (X^N - 1) on the LDE coset
    let quotient: Layer = per_channel(|ch| {
        let pc = p_columns(p, ch);
        let w = root_of_unity(n, ch);
        let g = shift(ch);
        let g_n = pow(g, n_rows as u64, ch);
        let w_b = root_of_unity(blowup, ch);
        let z_inv: Vec<u32> = (0..blowup)
            .map(|k| mod_inv_single(sub_mod(mul_mod_channel(g_n, pow(w_b, k as u64, ch), ch), 1, RNS_MODULI[ch]), RNS_MODULI[ch]))
            .collect();
        let tc = table_coeffs(ch);
        let mut x = g;
        let mut out = Vec::with_capacity(n);
        let mut main_pt = vec![0u32; MAIN_COLS];
        let mut aux_pt = vec![Extension4::ZERO; AUX_COLS];
        for i in 0..n {
            for c in 0..MAIN_COLS {
                main_pt[c] = main_lde[ch][c][i];
            }
            for c in 0..AUX_COLS {
                aux_pt[c] = aux_lde[ch][c][i];
            }
            let h_next = aux_lde[ch][SUM][(i + blowup) % n];
            let tv = table_value(&tc, x, n_rows, ch);
            let c = composition(&main_pt, &aux_pt, &h_next, tv, &alphas[ch], &gammas[ch], &pc, ch);
            out.push(c.mul_scalar(z_inv[i % blowup], ch));
            x = mul_mod_channel(x, w, ch);
        }
        out
    });
    let q_tree = Tree::from_leaves((0..n).map(|i| q_leaf(&std::array::from_fn(|ch| quotient[ch][i]))).collect());
    t.absorb(b"stark/quotient", &q_tree.root());
    let deltas = t.challenge_ext4_all(b"stark/delta");

    // ---- 4. FRI on the random combination
    let f: Layer = per_channel(|ch| {
        let mut main_pt = vec![0u32; MAIN_COLS];
        let mut aux_pt = vec![Extension4::ZERO; AUX_COLS];
        (0..n)
            .map(|i| {
                for c in 0..MAIN_COLS {
                    main_pt[c] = main_lde[ch][c][i];
                }
                for c in 0..AUX_COLS {
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
        main: std::array::from_fn(|ch| (0..MAIN_COLS).map(|c| main_lde[ch][c][pos]).collect()),
        aux: std::array::from_fn(|ch| (0..AUX_COLS).map(|c| aux_lde[ch][c][pos]).collect()),
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

    StarkProof { rows: real_rows, main_root: main_tree.root(), aux_root: aux_tree.root(), q_root: q_tree.root(), fri: fri_proof, openings }
}

/// Verifies a MULMOD batch proof.
pub fn verify(proof: &StarkProof, p: &Modulus256, params: &StarkParams, t: &mut Transcript) -> bool {
    params.check();
    let n_rows = 1usize << params.log_rows;
    let blowup = 1usize << params.log_blowup;
    let n = n_rows * blowup;
    if proof.openings.len() != params.num_queries || proof.rows > n_rows * DEFAULT_RNS_CHANNELS {
        return false;
    }
    start_transcript(t, p, params, proof.rows);
    t.absorb(b"stark/main", &proof.main_root);
    let alphas = t.challenge_ext4_all(b"stark/alpha");
    t.absorb(b"stark/aux", &proof.aux_root);
    let gammas = t.challenge_ext4_all(b"stark/gamma");
    t.absorb(b"stark/quotient", &proof.q_root);
    let deltas = t.challenge_ext4_all(b"stark/delta");
    let shifts: [u32; DEFAULT_RNS_CHANNELS] = std::array::from_fn(shift);
    let tcs: [Vec<u32>; DEFAULT_RNS_CHANNELS] = std::array::from_fn(table_coeffs);
    let Some(indices) = fri::verify_coset(&proof.fri, &shifts, &params.fri(), t) else {
        return false;
    };

    for (q, (&i, opens)) in indices.iter().zip(&proof.openings).enumerate() {
        let j = i + n / 2;
        let positions = [i, j, (i + blowup) % n, (j + blowup) % n];
        for (o, &pos) in opens.iter().zip(&positions) {
            let shape_ok = (0..DEFAULT_RNS_CHANNELS).all(|ch| o.main[ch].len() == MAIN_COLS && o.aux[ch].len() == AUX_COLS);
            if !shape_ok
                || !fri::verify_path(&proof.main_root, main_leaf_from(o), pos, &o.main_path)
                || !fri::verify_path(&proof.aux_root, aux_leaf_from(o), pos, &o.aux_path)
                || !fri::verify_path(&proof.q_root, q_leaf(&o.quotient), pos, &o.q_path)
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
                let c = composition(&here.main[ch], &here.aux[ch], &next.aux[ch][SUM], tv, &alphas[ch], &gammas[ch], &p_columns(p, ch), ch);
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
