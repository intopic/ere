//! AIR of the FRI folding checks of one lane (docs/REKURSIONI.md, R6.2a).
//!
//! The FRI verifier does two kinds of work: hashes (Merkle paths, Fiat-Shamir: `merkle_air.rs`,
//! `sponge_air.rs`) and algebra. This AIR is the algebra of FRI: for every query q and layer l
//! it checks, in the lane's own field F_{m_j},
//!
//!   fold = (f0 + f1) / 2 + alpha_l * (f0 - f1) / (2 x_l)
//!
//! and that `fold` is the element of the next layer's pair that the query index selects (or the
//! constant final layer after the last round). One row per (query, layer).
//!
//! The evaluation point is not a free witness. With n_l the layer size, j_l = i mod (n_l / 2)
//! and x_l = s_l * w_{n_l}^{j_l}:
//!
//!   x_{l+1} = (-1)^{b_l} * x_l^2,   b_l = bit (log2 n_0 - 2 - l) of the query index i,
//!
//! and b_l also picks the slot of the next pair. So the AIR derives every x_l from x_0 = s * w^i,
//! and the bits and x_0 come from the public claim.
//!
//! Public claim (sent on one LogUp bus, one tuple per row, the verifier adds the expected
//! multiset): (q, l, continues, first, b_l, alpha_l, final-or-0, x_0-or-0). Rows of the same
//! query are consecutive (transition constraints on q and l), so the bus fixes the whole chain.
//! In R7 the alphas and indices come from the sponge AIR instead of the public claim.
//!
//! Every constraint has degree <= 2; width 36, 28 constraints.

use crate::stark::{Air, BusTerm, Challenges, Point};
use crate::{add_mod, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

const ACT: usize = 0;
const CONT: usize = 1;
const FIRST: usize = 2;
const B: usize = 3;
const SEL: usize = 4;
const Q: usize = 5;
const L: usize = 6;
const X: usize = 7;
const INV: usize = 8;
const X2: usize = 9;
const SX: usize = 10;
const XZ: usize = 11;
const F0: usize = 12;
const F1: usize = 16;
const AL: usize = 20;
const D: usize = 24;
const OUT: usize = 28;
const FIN: usize = 32;
pub const COLS: usize = 36;
pub const NUM_CONSTRAINTS: usize = 28;
const TAG: u32 = 7;

/// The public claim: lane j's FRI verifier view.
#[derive(Clone, Debug)]
pub struct FriFoldAir {
    pub lane: usize,
    /// Coset shift of layer 0.
    pub shift: u32,
    /// log2 of the layer-0 domain size.
    pub log_n: u32,
    /// Folding challenge of every layer (the number of rounds is `alphas.len()`).
    pub alphas: Vec<Extension4>,
    pub indices: Vec<usize>,
    pub final_value: Extension4,
}

fn ext(row: &[u32], at: usize) -> Extension4 {
    Extension4::new(row[at], row[at + 1], row[at + 2], row[at + 3])
}

fn put(row: &mut [u32], at: usize, e: &Extension4) {
    row[at..at + 4].copy_from_slice(&e.c);
}

impl FriFoldAir {
    fn rounds(&self) -> usize {
        self.alphas.len()
    }

    /// b_l: bit (log_n - 2 - l) of i; 0 for the last layer (nothing to select).
    fn bit(&self, i: usize, l: usize) -> u32 {
        if l + 1 < self.rounds() {
            ((i >> (self.log_n as usize - 2 - l)) & 1) as u32
        } else {
            0
        }
    }

    fn x0(&self, i: usize) -> u32 {
        let ch = self.lane;
        let w = crate::ntt::root_of_unity(1 << self.log_n, ch);
        mul_mod_channel(self.shift, crate::stark::pow(w, i as u64, ch), ch)
    }

    /// The public tuple of row (q, l).
    fn tuple(&self, q: usize, l: usize) -> Vec<u32> {
        let last = l + 1 == self.rounds();
        let fin = if last { self.final_value } else { Extension4::ZERO };
        let mut v = vec![q as u32, l as u32, !last as u32, (l == 0) as u32, self.bit(self.indices[q], l)];
        v.extend(self.alphas[l].c);
        v.extend(fin.c);
        v.push(if l == 0 { self.x0(self.indices[q]) } else { 0 });
        v
    }

    fn row_tuple(row: &[u32]) -> Vec<u32> {
        let mut v = vec![row[Q], row[L], row[CONT], row[FIRST], row[B]];
        v.extend_from_slice(&row[AL..AL + 4]);
        v.extend_from_slice(&row[FIN..FIN + 4]);
        v.push(row[XZ]);
        v
    }

    /// Trace of the lane (2^log_rows rows) from the opened pairs: `pairs[q][l]` = (f(x), f(-x))
    /// of query q at layer l. The other lanes are empty (the proof runs in `HashMode::Lane`).
    pub fn traces(&self, pairs: &[Vec<[Extension4; 2]>], log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let ch = self.lane;
        let m = RNS_MODULI[ch];
        let n = 1usize << log_rows;
        let rounds = self.rounds();
        assert_eq!(pairs.len(), self.indices.len());
        assert!(self.indices.len() * rounds <= n, "too many fold rows for the trace");
        let mut rows = Vec::with_capacity(n);
        for (q, &i) in self.indices.iter().enumerate() {
            let mut x = self.x0(i);
            for l in 0..rounds {
                let mut r = vec![0u32; COLS];
                let last = l + 1 == rounds;
                let b = self.bit(i, l);
                r[ACT] = 1;
                r[CONT] = !last as u32;
                r[FIRST] = (l == 0) as u32;
                r[B] = b;
                r[SEL] = r[CONT] * b;
                r[Q] = q as u32;
                r[L] = l as u32;
                r[X] = x;
                r[INV] = crate::mod_inv_single(x, m);
                r[X2] = mul_mod_channel(x, x, ch);
                r[SX] = if b == 1 { sub_mod(0, r[X2], m) } else { r[X2] };
                r[XZ] = if l == 0 { x } else { 0 };
                let [f0, f1] = pairs[q][l];
                let alpha = self.alphas[l];
                let d = alpha.mul(&f0.sub(&f1, ch), ch);
                let inv2 = m.div_ceil(2);
                let out = f0.add(&f1, ch).add(&d.mul_scalar(r[INV], ch), ch).mul_scalar(inv2, ch);
                put(&mut r, F0, &f0);
                put(&mut r, F1, &f1);
                put(&mut r, AL, &alpha);
                put(&mut r, D, &d);
                put(&mut r, OUT, &out);
                if last {
                    put(&mut r, FIN, &self.final_value);
                }
                rows.push(r);
                x = rows[rows.len() - 1][SX]; // x_{l+1} = (-1)^b x_l^2
            }
        }
        let mut pad = vec![0u32; COLS];
        for c in [X, INV, X2, SX] {
            pad[c] = 1;
        }
        rows.resize(n, pad);
        std::array::from_fn(|c| if c == ch { rows.clone() } else { Vec::new() })
    }
}

impl Air for FriFoldAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"fri-fold-v1".to_vec();
        for x in [self.lane as u32, self.shift, self.log_n, self.alphas.len() as u32, self.indices.len() as u32] {
            v.extend_from_slice(&x.to_le_bytes());
        }
        v.extend(self.alphas.iter().flat_map(|a| a.to_bytes()));
        v.extend(self.indices.iter().flat_map(|&i| (i as u64).to_le_bytes()));
        v.extend(self.final_value.to_bytes());
        v
    }
    fn width(&self) -> usize {
        COLS
    }
    fn byte_cols(&self) -> usize {
        0
    }
    fn num_constraints(&self) -> usize {
        NUM_CONSTRAINTS
    }
    fn eval(&self, cur: &[u32], next: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        if ch != self.lane {
            out.extend(std::iter::repeat_n(0, NUM_CONSTRAINTS));
            return;
        }
        let m = RNS_MODULI[ch];
        let mul = |a: u32, b: u32| mul_mod_channel(a, b, ch);
        let sub = |a: u32, b: u32| sub_mod(a, b, m);
        let start = out.len();
        for c in [ACT, CONT, FIRST, B] {
            out.push(mul(cur[c], sub(cur[c], 1)));
        }
        out.push(sub(cur[SEL], mul(cur[CONT], cur[B])));
        out.push(sub(mul(cur[X], cur[INV]), 1));
        out.push(sub(cur[X2], mul(cur[X], cur[X])));
        // sx = (1 - 2b) x^2
        out.push(add_mod(sub(cur[SX], cur[X2]), mul(add_mod(cur[B], cur[B], m), cur[X2]), m));
        out.push(sub(cur[XZ], mul(cur[FIRST], cur[X])));
        let (f0, f1, alpha, d, o) = (ext(cur, F0), ext(cur, F1), ext(cur, AL), ext(cur, D), ext(cur, OUT));
        out.extend(d.sub(&alpha.mul(&f0.sub(&f1, ch), ch), ch).c);
        // 2 out = f0 + f1 + d / x
        out.extend(o.add(&o, ch).sub(&f0.add(&f1, ch), ch).sub(&d.mul_scalar(cur[INV], ch), ch).c);
        // transitions inside a query
        out.push(mul(cur[CONT], sub(next[X], cur[SX])));
        out.push(mul(cur[CONT], sub(next[Q], cur[Q])));
        out.push(mul(cur[CONT], sub(sub(next[L], cur[L]), 1)));
        let (n0, n1) = (ext(next, F0), ext(next, F1));
        let chosen = n0.mul_scalar(cur[CONT], ch).add(&n1.sub(&n0, ch).mul_scalar(cur[SEL], ch), ch);
        out.extend(chosen.sub(&o.mul_scalar(cur[CONT], ch), ch).c);
        // the last layer folds to the public constant
        out.extend(o.sub(&ext(cur, FIN), ch).mul_scalar(sub(1, cur[CONT]), ch).c);
        debug_assert_eq!(out.len() - start, NUM_CONSTRAINTS);
    }
    fn num_bus(&self) -> usize {
        1
    }
    fn bus(&self, cur: &[u32], c: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        if ch != self.lane {
            out.push(BusTerm { den: c.beta, weight: 0 });
            return;
        }
        out.push(BusTerm { den: c.fingerprint(TAG, &Self::row_tuple(cur), ch), weight: sub_mod(0, cur[ACT], RNS_MODULI[ch]) });
    }
    fn bus_sum(&self, c: &Challenges, ch: usize) -> Extension4 {
        if ch != self.lane {
            return Extension4::ZERO;
        }
        let dens: Vec<Extension4> = (0..self.indices.len())
            .flat_map(|q| (0..self.rounds()).map(move |l| (q, l)))
            .map(|(q, l)| c.fingerprint(TAG, &self.tuple(q, l), ch))
            .collect();
        match crate::logup::batch_inverse_ext4(&dens, ch) {
            Some(inv) => inv.iter().fold(Extension4::ZERO, |a, x| a.sub(x, ch)),
            None => Extension4::ONE,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fri::{self, FriParams};
    use crate::hash::HashMode;
    use crate::stark::{prove_air, verify_air, StarkParams};
    use crate::transcript::Transcript;

    const FP: FriParams = FriParams { log_degree: 6, log_blowup: 2, num_queries: 12 };
    const SP: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };

    /// A per-lane FRI proof of a random polynomial on the coset beta_j * <w>, and its claim.
    fn lane_fri(j: usize, seed: u64) -> (FriFoldAir, Vec<Vec<[Extension4; 2]>>, fri::FriProof) {
        let n = FP.domain_size();
        let mut s = seed;
        let shift = crate::EXTENSION_BETA[j];
        let mut c: Vec<u32> = (0..1usize << FP.log_degree)
            .map(|_| {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                ((s >> 33) as u32) % RNS_MODULI[j]
            })
            .collect();
        let mut gk = 1u32;
        for x in c.iter_mut() {
            *x = mul_mod_channel(*x, gk, j);
            gk = mul_mod_channel(gk, shift, j);
        }
        c.resize(n, 0);
        crate::ntt::ntt(&mut c, j);
        let layer: fri::Layer = std::array::from_fn(|ch| if ch == j { c.iter().map(|&v| Extension4::from_base(v)).collect() } else { Vec::new() });
        let mut shifts = [1u32; DEFAULT_RNS_CHANNELS];
        shifts[j] = shift;
        let (proof, _) = fri::prove_coset(layer, &shifts, &FP, &mut Transcript::with_mode(b"fri-air", HashMode::Lane(j as u8)));
        let view = fri::verify_view(&proof, &shifts, &FP, &mut Transcript::with_mode(b"fri-air", HashMode::Lane(j as u8))).expect("honest FRI verifies");
        let air = FriFoldAir {
            lane: j,
            shift,
            log_n: n.trailing_zeros(),
            alphas: view.alphas.iter().map(|a| a[j]).collect(),
            indices: view.indices,
            final_value: proof.final_layer[j][0],
        };
        let pairs = proof.queries.iter().map(|q| q.iter().map(|o| o.pair[j]).collect()).collect();
        (air, pairs, proof)
    }

    fn prove_and_verify(air: &FriFoldAir, traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS], claim: &FriFoldAir) -> bool {
        let t = || Transcript::with_mode(b"fold", HashMode::Lane(air.lane as u8));
        let rows = claim.indices.len() * claim.alphas.len();
        let proof = prove_air(claim, traces, rows, &SP, &mut t());
        verify_air(claim, &proof, 1 << SP.log_rows, &SP, &mut t())
    }

    #[test]
    fn point_chain_matches_the_native_verifier() {
        let (air, _, _) = lane_fri(2, 1);
        let ch = air.lane;
        for &i in &air.indices {
            let mut x = air.x0(i);
            let (mut n, mut s) = (1usize << air.log_n, air.shift);
            for l in 0..air.alphas.len() {
                let j = i % (n / 2);
                assert_eq!(x, mul_mod_channel(s, crate::stark::pow(crate::ntt::root_of_unity(n, ch), j as u64, ch), ch));
                let x2 = mul_mod_channel(x, x, ch);
                x = if air.bit(i, l) == 1 { sub_mod(0, x2, RNS_MODULI[ch]) } else { x2 };
                n /= 2;
                s = mul_mod_channel(s, s, ch);
            }
        }
    }

    #[test]
    fn honest_folds_verify_in_every_lane() {
        for j in 0..DEFAULT_RNS_CHANNELS {
            let (air, pairs, _) = lane_fri(j, 10 + j as u64);
            let traces = air.traces(&pairs, SP.log_rows);
            let mut cons = Vec::new();
            for w in traces[j].windows(2) {
                air.eval(&w[0], &w[1], &Point { first_row: 0, not_last: 1 }, j, &mut cons);
            }
            assert!(cons.iter().all(|&c| c == 0), "lane {j}: honest trace violates a constraint");
            assert!(prove_and_verify(&air, &traces, &air), "lane {j}");
        }
    }

    #[test]
    fn forged_folds_and_claims_are_rejected() {
        let j = 1;
        let (air, pairs, _) = lane_fri(j, 77);

        // A layer value that does not fold correctly (what a cheating FRI prover must send).
        let mut bad_pairs = pairs.clone();
        bad_pairs[3][2][0] = bad_pairs[3][2][0].add(&Extension4::ONE, j);
        let traces = air.traces(&bad_pairs, SP.log_rows);
        assert!(!prove_and_verify(&air, &traces, &air), "forged layer value");

        let traces = air.traces(&pairs, SP.log_rows);
        let mut claim = air.clone();
        claim.alphas[1] = claim.alphas[1].add(&Extension4::ONE, j);
        assert!(!prove_and_verify(&air, &traces, &claim), "wrong folding challenge");

        let mut claim = air.clone();
        claim.indices[0] ^= 1 << 3;
        assert!(!prove_and_verify(&air, &traces, &claim), "wrong query index");

        let mut claim = air.clone();
        claim.final_value = claim.final_value.add(&Extension4::ONE, j);
        assert!(!prove_and_verify(&air, &traces, &claim), "wrong final layer");

        // Break the chain: the trace says a row does not continue to the next layer.
        assert_eq!(traces[j][2][CONT], 1);
        let mut cut = traces.clone();
        cut[j][2][CONT] = 0;
        cut[j][2][SEL] = 0;
        assert!(!prove_and_verify(&air, &cut, &air), "chain cut");

        // Flip a selection bit (and the point chain with it).
        let mut flip = traces.clone();
        let r = &mut flip[j][4];
        r[B] ^= 1;
        r[SEL] = r[CONT] * r[B];
        r[SX] = sub_mod(0, r[SX], RNS_MODULI[j]);
        assert!(!prove_and_verify(&air, &flip, &air), "flipped bit");
    }

    #[test]
    fn a_cheating_fri_proof_cannot_get_a_fold_proof() {
        // Natively rejected FRI proof (one opened value changed): no trace of its openings
        // satisfies the fold AIR.
        let j = 3;
        let (air, _, proof) = lane_fri(j, 5);
        let mut bad = proof.clone();
        bad.queries[2][1].pair[j][1] = bad.queries[2][1].pair[j][1].add(&Extension4::ONE, j);
        let pairs: Vec<Vec<[Extension4; 2]>> = bad.queries.iter().map(|q| q.iter().map(|o| o.pair[j]).collect()).collect();
        let traces = air.traces(&pairs, SP.log_rows);
        assert!(!prove_and_verify(&air, &traces, &air));
    }
}
