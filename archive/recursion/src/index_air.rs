//! AIR of the FRI query indices of one lane (docs/REKURSIONI.md, R7.2e).
//!
//! In per-lane mode query q's index is i = w mod 2^K (K = log2 n - 1), where w is an output word
//! of the transcript (`Transcript::challenge_index`). One row per query:
//!   - reads w from the transcript (`transcript_air::TAG_OUT_WORD`, at the public (k, p));
//!   - decomposes w into 31 bits and proves the decomposition canonical (w < m): with
//!     m = c * 2^s + 1, the top bits H satisfy H <= c (c - H has 31 - s bits) and H = c forces
//!     the low s bits to zero. Otherwise w + m could be decomposed instead and shift i;
//!   - gives the FRI fold rows their selection bits b_l (bit log2 n - 2 - l of i) and their
//!     first point x_0 = shift * w_n^i (product over the bits of i);
//!   - gives every leaf of the query its position: i and i + n/2 for the two composition rows,
//!     (pos + blowup) mod n for the next-row openings (the wrap is a boolean witness: a wrong one
//!     leaves a position outside [0, n), which no Merkle path reaches), and i mod (n_l / 2) for
//!     the FRI layer l.
//!
//! So the positions where the inner proof is opened are the ones Fiat-Shamir chose.

use crate::stark::{Air, BusTerm, Challenges, Point};
use crate::transcript_air::TAG_OUT_WORD;
use crate::{add_mod, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

/// (q, l, b_l) for the FRI fold rows.
pub const TAG_FOLD_BIT: u32 = 30;
/// (q, x_0) for the FRI fold row (q, 0).
pub const TAG_X0: u32 = 31;
const TAG_ROW: u32 = 32;

const BITS: usize = 31;

pub struct IndexAir {
    pub lane: usize,
    pub shift: u32,
    pub log_n: u32,
    pub log_blowup: u32,
    pub rounds: usize,
    /// Transcript position (k, p) of each query's word.
    pub words_at: Vec<(u32, u32)>,
    /// Leaf ids of query q: 6 for composition row 2q, 6 for row 2q + 1, then one per FRI layer:
    /// `comp_lid(q, slot, kind)` = 12 q + 6 slot + kind, `fri_lid(q, l)` = fri_base + q * rounds + l.
    pub fri_base: u32,
}

struct Lay {
    act: usize,
    q: usize,
    kq: usize,
    pq: usize,
    w: usize,
    bits: usize,
    db: usize,
    e: usize,
    inv: usize,
    cy: usize,
    xc: usize,
    width: usize,
}

impl IndexAir {
    pub(crate) fn k_bits(&self) -> usize {
        self.log_n as usize - 1
    }
    fn split(&self) -> (u32, usize) {
        let m = RNS_MODULI[self.lane];
        let s = (m - 1).trailing_zeros() as usize;
        ((m - 1) >> s, s)
    }
    fn lay(&self) -> Lay {
        let (_, s) = self.split();
        let mut at = 0;
        let mut take = |k: usize| {
            let a = at;
            at += k;
            a
        };
        let act = take(1);
        let q = take(1);
        let kq = take(1);
        let pq = take(1);
        let w = take(1);
        let bits = take(BITS);
        let db = take(BITS - s);
        let e = take(1);
        let inv = take(1);
        let cy = take(1);
        let xc = take(self.k_bits());
        Lay { act, q, kq, pq, w, bits, db, e, inv, cy, xc, width: at }
    }

    fn omega_pow2(&self, k: usize) -> u32 {
        let ch = self.lane;
        crate::stark::pow(crate::ntt::root_of_unity(1 << self.log_n, ch), 1u64 << k, ch)
    }

    /// Row of query q from its transcript word.
    fn row(&self, q: usize, w: u32) -> Vec<u32> {
        let l = self.lay();
        let ch = self.lane;
        let m = RNS_MODULI[ch];
        let (c, s) = self.split();
        let mut r = vec![0u32; l.width];
        r[l.act] = 1;
        r[l.q] = q as u32;
        r[l.kq] = self.words_at[q].0;
        r[l.pq] = self.words_at[q].1;
        r[l.w] = w;
        for k in 0..BITS {
            r[l.bits + k] = (w >> k) & 1;
        }
        let h = w >> s;
        let d = c - h;
        for t in 0..BITS - s {
            r[l.db + t] = (d >> t) & 1;
        }
        r[l.e] = (d == 0) as u32;
        r[l.inv] = if d == 0 { 0 } else { crate::mod_inv_single(d, m) };
        let n = 1u32 << self.log_n;
        let i = w & (n / 2 - 1);
        r[l.cy] = (i + n / 2 + (1 << self.log_blowup) >= n) as u32;
        let mut acc = self.shift;
        for k in 0..self.k_bits() {
            if r[l.bits + k] == 1 {
                acc = mul_mod_channel(acc, self.omega_pow2(k), ch);
            }
            r[l.xc + k] = acc;
        }
        r
    }

    pub fn traces(&self, words: &[u32], log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let n = 1usize << log_rows;
        assert_eq!(words.len(), self.words_at.len());
        let mut rows: Vec<Vec<u32>> = words.iter().enumerate().map(|(q, &w)| self.row(q, w)).collect();
        assert!(rows.len() <= n);
        // padding: a valid decomposition of 0 with act = 0
        let mut pad = self.row(0, 0);
        let l = self.lay();
        for c in [l.act, l.q, l.kq, l.pq] {
            pad[c] = 0;
        }
        rows.resize(n, pad);
        std::array::from_fn(|c| if c == self.lane { rows.clone() } else { Vec::new() })
    }

    /// Linear expression helpers on a row: value of bits [from, to) as an integer (mod m).
    fn bits_value(&self, row: &[u32], from: usize, to: usize) -> u32 {
        let l = self.lay();
        let m = RNS_MODULI[self.lane];
        (from..to).rev().fold(0u32, |acc, k| add_mod(add_mod(acc, acc, m), row[l.bits + k], m))
    }

    /// The (leaf id, position) tokens of a row, as linear expressions.
    fn leaf_positions(&self, row: &[u32]) -> Vec<(u32, u32)> {
        let l = self.lay();
        let ch = self.lane;
        let m = RNS_MODULI[ch];
        let n = 1u32 << self.log_n;
        let blow = 1u32 << self.log_blowup;
        let i = self.bits_value(row, 0, self.k_bits());
        let q = row[l.q];
        let pos = [i, add_mod(i, n / 2, m)];
        let next = [add_mod(i, blow, m), sub_mod(add_mod(add_mod(i, n / 2, m), blow, m), mul_mod_channel(row[l.cy], n, ch), m)];
        let mut out = Vec::new();
        for slot in 0..2u32 {
            for kind in 0..6u32 {
                let lid = add_mod(mul_mod_channel(q, 12, ch), 6 * slot + kind, m);
                out.push((lid, if kind < 3 { pos[slot as usize] } else { next[slot as usize] }));
            }
        }
        for layer in 0..self.rounds {
            let lid = add_mod(add_mod(self.fri_base % m, mul_mod_channel(q, self.rounds as u32, ch), m), layer as u32, m);
            // i mod (n_l / 2) = low log2(n) - 1 - layer bits
            out.push((lid, self.bits_value(row, 0, self.k_bits() - layer)));
        }
        out
    }
}

impl Air for IndexAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"query-index-v1".to_vec();
        for x in [self.lane as u32, self.shift, self.log_n, self.log_blowup, self.rounds as u32, self.fri_base] {
            v.extend_from_slice(&x.to_le_bytes());
        }
        v.extend(self.words_at.iter().flat_map(|&(k, p)| [k, p]).flat_map(|x| x.to_le_bytes()));
        v
    }
    fn width(&self) -> usize {
        self.lay().width
    }
    fn byte_cols(&self) -> usize {
        0
    }
    fn num_constraints(&self) -> usize {
        let (_, s) = self.split();
        1 + BITS + 1 + (BITS - s) + 1 + 2 + 1 + 1 + self.k_bits()
    }
    fn eval(&self, r: &[u32], _n: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        let l = self.lay();
        let m = RNS_MODULI[ch];
        let (c, s) = self.split();
        let mul = |a: u32, b: u32| mul_mod_channel(a, b, ch);
        let boolean = |x: u32| mul(x, sub_mod(x, 1, m));
        out.push(boolean(r[l.act]));
        for k in 0..BITS {
            out.push(boolean(r[l.bits + k]));
        }
        out.push(sub_mod(r[l.w], self.bits_value(r, 0, BITS), m));
        for t in 0..BITS - s {
            out.push(boolean(r[l.db + t]));
        }
        // c - H = sum db 2^t  (so H <= c)
        let h = self.bits_value(r, s, BITS);
        let d = sub_mod(c, h, m);
        let db = (0..BITS - s).rev().fold(0u32, |a, t| add_mod(add_mod(a, a, m), r[l.db + t], m));
        out.push(sub_mod(d, db, m));
        // e = [H == c]; then the low s bits are zero
        out.push(mul(r[l.e], d));
        out.push(sub_mod(mul(d, r[l.inv]), sub_mod(1, r[l.e], m), m));
        out.push(mul(r[l.e], self.bits_value(r, 0, s)));
        out.push(boolean(r[l.cy]));
        // x chain: xc_k = xc_{k-1} * (1 + b_k (w^(2^k) - 1)), xc_{-1} = shift
        for k in 0..self.k_bits() {
            let prev = if k == 0 { self.shift } else { r[l.xc + k - 1] };
            let f = add_mod(1, mul(r[l.bits + k], sub_mod(self.omega_pow2(k), 1, m)), m);
            out.push(sub_mod(r[l.xc + k], mul(prev, f), m));
        }
    }
    fn num_bus(&self) -> usize {
        3 + self.rounds + 12 + self.rounds
    }
    fn bus(&self, r: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        let l = self.lay();
        let m = RNS_MODULI[ch];
        let neg = sub_mod(0, r[l.act], m);
        let fp = |tag: u32, v: &[u32]| cc.fingerprint(tag, v, ch);
        out.push(BusTerm { den: fp(TAG_OUT_WORD, &[r[l.kq], r[l.pq], r[l.w]]), weight: r[l.act] });
        out.push(BusTerm { den: fp(TAG_ROW, &[r[l.q], r[l.kq], r[l.pq]]), weight: neg });
        out.push(BusTerm { den: fp(TAG_X0, &[r[l.q], r[l.xc + self.k_bits() - 1]]), weight: neg });
        for layer in 0..self.rounds {
            let b = if layer + 1 < self.rounds { r[l.bits + self.log_n as usize - 2 - layer] } else { 0 };
            out.push(BusTerm { den: fp(TAG_FOLD_BIT, &[r[l.q], layer as u32, b]), weight: neg });
        }
        for (lid, pos) in self.leaf_positions(r) {
            out.push(BusTerm { den: fp(crate::leaf_air::TAG_LEAF_INDEX, &[lid, pos]), weight: neg });
        }
    }
    fn bus_sum(&self, cc: &Challenges, ch: usize) -> Extension4 {
        let dens: Vec<Extension4> = self.words_at.iter().enumerate().map(|(q, &(k, p))| cc.fingerprint(TAG_ROW, &[q as u32, k, p], ch)).collect();
        match crate::logup::batch_inverse_ext4(&dens, ch) {
            Some(inv) => inv.iter().fold(Extension4::ZERO, |a, x| a.sub(x, ch)),
            None => Extension4::ONE,
        }
    }
}
