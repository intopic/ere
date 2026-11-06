//! AIR of the inner proof's public bus sum (docs/REKURSIONI.md, R7.2f).
//!
//! The inner verifier needs S / N, with S = sum over the inner AIR's public tuples of
//! weight / (beta - sum rho^(i+1) v_i) under the inner challenges beta, rho. Those challenges
//! are private in the stack (transcript outputs), so S is computed here: one row per public
//! tuple, a Horner chain for the fingerprint, its inverse, and a running sum down the table.
//! The last row of the table hands S / N to the composition rows (bus `TAG_SN`).
//!
//! The tuples themselves are public (they are the inner statement: initial and final account
//! states, the transactions); the verifier closes them on the outer bus.

use crate::stark::{Air, BusTerm, BusTuple, Challenges, Point};
use crate::transcript_air::{ext_tuple, TAG_EXT};
use crate::{mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

/// S / N of the inner proof, read by every composition row.
pub const TAG_SN: u32 = 33;
const TAG_PUBLIC: u32 = 34;

pub struct PublicSumAir {
    pub lane: usize,
    /// Rows of the inner trace (N).
    pub inner_rows: usize,
    pub tuples: Vec<BusTuple>,
    /// Transcript permutations of the inner beta and rho.
    pub beta_k: u32,
    pub rho_k: u32,
    /// Readers of S / N (composition rows).
    pub readers: u32,
    len: usize,
}

struct Lay {
    act: usize,
    fin: usize,
    tag: usize,
    w: usize,
    vals: usize,
    horner: usize,
    beta: usize,
    rho: usize,
    inv: usize,
    t: usize,
    sum: usize,
    width: usize,
}

fn ext(r: &[u32], at: usize) -> Extension4 {
    Extension4::new(r[at], r[at + 1], r[at + 2], r[at + 3])
}

impl PublicSumAir {
    pub fn new(lane: usize, inner_rows: usize, tuples: Vec<BusTuple>, beta_k: u32, rho_k: u32, readers: u32) -> Self {
        let len = tuples.iter().map(|t| t.values.len()).max().unwrap_or(0);
        Self { lane, inner_rows, tuples, beta_k, rho_k, readers, len }
    }

    fn lay(&self) -> Lay {
        let mut at = 0;
        let mut take = |k: usize| {
            let a = at;
            at += k;
            a
        };
        let act = take(1);
        let fin = take(1);
        let tag = take(1);
        let w = take(1);
        let vals = take(self.len);
        let horner = take(4 * (self.len + 1));
        let beta = take(4);
        let rho = take(4);
        let inv = take(4);
        let t = take(4);
        let sum = take(4);
        Lay { act, fin, tag, w, vals, horner, beta, rho, inv, t, sum, width: at }
    }

    fn n_inv(&self) -> u32 {
        let m = RNS_MODULI[self.lane];
        crate::mod_inv_single(self.inner_rows as u32 % m, m)
    }

    /// Fills (out = None) or checks the row-local columns: Horner, inverse, t = w * inv.
    fn walk(&self, r: &mut [u32], mut out: Option<&mut Vec<u32>>) {
        let l = self.lay();
        let ch = self.lane;
        let rho = ext(r, l.rho);
        let mut acc = Extension4::ZERO;
        let seq: Vec<u32> = (0..self.len).rev().map(|i| r[l.vals + i]).chain(std::iter::once(r[l.tag])).collect();
        for (s, v) in seq.into_iter().enumerate() {
            let at = l.horner + 4 * s;
            let e = acc.add(&Extension4::from_base(v), ch).mul(&rho, ch);
            match out.as_deref_mut() {
                Some(o) => o.extend(ext(r, at).sub(&e, ch).c),
                None => r[at..at + 4].copy_from_slice(&e.c),
            }
            acc = ext(r, at);
        }
        let fp = ext(r, l.beta).sub(&acc, ch);
        match out.as_deref_mut() {
            Some(o) => {
                o.extend(ext(r, l.inv).mul(&fp, ch).sub(&Extension4::ONE, ch).c);
                o.extend(ext(r, l.t).sub(&ext(r, l.inv).mul_scalar(r[l.w], ch), ch).c);
            }
            None => {
                let inv = fp.inverse(ch);
                r[l.inv..l.inv + 4].copy_from_slice(&inv.c);
                let t = inv.mul_scalar(r[l.w], ch);
                r[l.t..l.t + 4].copy_from_slice(&t.c);
            }
        }
    }

    /// Trace from the inner challenges.
    pub fn traces(&self, beta: &Extension4, rho: &Extension4, log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let l = self.lay();
        let ch = self.lane;
        let n = 1usize << log_rows;
        assert!(self.tuples.len() < n, "need a padding row after the public tuples");
        let mut rows = Vec::with_capacity(n);
        let mut sum = Extension4::ZERO;
        for r in 0..n {
            let mut row = vec![0u32; l.width];
            let t = self.tuples.get(r).or(self.tuples.first());
            if let Some(t) = t {
                row[l.tag] = t.tag;
                row[l.vals..l.vals + t.values.len()].copy_from_slice(&t.values);
            }
            if r < self.tuples.len() {
                row[l.act] = 1;
                row[l.w] = self.tuples[r].weight;
            }
            row[l.fin] = (r + 1 == n) as u32;
            row[l.beta..l.beta + 4].copy_from_slice(&beta.c);
            row[l.rho..l.rho + 4].copy_from_slice(&rho.c);
            row[l.sum..l.sum + 4].copy_from_slice(&sum.c);
            self.walk(&mut row, None);
            sum = sum.add(&ext(&row, l.t), ch);
            rows.push(row);
        }
        std::array::from_fn(|c| if c == ch { rows.clone() } else { Vec::new() })
    }

    fn public_tuple(t: &BusTuple, len: usize) -> Vec<u32> {
        let mut v = vec![t.tag, t.weight];
        v.extend_from_slice(&t.values);
        v.resize(2 + len, 0);
        v
    }
}

impl Air for PublicSumAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"public-sum-v1".to_vec();
        for x in [self.lane as u32, self.inner_rows as u32, self.beta_k, self.rho_k, self.readers] {
            v.extend_from_slice(&x.to_le_bytes());
        }
        for t in &self.tuples {
            v.extend(Self::public_tuple(t, self.len).iter().flat_map(|x| x.to_le_bytes()));
        }
        v
    }
    fn width(&self) -> usize {
        self.lay().width
    }
    fn byte_cols(&self) -> usize {
        0
    }
    fn num_constraints(&self) -> usize {
        3 + 4 * (self.len + 1) + 8 + 8
    }
    fn eval(&self, cur: &[u32], next: &[u32], pt: &Point, ch: usize, out: &mut Vec<u32>) {
        let l = self.lay();
        let m = RNS_MODULI[ch];
        let mul = |a: u32, b: u32| mul_mod_channel(a, b, ch);
        out.push(mul(cur[l.act], sub_mod(cur[l.act], 1, m)));
        out.push(mul(cur[l.w], sub_mod(1, cur[l.act], m))); // no weight on padding rows
        out.push(mul(cur[l.fin], pt.not_last)); // fin only on the last row
        let mut row = cur.to_vec();
        self.walk(&mut row, Some(out));
        // the sum starts at 0 and adds t on every row
        out.extend(ext(cur, l.sum).mul_scalar(pt.first_row, ch).c);
        let step = ext(next, l.sum).sub(&ext(cur, l.sum), ch).sub(&ext(cur, l.t), ch);
        out.extend(step.mul_scalar(pt.not_last, ch).c);
    }
    fn num_bus(&self) -> usize {
        4
    }
    fn bus(&self, r: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        let l = self.lay();
        let m = RNS_MODULI[ch];
        let fp = |tag: u32, v: &[u32]| cc.fingerprint(tag, v, ch);
        let mut pubt = vec![r[l.tag], r[l.w]];
        pubt.extend_from_slice(&r[l.vals..l.vals + self.len]);
        out.push(BusTerm { den: fp(TAG_PUBLIC, &pubt), weight: sub_mod(0, r[l.act], m) });
        out.push(BusTerm { den: fp(TAG_EXT, &ext_tuple(self.beta_k, &r[l.beta..l.beta + 4])), weight: r[l.act] });
        out.push(BusTerm { den: fp(TAG_EXT, &ext_tuple(self.rho_k, &r[l.rho..l.rho + 4])), weight: r[l.act] });
        // S / N from the last row (padding rows keep the sum; the last row is padding)
        let sn = ext(r, l.sum).add(&ext(r, l.t), ch).mul_scalar(self.n_inv(), ch);
        out.push(BusTerm { den: fp(TAG_SN, &sn.c), weight: sub_mod(0, mul_mod_channel(r[l.fin], self.readers % m, ch), m) });
    }
    fn bus_sum(&self, cc: &Challenges, ch: usize) -> Extension4 {
        let dens: Vec<Extension4> = self.tuples.iter().map(|t| cc.fingerprint(TAG_PUBLIC, &Self::public_tuple(t, self.len), ch)).collect();
        match crate::logup::batch_inverse_ext4(&dens, ch) {
            Some(inv) => inv.iter().fold(Extension4::ZERO, |a, x| a.sub(x, ch)),
            None => Extension4::ONE,
        }
    }
}
