//! AIR of a per-lane Fiat-Shamir transcript, linked into the recursion stack (R7.2d).
//!
//! Like `sponge_air` (one Poseidon2 permutation per row, capacity chained by a bus), but nothing
//! that depends on the inner proof is public:
//!   - every rate word written by a row is a separate token (k, p, word). The verifier closes the
//!     public ones (labels, lengths, statement bytes, padding); the commitment roots and the
//!     final FRI layer are produced by other tables of the stack (`roots_air`, `final_air`);
//!   - the outputs go to the tables that use the challenges: the extension challenge of a
//!     permutation as (k, o1, o3, o5, o7) (a challenge_base takes the second of two squeezed
//!     words), and single words (k, p, o_p) for the query indices. Each output has a
//!     multiplicity column (how many consumers read it); the bus balance forces it;
//!   - the chain ends at a row flagged `last`, so the final capacity stays private.
//!
//! The verifier needs only the number of permutations and the public words.

use crate::poseidon2::WIDTH;
use crate::poseidon2_air::{run_at_ch, PERM_CONSTRAINTS, SBOX_COLS};
use crate::stark::{Air, BusTerm, Challenges, Point};
use crate::{add_mod, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

const ACT: usize = 0;
const LAST: usize = 1;
const K: usize = 2;
const BLOCK: usize = 3;
const CAP: usize = 11;
const MULT_EXT: usize = 19;
const MULT_W: usize = 20; // 4 columns, for o1, o3, o5, o7
const SBOX: usize = 24;
pub const COLS: usize = SBOX + SBOX_COLS;
pub const NUM_CONSTRAINTS: usize = 3 + PERM_CONSTRAINTS;

const TAG_CHAIN: u32 = 20;
/// A rate word written by permutation k at position p: (k, p, word).
pub const TAG_BLOCK_WORD: u32 = 21;
/// The extension challenge of permutation k: (k, o1, o3, o5, o7).
pub const TAG_EXT: u32 = 22;
/// An output word: (k, p, o_p), p odd.
pub const TAG_OUT_WORD: u32 = 23;

pub fn block_word(k: u32, p: u32, w: u32) -> Vec<u32> {
    vec![k, p, w]
}

pub fn ext_tuple(k: u32, e: &[u32]) -> Vec<u32> {
    let mut v = vec![k];
    v.extend_from_slice(e);
    v
}

pub struct TranscriptAir {
    pub lane: usize,
    pub perms: usize,
    /// Rate words the verifier knows: (k, p, word).
    pub public_words: Vec<(u32, u32, u32)>,
}

fn output(row: &mut [u32], fill: bool, out: Option<&mut Vec<u32>>, ch: usize) -> [u32; WIDTH] {
    let input: [u32; WIDTH] = std::array::from_fn(|i| if i < 8 { row[BLOCK + i] } else { row[CAP + i - 8] });
    run_at_ch(&input, row, SBOX, fill, out, ch)
}

impl TranscriptAir {
    /// Trace from the duplex log and the multiplicity of every output (ext challenge per k,
    /// output word per (k, odd p)).
    pub fn traces(&self, log: &[([u32; 8], [u32; WIDTH])], mult_ext: &[u32], mult_word: &[[u32; 4]], log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let ch = self.lane;
        let n = 1usize << log_rows;
        assert_eq!(log.len(), self.perms);
        assert!(log.len() <= n);
        let mut rows = Vec::with_capacity(n);
        let mut cap = [0u32; 8];
        for (k, (block, want)) in log.iter().enumerate() {
            let mut r = vec![0u32; COLS];
            r[ACT] = 1;
            r[LAST] = (k + 1 == log.len()) as u32;
            r[K] = k as u32;
            r[BLOCK..BLOCK + 8].copy_from_slice(block);
            r[CAP..CAP + 8].copy_from_slice(&cap);
            r[MULT_EXT] = mult_ext[k];
            r[MULT_W..MULT_W + 4].copy_from_slice(&mult_word[k]);
            let o = output(&mut r, true, None, ch);
            debug_assert_eq!(&o, want);
            cap.copy_from_slice(&o[8..]);
            rows.push(r);
        }
        let mut pad = vec![0u32; COLS];
        output(&mut pad, true, None, ch);
        rows.resize(n, pad);
        std::array::from_fn(|c| if c == ch { rows.clone() } else { Vec::new() })
    }
}

impl Air for TranscriptAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"transcript-air-v1".to_vec();
        for x in [self.lane as u32, self.perms as u32] {
            v.extend_from_slice(&x.to_le_bytes());
        }
        for &(k, p, w) in &self.public_words {
            for x in [k, p, w] {
                v.extend_from_slice(&x.to_le_bytes());
            }
        }
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
    fn eval(&self, c: &[u32], _nx: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        let m = RNS_MODULI[ch];
        let mul = |a: u32, b: u32| mul_mod_channel(a, b, ch);
        out.push(mul(c[ACT], sub_mod(c[ACT], 1, m)));
        out.push(mul(c[LAST], sub_mod(c[LAST], 1, m)));
        out.push(mul(c[LAST], sub_mod(1, c[ACT], m)));
        let mut row = c.to_vec();
        output(&mut row, false, Some(out), ch);
    }
    fn num_bus(&self) -> usize {
        2 + 8 + 1 + 4
    }
    fn bus(&self, c: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        let m = RNS_MODULI[ch];
        let mut row = c.to_vec();
        let o = output(&mut row, false, None, ch);
        let fp = |tag: u32, v: &[u32]| cc.fingerprint(tag, v, ch);
        let chain = |k: u32, cap: &[u32]| {
            let mut v = vec![k];
            v.extend_from_slice(cap);
            v
        };
        out.push(BusTerm { den: fp(TAG_CHAIN, &chain(c[K], &c[CAP..CAP + 8])), weight: c[ACT] });
        out.push(BusTerm { den: fp(TAG_CHAIN, &chain(add_mod(c[K], 1, m), &o[8..])), weight: sub_mod(c[LAST], c[ACT], m) });
        for p in 0..8 {
            out.push(BusTerm { den: fp(TAG_BLOCK_WORD, &block_word(c[K], p as u32, c[BLOCK + p])), weight: c[ACT] });
        }
        let neg = |x: u32| sub_mod(0, x, m);
        out.push(BusTerm { den: fp(TAG_EXT, &ext_tuple(c[K], &[o[1], o[3], o[5], o[7]])), weight: neg(c[MULT_EXT]) });
        for r in 0..4 {
            let p = 2 * r + 1;
            out.push(BusTerm { den: fp(TAG_OUT_WORD, &[c[K], p as u32, o[p]]), weight: neg(c[MULT_W + r]) });
        }
    }
    fn bus_sum(&self, cc: &Challenges, ch: usize) -> Extension4 {
        let mut dens = vec![cc.fingerprint(TAG_CHAIN, &[0; 9], ch)];
        dens.extend(self.public_words.iter().map(|&(k, p, w)| cc.fingerprint(TAG_BLOCK_WORD, &block_word(k, p, w), ch)));
        match crate::logup::batch_inverse_ext4(&dens, ch) {
            Some(inv) => inv.iter().fold(Extension4::ZERO, |a, x| a.add(x, ch)),
            None => Extension4::ONE,
        }
    }
}
