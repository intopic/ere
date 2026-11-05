//! AIR of the Merkle leaf hashes of one lane (docs/REKURSIONI.md, R7.2b).
//!
//! A leaf is `poseidon2::hash_ch([tag, values...])`: a sponge with the length in the last
//! capacity word, 8 words added to the rate per permutation. One row = one permutation of one
//! leaf. Rows of a leaf are chained by a LogUp bus on (leaf id, chunk k, index, state); every row
//! consumes its chunk (leaf id, k, 8 words) and the last row of a leaf produces the level-0
//! token (leaf id, 0, index, digest) of the Merkle path AIR.
//!
//! In a stack the chunks come from the AIR that holds the opened values (composition, FRI
//! fold) and the level-0 token goes to `merkle_air`, so neither the values nor the digest are
//! public: the opened values are proven to be what the committed tree holds. Public per leaf:
//! (leaf id, index, length), which fix the start state.

use crate::poseidon2::WIDTH;
use crate::poseidon2_air::{run_at_ch, PERM_CONSTRAINTS, SBOX_COLS};
use crate::stark::{Air, BusTerm, Challenges, Point};
use crate::{add_mod, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

const ACT: usize = 0;
const LAST: usize = 1;
const LID: usize = 2;
const K: usize = 3;
const IDX: usize = 4;
const SIN: usize = 5;
const CHUNK: usize = 21;
const SBOX: usize = 29;
pub const COLS: usize = SBOX + SBOX_COLS;
pub const NUM_CONSTRAINTS: usize = 3 + PERM_CONSTRAINTS;
const TAG_CHAIN: u32 = 12;
/// Bus tag of the chunks a leaf absorbs.
pub const TAG_CHUNK: u32 = 13;

/// Chunk tuple (leaf id, k, 8 words), zero-padded.
pub fn chunk_tuple(lid: u32, k: u32, chunk: &[u32]) -> Vec<u32> {
    let mut v = vec![lid, k];
    v.extend_from_slice(chunk);
    v.resize(10, 0);
    v
}

/// A leaf to hash: public id (= Merkle path id), position in the tree, number of words.
#[derive(Clone, Debug)]
pub struct LeafSpec {
    pub lid: u32,
    pub index: u32,
    pub len: usize,
}

pub struct LeafHashAir {
    pub lane: usize,
    pub leaves: Vec<LeafSpec>,
    /// Standalone mode: the leaf words are public (chunks closed by the verifier) and so is the
    /// digest. In a stack both are `None` and the tuples are linked.
    pub public_words: Option<Vec<Vec<u32>>>,
    pub public_digests: Option<Vec<[u32; 8]>>,
}

fn start_state(len: usize, ch: usize) -> [u32; WIDTH] {
    let mut s = [0u32; WIDTH];
    s[15] = len as u32 % RNS_MODULI[ch];
    s
}

fn perm(row: &mut [u32], fill: bool, out: Option<&mut Vec<u32>>, ch: usize) -> [u32; WIDTH] {
    let m = RNS_MODULI[ch];
    let input: [u32; WIDTH] = std::array::from_fn(|i| if i < 8 { add_mod(row[SIN + i], row[CHUNK + i], m) } else { row[SIN + i] });
    run_at_ch(&input, row, SBOX, fill, out, ch)
}

fn chain_tuple(lid: u32, k: u32, idx: u32, st: &[u32]) -> Vec<u32> {
    let mut v = vec![lid, k, idx];
    v.extend_from_slice(st);
    v
}

impl LeafHashAir {
    /// Trace from the leaf words (`words[i]` = tag word + values of leaf i).
    pub fn traces(&self, words: &[Vec<u32>], log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let ch = self.lane;
        let n = 1usize << log_rows;
        assert_eq!(words.len(), self.leaves.len());
        let mut rows = Vec::new();
        for (spec, w) in self.leaves.iter().zip(words) {
            assert_eq!(w.len(), spec.len);
            let mut st = start_state(spec.len, ch);
            let chunks: Vec<&[u32]> = w.chunks(8).collect();
            for (k, c) in chunks.iter().enumerate() {
                let mut r = vec![0u32; COLS];
                r[ACT] = 1;
                r[LAST] = (k + 1 == chunks.len()) as u32;
                r[LID] = spec.lid;
                r[K] = k as u32;
                r[IDX] = spec.index;
                r[SIN..SIN + WIDTH].copy_from_slice(&st);
                r[CHUNK..CHUNK + c.len()].copy_from_slice(c);
                st = perm(&mut r, true, None, ch);
                rows.push(r);
            }
            debug_assert_eq!(&st[..8], &crate::poseidon2::hash_ch(w, ch));
        }
        assert!(rows.len() <= n, "too many leaf permutations: {} rows for 2^{log_rows}", rows.len());
        let mut pad = vec![0u32; COLS];
        perm(&mut pad, true, None, ch);
        rows.resize(n, pad);
        std::array::from_fn(|c| if c == ch { rows.clone() } else { Vec::new() })
    }

    /// Permutations needed for the leaves.
    pub fn rows_needed(&self) -> usize {
        self.leaves.iter().map(|l| l.len.div_ceil(8)).sum()
    }
}

impl Air for LeafHashAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"leaf-hash-v1".to_vec();
        v.extend_from_slice(&(self.lane as u32).to_le_bytes());
        for l in &self.leaves {
            for x in [l.lid, l.index, l.len as u32] {
                v.extend_from_slice(&x.to_le_bytes());
            }
        }
        for w in self.public_words.iter().flatten() {
            v.extend(w.iter().flat_map(|x| x.to_le_bytes()));
        }
        for d in self.public_digests.iter().flatten() {
            v.extend(d.iter().flat_map(|x| x.to_le_bytes()));
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
    fn eval(&self, c: &[u32], _n: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        let m = RNS_MODULI[ch];
        let mul = |a: u32, b: u32| mul_mod_channel(a, b, ch);
        out.push(mul(c[ACT], sub_mod(c[ACT], 1, m)));
        out.push(mul(c[LAST], sub_mod(c[LAST], 1, m)));
        out.push(mul(c[LAST], sub_mod(1, c[ACT], m))); // last only on active rows
        let mut row = c.to_vec();
        perm(&mut row, false, Some(out), ch);
    }
    fn num_bus(&self) -> usize {
        4
    }
    fn bus(&self, c: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        let m = RNS_MODULI[ch];
        let mut row = c.to_vec();
        let o = perm(&mut row, false, None, ch);
        let fp = |tag: u32, v: &[u32]| cc.fingerprint(tag, v, ch);
        out.push(BusTerm { den: fp(TAG_CHAIN, &chain_tuple(c[LID], c[K], c[IDX], &c[SIN..SIN + WIDTH])), weight: c[ACT] });
        out.push(BusTerm { den: fp(TAG_CHAIN, &chain_tuple(c[LID], add_mod(c[K], 1, m), c[IDX], &o)), weight: sub_mod(c[LAST], c[ACT], m) });
        out.push(BusTerm { den: fp(TAG_CHUNK, &chunk_tuple(c[LID], c[K], &c[CHUNK..CHUNK + 8])), weight: c[ACT] });
        out.push(BusTerm { den: fp(crate::merkle_air::TAG_PATH, &crate::merkle_air::token_values(c[LID], 0, c[IDX], &o[..8])), weight: sub_mod(0, c[LAST], m) });
    }
    fn bus_sum(&self, cc: &Challenges, ch: usize) -> Extension4 {
        // + start states (+ public chunks) (- public digests)
        let mut plus: Vec<Extension4> = self.leaves.iter().map(|l| cc.fingerprint(TAG_CHAIN, &chain_tuple(l.lid, 0, l.index, &start_state(l.len, ch)), ch)).collect();
        if let Some(words) = &self.public_words {
            for (l, w) in self.leaves.iter().zip(words) {
                for (k, c) in w.chunks(8).enumerate() {
                    plus.push(cc.fingerprint(TAG_CHUNK, &chunk_tuple(l.lid, k as u32, c), ch));
                }
            }
        }
        let np = plus.len();
        if let Some(ds) = &self.public_digests {
            for (l, d) in self.leaves.iter().zip(ds) {
                plus.push(cc.fingerprint(crate::merkle_air::TAG_PATH, &crate::merkle_air::token_values(l.lid, 0, l.index, d), ch));
            }
        }
        match crate::logup::batch_inverse_ext4(&plus, ch) {
            Some(inv) => inv.iter().enumerate().fold(Extension4::ZERO, |a, (i, x)| if i < np { a.add(x, ch) } else { a.sub(x, ch) }),
            None => Extension4::ONE,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::HashMode;
    use crate::stark::{prove_air, verify_air, StarkParams};
    use crate::transcript::Transcript;

    const P: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };

    fn case(ch: usize) -> (LeafHashAir, Vec<Vec<u32>>) {
        let words: Vec<Vec<u32>> = [1usize, 8, 9, 30, 64].iter().enumerate().map(|(i, &len)| (0..len as u32).map(|k| (k * 97 + i as u32 * 13 + 1) % RNS_MODULI[ch]).collect()).collect();
        let leaves = words.iter().enumerate().map(|(i, w)| LeafSpec { lid: i as u32 * 3 + 1, index: 5 * i as u32, len: w.len() }).collect();
        let digests = words.iter().map(|w| crate::poseidon2::hash_ch(w, ch)).collect();
        (LeafHashAir { lane: ch, leaves, public_words: Some(words.clone()), public_digests: Some(digests) }, words)
    }

    fn ok(air: &LeafHashAir, traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]) -> bool {
        let t = || Transcript::with_mode(b"leaf", HashMode::Lane(air.lane as u8));
        let proof = prove_air(air, traces, air.leaves.len(), &P, &mut t());
        verify_air(air, &proof, usize::MAX, &P, &mut t())
    }

    #[test]
    fn leaves_hash_in_every_lane() {
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let (air, words) = case(ch);
            assert!(ok(&air, &air.traces(&words, P.log_rows)), "lane {ch}");
        }
    }

    #[test]
    fn wrong_words_digest_or_truncation_are_rejected() {
        let ch = 3;
        let (air, words) = case(ch);
        let traces = air.traces(&words, P.log_rows);

        let mut bad = case(ch).0;
        bad.public_digests.as_mut().unwrap()[2][0] ^= 1;
        assert!(!ok(&bad, &traces), "wrong digest");

        let mut bad = case(ch).0;
        bad.public_words.as_mut().unwrap()[3][17] ^= 1;
        assert!(!ok(&bad, &traces), "wrong word");

        // Stop leaf 4 one chunk early (claim its digest after 7 of 8 chunks).
        let mut t = traces.clone();
        let last_of_4 = 1 + 1 + 2 + 4 + 7; // rows before leaf 4's last chunk
        t[ch][last_of_4 - 1][LAST] = 1;
        assert!(!ok(&air, &t), "truncated leaf");
    }
}
