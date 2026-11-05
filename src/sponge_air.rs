//! AIR for the Poseidon2 duplex sponge behind Fiat-Shamir (docs/REKURSIONI.md, R5b).
//!
//! The transcript in `HashMode::Poseidon2` is a chain of permutations: permutation k takes
//! (rate block b_k, capacity c_k) and outputs a state whose capacity half is c_{k+1} and whose
//! rate half r_k is what squeezes read. One row = one permutation. Rows are chained by a LogUp
//! bus on (k, capacity); each row also consumes its block (k, b_k) and produces its rate
//! output (k, r_k). The verifier closes the bus with the public data: the initial capacity
//! (zero), the final capacity, every absorbed block (statement, roots, ...) and every rate
//! output (the challenges). So the challenges are proven to be the sponge outputs of exactly
//! those messages, in that order, without the verifier running a single permutation.

use crate::poseidon2::WIDTH;
use crate::poseidon2_air::{run_at, PERM_CONSTRAINTS, SBOX_COLS};
use crate::stark::{Air, BusTerm, Challenges, Point};
use crate::{add_mod, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

pub const LANE: usize = crate::poseidon2_air::LANE;

const ACTIVE: usize = 0;
const K: usize = 1;
const BLOCK: usize = 2;
const CAP: usize = 10;
const SBOX: usize = 18;
pub const COLS: usize = SBOX + SBOX_COLS;
pub const NUM_CONSTRAINTS: usize = 1 + PERM_CONSTRAINTS;
const TAG_CHAIN: u32 = 5;
const TAG_BLOCK: u32 = 6;
const TAG_OUT: u32 = 7;

pub struct SpongeAir {
    /// The duplex log: (block, output state) per permutation, in order.
    pub log: Vec<([u32; 8], [u32; WIDTH])>,
}

fn tok(c: &Challenges, tag: u32, k: u32, w: &[u32]) -> Extension4 {
    let mut v = vec![k];
    v.extend_from_slice(w);
    c.fingerprint(tag, &v, LANE)
}

fn output(row: &mut [u32], fill: bool, out: Option<&mut Vec<u32>>) -> [u32; WIDTH] {
    let input: [u32; WIDTH] = std::array::from_fn(|i| if i < 8 { row[BLOCK + i] } else { row[CAP + i - 8] });
    run_at(&input, row, SBOX, fill, out)
}

impl SpongeAir {
    pub fn traces(&self, log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let n = 1usize << log_rows;
        assert!(self.log.len() <= n);
        let mut rows = Vec::with_capacity(n);
        let mut cap = [0u32; 8];
        for (k, (block, out)) in self.log.iter().enumerate() {
            let mut r = vec![0u32; COLS];
            r[ACTIVE] = 1;
            r[K] = k as u32;
            r[BLOCK..BLOCK + 8].copy_from_slice(block);
            r[CAP..CAP + 8].copy_from_slice(&cap);
            let o = output(&mut r, true, None);
            debug_assert_eq!(&o, out);
            cap.copy_from_slice(&o[8..]);
            rows.push(r);
        }
        let mut pad = vec![0u32; COLS];
        output(&mut pad, true, None);
        rows.resize(n, pad);
        std::array::from_fn(|ch| if ch == LANE { rows.clone() } else { vec![vec![0u32; COLS]; n] })
    }
}

impl Air for SpongeAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"sponge-poseidon2-koalabear-v1".to_vec();
        for (b, o) in &self.log {
            for x in b.iter().chain(&o[..8]) {
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
        if ch != LANE {
            out.extend(std::iter::repeat_n(0, NUM_CONSTRAINTS));
            return;
        }
        let m = RNS_MODULI[ch];
        out.push(mul_mod_channel(c[ACTIVE], sub_mod(c[ACTIVE], 1, m), ch));
        let mut row = c.to_vec();
        output(&mut row, false, Some(out));
    }
    fn num_bus(&self) -> usize {
        4
    }
    fn bus(&self, c: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        if ch != LANE {
            for _ in 0..4 {
                out.push(BusTerm { den: cc.beta, weight: 0 });
            }
            return;
        }
        let m = RNS_MODULI[ch];
        let (a, neg) = (c[ACTIVE], sub_mod(0, c[ACTIVE], m));
        let mut row = c.to_vec();
        let o = output(&mut row, false, None);
        out.push(BusTerm { den: tok(cc, TAG_CHAIN, c[K], &c[CAP..CAP + 8]), weight: a });
        out.push(BusTerm { den: tok(cc, TAG_BLOCK, c[K], &c[BLOCK..BLOCK + 8]), weight: a });
        out.push(BusTerm { den: tok(cc, TAG_CHAIN, add_mod(c[K], 1, m), &o[8..]), weight: neg });
        out.push(BusTerm { den: tok(cc, TAG_OUT, c[K], &o[..8]), weight: neg });
    }
    fn bus_sum(&self, cc: &Challenges, ch: usize) -> Extension4 {
        if ch != LANE {
            return Extension4::ZERO;
        }
        // + initial chain + blocks - final chain - outputs
        let n = self.log.len() as u32;
        let final_cap: Vec<u32> = self.log.last().map(|(_, o)| o[8..].to_vec()).unwrap_or(vec![0; 8]);
        let mut plus = vec![tok(cc, TAG_CHAIN, 0, &[0; 8])];
        let mut minus = vec![tok(cc, TAG_CHAIN, n, &final_cap)];
        for (k, (b, o)) in self.log.iter().enumerate() {
            plus.push(tok(cc, TAG_BLOCK, k as u32, b));
            minus.push(tok(cc, TAG_OUT, k as u32, &o[..8]));
        }
        let np = plus.len();
        plus.extend(minus);
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

    /// The duplex log of a real Poseidon2 transcript (a small STARK's worth of messages).
    fn real_log() -> (Vec<([u32; 8], [u32; WIDTH])>, Vec<u32>) {
        let mut t = Transcript::with_mode(b"outer", HashMode::Poseidon2);
        t.absorb(b"statement", b"some public statement bytes");
        let mut challenges = Vec::new();
        for r in 0..6u8 {
            t.absorb_digest(b"root", &[r; 32]);
            challenges.push(t.challenge_base(b"alpha", 1));
        }
        (t.poseidon2_duplex().unwrap().log.clone(), challenges)
    }

    fn run(air: &SpongeAir, traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]) -> bool {
        let proof = prove_air(air, traces, air.log.len(), &P, &mut Transcript::new(b"sponge"));
        verify_air(air, &proof, usize::MAX, &P, &mut Transcript::new(b"sponge"))
    }

    #[test]
    fn transcript_log_is_proven() {
        let (log, _) = real_log();
        assert!(log.len() >= 6);
        let air = SpongeAir { log };
        assert!(run(&air, &air.traces(P.log_rows)));
    }

    #[test]
    fn forged_challenge_or_message_is_rejected() {
        let (log, _) = real_log();
        let honest = SpongeAir { log: log.clone() };
        let traces = honest.traces(P.log_rows);
        // Claim a different squeezed output (i.e. a different challenge).
        let mut l = log.clone();
        l[3].1[0] ^= 1;
        assert!(!run(&SpongeAir { log: l }, &traces));
        // Claim a different absorbed block (a different root) with the same outputs.
        let mut l = log.clone();
        l[2].0[5] ^= 1;
        assert!(!run(&SpongeAir { log: l }, &traces));
        // Break the capacity chain in the trace.
        let mut bad = traces.clone();
        bad[LANE][4][CAP + 1] ^= 1;
        assert!(!run(&honest, &bad));
    }
}
