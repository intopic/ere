//! AIR for the Poseidon2-KoalaBear permutation (docs/REKURSIONI.md, R2b): one permutation per
//! row, in the KoalaBear lane.
//!
//! Every S-box gets 4 columns of degree-2 steps (s^2, ... up to s^7, see `run_at_ch`), so all
//! constraints have degree 2 (the engine's limit); the linear layers are evaluated inside the
//! constraints, so they need no columns. Width 1 + 16 + 4 * (8 * 16 + 22) = 617.
//!
//! Each active row sends (input, output) on a LogUp bus. In this standalone form the verifier
//! adds the public list of (input, output) pairs, which proves that every listed pair is a
//! correct evaluation of the permutation. The recursion AIRs (Merkle paths, Fiat-Shamir) will
//! consume the same bus instead.
//!
//! The other four lanes carry an all-zero trace and only trivial constraints: the permutation
//! is native to KoalaBear only.

use crate::poseidon2::{external_linear_ch, internal_linear_ch, params_ch, FULL_ROUNDS, PARTIAL_ROUNDS, SBOX_DEGREE, WIDTH};
use crate::stark::{Air, BusTerm, Challenges, Point};
use crate::{add_mod, mul_mod_channel, sub_mod, Extension4, RNS_MODULI};

pub const LANE: usize = 1; // KoalaBear
const SBOXES: usize = FULL_ROUNDS * WIDTH + PARTIAL_ROUNDS;
/// Columns (and constraints) per S-box: enough for x^7 = ((s^2 * s)^2) * s in degree-2 steps.
pub const PER_SBOX: usize = 4;
pub const COLS: usize = 1 + WIDTH + PER_SBOX * SBOXES;
pub const NUM_CONSTRAINTS: usize = 1 + PER_SBOX * SBOXES;
const TAG: u32 = 3;

/// Columns used by one permutation's S-boxes.
pub const SBOX_COLS: usize = PER_SBOX * SBOXES;
/// Constraints of one permutation.
pub const PERM_CONSTRAINTS: usize = PER_SBOX * SBOXES;

/// Runs the permutation on `input` with its S-box columns at `cols[base..base + SBOX_COLS]`,
/// either filling them (`fill`) or reading them and pushing the constraint values; returns the
/// output state.
pub(crate) fn run_at(input: &[u32; WIDTH], cols: &mut [u32], base: usize, fill: bool, out: Option<&mut Vec<u32>>) -> [u32; WIDTH] {
    run_at_ch(input, cols, base, fill, out, LANE)
}

/// Same, in channel `ch` (S-box x^d with d = SBOX_DEGREE[ch]). Each S-box has 4 columns c0..c3:
///   d = 3: c0 = s^2, c1 = c0 s (output), c2 = c3 = 0
///   d = 5: c0 = s^2, c1 = c0^2, c2 = c1 s (output), c3 = 0
///   d = 7: c0 = s^2, c1 = c0 s, c2 = c1^2, c3 = c2 s (output)
pub fn run_at_ch(input: &[u32; WIDTH], cols: &mut [u32], base: usize, fill: bool, out: Option<&mut Vec<u32>>, ch: usize) -> [u32; WIDTH] {
    let m = RNS_MODULI[ch];
    let d = SBOX_DEGREE[ch];
    let prm = params_ch(ch);
    let mut out = out;
    let mut k = 0usize;
    let mul = |a: u32, b: u32| mul_mod_channel(a, b, ch);
    let mut sbox = |s: u32, cols: &mut [u32]| -> u32 {
        let c = base + PER_SBOX * k;
        k += 1;
        // expected value of each column given the previous ones (as committed)
        let expect = |cols: &[u32], j: usize| -> u32 {
            match (d, j) {
                (_, 0) => mul(s, s),
                (3, 1) => mul(cols[c], s),
                (5, 1) => mul(cols[c], cols[c]),
                (5, 2) => mul(cols[c + 1], s),
                (7, 1) => mul(cols[c], s),
                (7, 2) => mul(cols[c + 1], cols[c + 1]),
                (7, 3) => mul(cols[c + 2], s),
                _ => 0,
            }
        };
        for j in 0..PER_SBOX {
            if fill {
                cols[c + j] = expect(cols, j);
            }
            if let Some(o) = out.as_deref_mut() {
                o.push(sub_mod(cols[c + j], expect(cols, j), m));
            }
        }
        cols[c + (d as usize - 1) / 2]
    };
    let mut st = *input;
    external_linear_ch(&mut st, ch);
    for r in 0..FULL_ROUNDS {
        if r == FULL_ROUNDS / 2 {
            for pr in 0..PARTIAL_ROUNDS {
                st[0] = sbox(add_mod(st[0], prm.partial_rc[pr], m), cols);
                internal_linear_ch(&mut st, &prm.diag, ch);
            }
        }
        for i in 0..WIDTH {
            st[i] = sbox(add_mod(st[i], prm.full_rc[r][i], m), cols);
        }
        external_linear_ch(&mut st, ch);
    }
    st
}

fn run(input: &[u32; WIDTH], cols: &mut [u32], fill: bool, out: Option<&mut Vec<u32>>) -> [u32; WIDTH] {
    run_at(input, cols, 1 + WIDTH, fill, out)
}

/// Trace row for one permutation.
pub fn row(input: &[u32; WIDTH], active: bool) -> Vec<u32> {
    let mut cols = vec![0u32; COLS];
    cols[0] = active as u32;
    cols[1..1 + WIDTH].copy_from_slice(input);
    run(input, &mut cols, true, None);
    cols
}

pub struct Poseidon2Air {
    /// Public (input, output) pairs proven by the KoalaBear lane.
    pub public: Vec<([u32; WIDTH], [u32; WIDTH])>,
}

impl Poseidon2Air {
    fn fingerprint(c: &Challenges, input: &[u32], output: &[u32]) -> Extension4 {
        let v: Vec<u32> = input.iter().chain(output).copied().collect();
        c.fingerprint(TAG, &v, LANE)
    }

    /// Traces for all 5 lanes (2^log_rows rows each).
    pub fn traces(&self, log_rows: u32) -> [Vec<Vec<u32>>; crate::DEFAULT_RNS_CHANNELS] {
        let n = 1usize << log_rows;
        assert!(self.public.len() <= n);
        std::array::from_fn(|ch| {
            if ch != LANE {
                return vec![vec![0u32; COLS]; n];
            }
            (0..n).map(|r| match self.public.get(r) {
                Some((inp, _)) => row(inp, true),
                None => row(&[0; WIDTH], false),
            }).collect()
        })
    }
}

impl Air for Poseidon2Air {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"poseidon2-koalabear-16-v1".to_vec();
        for (i, o) in &self.public {
            for x in i.iter().chain(o) {
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
    fn eval(&self, cur: &[u32], _next: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        if ch != LANE {
            out.extend(std::iter::repeat_n(0, NUM_CONSTRAINTS));
            return;
        }
        let m = RNS_MODULI[ch];
        out.push(mul_mod_channel(cur[0], sub_mod(cur[0], 1, m), ch));
        let input: [u32; WIDTH] = cur[1..1 + WIDTH].try_into().unwrap();
        let mut cols = cur.to_vec();
        run(&input, &mut cols, false, Some(out));
    }
    fn num_bus(&self) -> usize {
        1
    }
    fn bus(&self, cur: &[u32], c: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        if ch != LANE {
            out.push(BusTerm { den: c.beta, weight: 0 });
            return;
        }
        let input: [u32; WIDTH] = cur[1..1 + WIDTH].try_into().unwrap();
        let mut cols = cur.to_vec();
        let output = run(&input, &mut cols, false, None);
        out.push(BusTerm { den: Self::fingerprint(c, &input, &output), weight: sub_mod(0, cur[0], RNS_MODULI[ch]) });
    }
    fn bus_sum(&self, c: &Challenges, ch: usize) -> Extension4 {
        if ch != LANE {
            return Extension4::ZERO;
        }
        let dens: Vec<Extension4> = self.public.iter().map(|(i, o)| Self::fingerprint(c, i, o)).collect();
        match crate::logup::batch_inverse_ext4(&dens, ch) {
            Some(inv) => inv.iter().fold(Extension4::ZERO, |a, x| a.sub(x, ch)),
            None => Extension4::ONE,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::permute;
    use crate::stark::{prove_air, verify_air, StarkParams};
    use crate::transcript::Transcript;

    const P: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };

    fn pairs(n: usize) -> Vec<([u32; WIDTH], [u32; WIDTH])> {
        (0..n)
            .map(|k| {
                let inp: [u32; WIDTH] = std::array::from_fn(|i| (k * 31 + i * 7) as u32 * 2654435761 % crate::poseidon2::P);
                let mut out = inp;
                permute(&mut out);
                (inp, out)
            })
            .collect()
    }

    #[test]
    fn row_reproduces_the_native_permutation() {
        for (inp, out) in pairs(5) {
            let r = row(&inp, true);
            let mut cols = r.clone();
            let mut cons = Vec::new();
            assert_eq!(run(&inp, &mut cols, false, Some(&mut cons)), out);
            assert!(cons.iter().all(|&x| x == 0));
        }
    }

    #[test]
    fn columns_reproduce_the_permutation_in_every_channel() {
        for ch in 0..crate::DEFAULT_RNS_CHANNELS {
            let inp: [u32; WIDTH] = std::array::from_fn(|i| (i as u32 + 1) * 1_000_003 % RNS_MODULI[ch]);
            let mut want = inp;
            crate::poseidon2::permute_ch(&mut want, ch);
            let mut cols = vec![0u32; COLS];
            assert_eq!(run_at_ch(&inp, &mut cols, 1 + WIDTH, true, None, ch), want, "channel {ch}");
            let mut cons = Vec::new();
            run_at_ch(&inp, &mut cols.clone(), 1 + WIDTH, false, Some(&mut cons), ch);
            assert!(cons.iter().all(|&x| x == 0));
            assert_eq!(cons.len(), PERM_CONSTRAINTS);
            cols[1 + WIDTH + 4 * 7 + 1] ^= 1;
            let mut cons = Vec::new();
            run_at_ch(&inp, &mut cols, 1 + WIDTH, false, Some(&mut cons), ch);
            assert!(cons.iter().any(|&x| x != 0), "channel {ch}: forged S-box column accepted");
        }
    }

    #[test]
    fn honest_permutations_verify_and_forgeries_fail() {
        let air = Poseidon2Air { public: pairs(100) };
        let traces = air.traces(P.log_rows);
        let proof = prove_air(&air, &traces, 100, &P, &mut Transcript::new(b"p2"));
        assert!(verify_air(&air, &proof, 1 << P.log_rows, &P, &mut Transcript::new(b"p2")));

        // Claim a wrong output for one pair: the honest trace does not match the public list.
        let mut bad = Poseidon2Air { public: pairs(100) };
        bad.public[42].1[3] ^= 1;
        let proof = prove_air(&bad, &traces, 100, &P, &mut Transcript::new(b"p2"));
        assert!(!verify_air(&bad, &proof, 1 << P.log_rows, &P, &mut Transcript::new(b"p2")));

        // Forge an S-box column so the row "computes" the wrong output.
        let mut forged = traces.clone();
        forged[LANE][42][1 + WIDTH + 1] ^= 1;
        let proof = prove_air(&bad, &forged, 100, &P, &mut Transcript::new(b"p2"));
        assert!(!verify_air(&bad, &proof, 1 << P.log_rows, &P, &mut Transcript::new(b"p2")));
    }
}
