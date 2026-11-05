//! Several AIRs in one proof (docs/REKURSIONI.md, R7.1).
//!
//! The recursive verifier is made of tables of different kinds (Poseidon2 permutations, Merkle
//! levels, the transcript sponge, FRI folds, composition rows). `Stacked` puts them side by side
//! in one trace: row r holds row r of every table (each table padded to the common height), the
//! constraints are the union, and all bus terms go into the one LogUp running sum.
//!
//! That is what links the tables: a tuple sent by one table (weight -1) and received by another
//! (weight +1) cancels in the sum, so neither the tuple nor its value has to be public. The
//! public bus sum of the stack is the sum of the tables' own public parts.
//!
//! Byte-checked columns of every table are moved to the front (the engine range-checks the
//! first `byte_cols` columns); `eval` gathers each table's row back into its own order.
//! Bus tags must be distinct across tables (see the TAG constants of each AIR).

use crate::stark::{Air, BusTerm, BusTuple, Challenges, Point};
use crate::{Extension4, DEFAULT_RNS_CHANNELS};

pub struct Stacked<'a> {
    pub tables: Vec<&'a dyn Air>,
    /// For each table: stacked column of each of its columns.
    map: Vec<Vec<usize>>,
    width: usize,
    bytes: usize,
}

impl<'a> Stacked<'a> {
    pub fn new(tables: Vec<&'a dyn Air>) -> Self {
        let bytes: usize = tables.iter().map(|t| t.byte_cols()).sum();
        let (mut b, mut r) = (0usize, bytes);
        let map = tables
            .iter()
            .map(|t| {
                let mut m: Vec<usize> = (b..b + t.byte_cols()).collect();
                b += t.byte_cols();
                let rest = t.width() - t.byte_cols();
                m.extend(r..r + rest);
                r += rest;
                m
            })
            .collect();
        Self { tables, map, width: r, bytes }
    }

    fn gather(&self, k: usize, row: &[u32]) -> Vec<u32> {
        self.map[k].iter().map(|&c| row[c]).collect()
    }

    /// Stacks per-table traces (each [lane][row][col]) into one; shorter tables are padded with
    /// their own last row, which therefore must be an inactive (padding) row.
    pub fn traces(&self, parts: &[[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]], log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        assert_eq!(parts.len(), self.tables.len());
        let n = 1usize << log_rows;
        std::array::from_fn(|ch| {
            if parts.iter().all(|p| p[ch].is_empty()) {
                return Vec::new();
            }
            (0..n)
                .map(|r| {
                    let mut row = vec![0u32; self.width];
                    for (k, p) in parts.iter().enumerate() {
                        let t = &p[ch];
                        assert!(t.len() <= n, "table {k} is taller than the stack");
                        let src = t.get(r).or(t.last()).expect("empty table trace");
                        for (c, &dst) in self.map[k].iter().enumerate() {
                            row[dst] = src[c];
                        }
                    }
                    row
                })
                .collect()
        })
    }
}

impl Air for Stacked<'_> {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"stacked-v1".to_vec();
        for t in &self.tables {
            let s = t.statement();
            v.extend_from_slice(&(s.len() as u64).to_le_bytes());
            v.extend(s);
        }
        v
    }
    fn width(&self) -> usize {
        self.width
    }
    fn byte_cols(&self) -> usize {
        self.bytes
    }
    fn num_constraints(&self) -> usize {
        self.tables.iter().map(|t| t.num_constraints()).sum()
    }
    fn eval(&self, cur: &[u32], next: &[u32], pt: &Point, ch: usize, out: &mut Vec<u32>) {
        for (k, t) in self.tables.iter().enumerate() {
            t.eval(&self.gather(k, cur), &self.gather(k, next), pt, ch, out);
        }
    }
    fn num_bus(&self) -> usize {
        self.tables.iter().map(|t| t.num_bus()).sum()
    }
    fn bus(&self, cur: &[u32], c: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        for (k, t) in self.tables.iter().enumerate() {
            t.bus(&self.gather(k, cur), c, ch, out);
        }
    }
    fn bus_tuples(&self, cur: &[u32], ch: usize, out: &mut Vec<BusTuple>) {
        for (k, t) in self.tables.iter().enumerate() {
            t.bus_tuples(&self.gather(k, cur), ch, out);
        }
    }
    fn bus_sum(&self, c: &Challenges, ch: usize) -> Extension4 {
        self.tables.iter().fold(Extension4::ZERO, |a, t| a.add(&t.bus_sum(c, ch), ch))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::HashMode;
    use crate::stark::{prove_air, verify_air, StarkParams};
    use crate::transcript::Transcript;
    use crate::{mul_mod_channel, sub_mod, RNS_MODULI};

    const P: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };
    const LINK: u32 = 100;

    /// Toy producer: column 1 is 0..k (as bytes, range-checked), it sends (v, v^2) with
    /// v^2 in column 2 when active. Nothing public: its tuples must be consumed by `Consumer`.
    struct Producer;
    impl Air for Producer {
        fn statement(&self) -> Vec<u8> {
            b"producer".to_vec()
        }
        fn width(&self) -> usize {
            3
        }
        fn byte_cols(&self) -> usize {
            1
        }
        fn num_constraints(&self) -> usize {
            2
        }
        fn eval(&self, c: &[u32], _n: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
            let m = RNS_MODULI[ch];
            out.push(mul_mod_channel(c[1], sub_mod(c[1], 1, m), ch)); // active flag boolean
            out.push(sub_mod(c[2], mul_mod_channel(c[0], c[0], ch), m)); // square
        }
        fn num_bus(&self) -> usize {
            1
        }
        fn bus(&self, c: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
            out.push(BusTerm { den: cc.fingerprint(LINK, &[c[0], c[2]], ch), weight: sub_mod(0, c[1], RNS_MODULI[ch]) });
        }
    }

    /// Toy consumer: receives (v, s) pairs from the link; publishes nothing either.
    struct Consumer;
    impl Air for Consumer {
        fn statement(&self) -> Vec<u8> {
            b"consumer".to_vec()
        }
        fn width(&self) -> usize {
            3
        }
        fn byte_cols(&self) -> usize {
            0
        }
        fn num_constraints(&self) -> usize {
            1
        }
        fn eval(&self, c: &[u32], _n: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
            out.push(mul_mod_channel(c[0], sub_mod(c[0], 1, RNS_MODULI[ch]), ch));
        }
        fn num_bus(&self) -> usize {
            1
        }
        fn bus(&self, c: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
            out.push(BusTerm { den: cc.fingerprint(LINK, &[c[1], c[2]], ch), weight: c[0] % RNS_MODULI[ch] });
        }
    }

    fn parts(lane: usize, rows: usize, bad: Option<usize>) -> Vec<[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]> {
        let n = 1usize << P.log_rows;
        let prod: Vec<Vec<u32>> = (0..n).map(|r| if r < rows { vec![r as u32 % 256, 1, (r % 256 * (r % 256)) as u32] } else { vec![0, 0, 0] }).collect();
        // the consumer holds the same pairs in another order and in fewer rows (padded)
        let mut cons: Vec<Vec<u32>> = (0..rows).rev().map(|r| vec![1, r as u32 % 256, (r % 256 * (r % 256)) as u32]).collect();
        if let Some(i) = bad {
            cons[i][2] += 1;
        }
        cons.push(vec![0, 0, 0]);
        let one = |t: Vec<Vec<u32>>| -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] { std::array::from_fn(|c| if c == lane { t.clone() } else { Vec::new() }) };
        vec![one(prod), one(cons)]
    }

    #[test]
    fn linked_tables_verify_without_public_tuples() {
        let (p, c) = (Producer, Consumer);
        let stack = Stacked::new(vec![&p, &c]);
        assert_eq!(stack.byte_cols(), 1);
        for lane in 0..DEFAULT_RNS_CHANNELS {
            let t = || Transcript::with_mode(b"stack", HashMode::Lane(lane as u8));
            let traces = stack.traces(&parts(lane, 200, None), P.log_rows);
            let proof = prove_air(&stack, &traces, 200, &P, &mut t());
            assert!(verify_air(&stack, &proof, 256, &P, &mut t()), "lane {lane}");
        }
    }

    #[test]
    fn a_tuple_the_other_table_does_not_send_is_rejected() {
        let (p, c) = (Producer, Consumer);
        let stack = Stacked::new(vec![&p, &c]);
        let lane = 2;
        let t = || Transcript::with_mode(b"stack", HashMode::Lane(lane as u8));
        let traces = stack.traces(&parts(lane, 200, Some(17)), P.log_rows);
        let proof = prove_air(&stack, &traces, 200, &P, &mut t());
        assert!(!verify_air(&stack, &proof, 256, &P, &mut t()));
        // and a consumer alone (nothing produced) cannot balance either
        let alone = Stacked::new(vec![&c]);
        let traces = alone.traces(&parts(lane, 200, None)[1..], P.log_rows);
        let proof = prove_air(&alone, &traces, 200, &P, &mut t());
        assert!(!verify_air(&alone, &proof, 256, &P, &mut t()));
    }
}
