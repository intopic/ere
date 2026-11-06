//! Small tables that connect the commitments to the transcript in the recursion stack (R7.2d).
//!
//! - `PidRootAir`, one row per Merkle path: takes the path's top token from `merkle_air`
//!   (pid, depth, 0, root) and re-emits it as (tree, root). Public per row: (pid, depth, tree).
//! - `TreeRootAir`, one row per committed tree: takes (tree, root) once per path of that tree
//!   (multiplicity public) and writes the 8 root words into the transcript blocks at their
//!   (permutation, position): the words that `absorb_digest` absorbed.
//! - `FinalAir`, one row: the constant final FRI layer value. It is read by the last fold row of
//!   every query and written into the transcript at the positions of the absorbed final layer.
//!
//! So every root a Merkle path ends in, and the final layer, is what the transcript absorbed
//! before drawing the next challenges; none of them is public.

use crate::merkle_air::{token_values, TAG_PATH};
use crate::stark::{Air, BusTerm, Challenges, Point};
use crate::transcript_air::{block_word, TAG_BLOCK_WORD};
use crate::{mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

/// (tree, root[8]) of a finished Merkle path.
pub const TAG_ROOT: u32 = 24;
/// The final FRI layer value (4 words).
pub const TAG_FIN: u32 = 25;
const TAG_PID: u32 = 26;
const TAG_TREE: u32 = 27;
const TAG_FINAL_ROW: u32 = 28;

fn sum_inverses(dens: &[Extension4], ch: usize, sign_plus: bool) -> Extension4 {
    match crate::logup::batch_inverse_ext4(dens, ch) {
        Some(inv) => inv.iter().fold(Extension4::ZERO, |a, x| if sign_plus { a.add(x, ch) } else { a.sub(x, ch) }),
        None => Extension4::ONE,
    }
}

fn one_lane(rows: Vec<Vec<u32>>, lane: usize, log_rows: u32, width: usize) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
    let n = 1usize << log_rows;
    assert!(rows.len() <= n);
    let mut rows = rows;
    rows.resize(n, vec![0u32; width]);
    std::array::from_fn(|c| if c == lane { rows.clone() } else { Vec::new() })
}

fn bool_act(c: &[u32], ch: usize, out: &mut Vec<u32>) {
    out.push(mul_mod_channel(c[0], sub_mod(c[0], 1, RNS_MODULI[ch]), ch));
}

// ---- per path ---------------------------------------------------------------------------------

/// (pid, depth, tree) of every path.
pub struct PidRootAir {
    pub paths: Vec<(u32, u32, u32)>,
}

const P_COLS: usize = 4 + 8; // act, pid, depth, tree, root

impl PidRootAir {
    pub fn traces(&self, roots: &[[u32; 8]], lane: usize, log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let rows = self
            .paths
            .iter()
            .zip(roots)
            .map(|(&(pid, depth, tree), root)| {
                let mut r = vec![1, pid, depth, tree];
                r.extend_from_slice(root);
                r
            })
            .collect();
        one_lane(rows, lane, log_rows, P_COLS)
    }
}

impl Air for PidRootAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"pid-root-v1".to_vec();
        v.extend(self.paths.iter().flat_map(|&(a, b, c)| [a, b, c]).flat_map(|x| x.to_le_bytes()));
        v
    }
    fn width(&self) -> usize {
        P_COLS
    }
    fn byte_cols(&self) -> usize {
        0
    }
    fn num_constraints(&self) -> usize {
        1
    }
    fn eval(&self, c: &[u32], _n: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        bool_act(c, ch, out);
    }
    fn num_bus(&self) -> usize {
        3
    }
    fn bus(&self, c: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        let neg = sub_mod(0, c[0], RNS_MODULI[ch]);
        let mut root = vec![c[3]];
        root.extend_from_slice(&c[4..12]);
        out.push(BusTerm { den: cc.fingerprint(TAG_PATH, &token_values(c[1], c[2], 0, &c[4..12]), ch), weight: c[0] });
        out.push(BusTerm { den: cc.fingerprint(TAG_ROOT, &root, ch), weight: neg });
        out.push(BusTerm { den: cc.fingerprint(TAG_PID, &c[1..4], ch), weight: neg });
    }
    fn bus_sum(&self, cc: &Challenges, ch: usize) -> Extension4 {
        let dens: Vec<Extension4> = self.paths.iter().map(|&(a, b, c)| cc.fingerprint(TAG_PID, &[a, b, c], ch)).collect();
        sum_inverses(&dens, ch, false)
    }
}

// ---- per tree ---------------------------------------------------------------------------------

/// A committed tree: id, number of paths into it, transcript position of each root word.
#[derive(Clone, Debug)]
pub struct TreeSpec {
    pub tree: u32,
    pub paths: u32,
    pub at: [(u32, u32); 8],
}

pub struct TreeRootAir {
    pub trees: Vec<TreeSpec>,
}

const T_COLS: usize = 3 + 8 + 16; // act, tree, mult, root, (k, p) x 8

impl TreeRootAir {
    pub fn traces(&self, roots: &[[u32; 8]], lane: usize, log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let rows = self
            .trees
            .iter()
            .zip(roots)
            .map(|(t, root)| {
                let mut r = vec![1, t.tree, t.paths];
                r.extend_from_slice(root);
                r.extend(t.at.iter().flat_map(|&(k, p)| [k, p]));
                r
            })
            .collect();
        one_lane(rows, lane, log_rows, T_COLS)
    }
    fn public(t: &TreeSpec) -> Vec<u32> {
        let mut v = vec![t.tree, t.paths];
        v.extend(t.at.iter().flat_map(|&(k, p)| [k, p]));
        v
    }
}

impl Air for TreeRootAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"tree-root-v1".to_vec();
        v.extend(self.trees.iter().flat_map(Self::public).flat_map(|x| x.to_le_bytes()));
        v
    }
    fn width(&self) -> usize {
        T_COLS
    }
    fn byte_cols(&self) -> usize {
        0
    }
    fn num_constraints(&self) -> usize {
        2
    }
    fn eval(&self, c: &[u32], _n: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        bool_act(c, ch, out);
        // a padding row must not absorb root tokens
        out.push(mul_mod_channel(c[2], sub_mod(1, c[0], RNS_MODULI[ch]), ch));
    }
    fn num_bus(&self) -> usize {
        2 + 8
    }
    fn bus(&self, c: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        let neg = sub_mod(0, c[0], RNS_MODULI[ch]);
        let mut root = vec![c[1]];
        root.extend_from_slice(&c[3..11]);
        out.push(BusTerm { den: cc.fingerprint(TAG_ROOT, &root, ch), weight: c[2] });
        let mut public = vec![c[1], c[2]];
        public.extend_from_slice(&c[11..27]);
        out.push(BusTerm { den: cc.fingerprint(TAG_TREE, &public, ch), weight: neg });
        for i in 0..8 {
            out.push(BusTerm { den: cc.fingerprint(TAG_BLOCK_WORD, &block_word(c[11 + 2 * i], c[12 + 2 * i], c[3 + i]), ch), weight: neg });
        }
    }
    fn bus_sum(&self, cc: &Challenges, ch: usize) -> Extension4 {
        let dens: Vec<Extension4> = self.trees.iter().map(|t| cc.fingerprint(TAG_TREE, &Self::public(t), ch)).collect();
        sum_inverses(&dens, ch, false)
    }
}

// ---- final FRI layer --------------------------------------------------------------------------

/// The final layer: read by `queries` fold rows, absorbed as words at `at` (4 per element,
/// `blowup` elements, all equal: the verifier's "constant" check).
pub struct FinalAir {
    pub queries: u32,
    pub at: Vec<(u32, u32)>,
}

impl FinalAir {
    fn width(&self) -> usize {
        1 + 4
    }
    pub fn traces(&self, value: &Extension4, lane: usize, log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let mut r = vec![1];
        r.extend(value.c);
        one_lane(vec![r], lane, log_rows, Air::width(self))
    }
}

impl Air for FinalAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"fri-final-v1".to_vec();
        v.extend_from_slice(&self.queries.to_le_bytes());
        v.extend(self.at.iter().flat_map(|&(k, p)| [k, p]).flat_map(|x| x.to_le_bytes()));
        v
    }
    fn width(&self) -> usize {
        FinalAir::width(self)
    }
    fn byte_cols(&self) -> usize {
        0
    }
    fn num_constraints(&self) -> usize {
        1
    }
    fn eval(&self, c: &[u32], _n: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        bool_act(c, ch, out);
    }
    fn num_bus(&self) -> usize {
        2 + self.at.len()
    }
    fn bus(&self, c: &[u32], cc: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        let m = RNS_MODULI[ch];
        let neg = sub_mod(0, c[0], m);
        out.push(BusTerm { den: cc.fingerprint(TAG_FIN, &c[1..5], ch), weight: sub_mod(0, mul_mod_channel(c[0], self.queries % m, ch), m) });
        out.push(BusTerm { den: cc.fingerprint(TAG_FINAL_ROW, &[], ch), weight: neg });
        for (i, &(k, p)) in self.at.iter().enumerate() {
            out.push(BusTerm { den: cc.fingerprint(TAG_BLOCK_WORD, &block_word(k, p, c[1 + i % 4]), ch), weight: neg });
        }
    }
    fn bus_sum(&self, cc: &Challenges, ch: usize) -> Extension4 {
        sum_inverses(&[cc.fingerprint(TAG_FINAL_ROW, &[], ch)], ch, false)
    }
}
