//! AIR for Merkle path verification with Poseidon2-KoalaBear (docs/REKURSIONI.md, R4).
//!
//! Tree: leaves and nodes are 8-word digests; parent = compress(left, right) from `poseidon2`.
//! One row = one level of one path: from (path id, level, digest, index) it computes the
//! parent and passes (path id, level + 1, parent, index >> 1) on to the next level.
//!
//! The rows are linked by a LogUp bus instead of by position: each active row consumes the
//! token of its child and produces the token of its parent, so the row terms sum to
//! (initial tokens) - (final tokens). The verifier adds exactly that from the public claims
//! (path id, leaf, index, root): every claim must then be closed by a chain of rows from its
//! leaf (level 0, index i) to its root (level `depth`, index 0). Levels only go up, so there
//! are no cycles; the path id keeps different paths apart; bits are boolean and the final
//! index must be 0, so the bits are exactly the binary digits of i (i < 2^depth).
//!
//! Columns: active, pid, level, idx_next, bit, cur[8], sib[8], left[8], right[8],
//! then the S-box columns of one permutation on left || right.
//! Constraints (degree 2): active and bit boolean; left = cur + bit (sib - cur);
//! right = sib + bit (cur - sib); the permutation's S-boxes.
//! parent = perm(left || right)[0..8] + left (feed-forward).

use crate::poseidon2::{compress, compress_ch, WIDTH};
use crate::poseidon2_air::{run_at_ch, PERM_CONSTRAINTS, SBOX_COLS};
use crate::stark::{Air, BusTerm, Challenges, Point};
use crate::{add_mod, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

pub const LANE: usize = crate::poseidon2_air::LANE;
pub type Digest = [u32; 8];

const ACTIVE: usize = 0;
const PID: usize = 1;
const LEVEL: usize = 2;
const IDX_NEXT: usize = 3;
const BIT: usize = 4;
const CUR: usize = 5;
const SIB: usize = 13;
const LEFT: usize = 21;
const RIGHT: usize = 29;
const SBOX: usize = 37;
pub const COLS: usize = SBOX + SBOX_COLS;
pub const NUM_CONSTRAINTS: usize = 2 + 16 + PERM_CONSTRAINTS;
const TAG: u32 = 4;

/// Native Merkle tree over 8-word digests (power-of-two number of leaves).
pub struct Tree {
    levels: Vec<Vec<Digest>>,
}

impl Tree {
    pub fn new(leaves: Vec<Digest>) -> Self {
        Self::new_ch(leaves, LANE)
    }
    /// Tree with Poseidon2 over F_{m_ch}.
    pub fn new_ch(leaves: Vec<Digest>, ch: usize) -> Self {
        assert!(leaves.len().is_power_of_two());
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            levels.push(prev.chunks(2).map(|c| if ch == LANE { compress(&c[0], &c[1]) } else { compress_ch(&c[0], &c[1], ch) }).collect());
        }
        Self { levels }
    }
    pub fn root(&self) -> Digest {
        self.levels.last().unwrap()[0]
    }
    pub fn depth(&self) -> usize {
        self.levels.len() - 1
    }
    pub fn path(&self, mut idx: usize) -> Vec<Digest> {
        let mut out = Vec::new();
        for lvl in &self.levels[..self.depth()] {
            out.push(lvl[idx ^ 1]);
            idx >>= 1;
        }
        out
    }
}

/// A public claim: `leaf` sits at `index` of the tree with `root` and depth `depth`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathClaim {
    pub leaf: Digest,
    pub index: u32,
    pub depth: u32,
    pub root: Digest,
}

pub struct MerkleAir {
    pub claims: Vec<PathClaim>,
    /// The field the tree's Poseidon2 runs in (KoalaBear = `LANE` for the unified path).
    pub lane: usize,
}

fn token(c: &Challenges, pid: u32, level: u32, d: &[u32], idx: u32, ch: usize) -> Extension4 {
    let mut v = vec![pid, level, idx];
    v.extend_from_slice(d);
    c.fingerprint(TAG, &v, ch)
}

/// Fills the permutation columns of a row from cur, sib and bit; returns the parent digest.
fn fill_row(row: &mut [u32], ch: usize) -> Digest {
    let m = RNS_MODULI[ch];
    let bit = row[BIT];
    for i in 0..8 {
        let (c, s) = (row[CUR + i], row[SIB + i]);
        row[LEFT + i] = if bit == 1 { s } else { c };
        row[RIGHT + i] = if bit == 1 { c } else { s };
        debug_assert!(c < m && s < m);
    }
    parent_of(row, true, None, ch)
}

fn parent_of(row: &mut [u32], fill: bool, out: Option<&mut Vec<u32>>, ch: usize) -> Digest {
    let m = RNS_MODULI[ch];
    let input: [u32; WIDTH] = std::array::from_fn(|i| if i < 8 { row[LEFT + i] } else { row[RIGHT + i - 8] });
    let st = run_at_ch(&input, row, SBOX, fill, out, ch);
    std::array::from_fn(|i| add_mod(st[i], row[LEFT + i], m))
}

impl MerkleAir {
    /// Prover: rows for every claim's path (siblings from `paths`), padded to 2^log_rows.
    pub fn traces(&self, paths: &[Vec<Digest>], log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let n = 1usize << log_rows;
        let mut rows = Vec::new();
        for (pid, (cl, path)) in self.claims.iter().zip(paths).enumerate() {
            let mut cur = cl.leaf;
            let mut idx = cl.index;
            for (level, sib) in path.iter().enumerate() {
                let mut r = vec![0u32; COLS];
                r[ACTIVE] = 1;
                r[PID] = pid as u32;
                r[LEVEL] = level as u32;
                r[IDX_NEXT] = idx >> 1;
                r[BIT] = idx & 1;
                r[CUR..CUR + 8].copy_from_slice(&cur);
                r[SIB..SIB + 8].copy_from_slice(sib);
                cur = fill_row(&mut r, self.lane);
                idx >>= 1;
                rows.push(r);
            }
        }
        assert!(rows.len() <= n, "too many path levels for 2^log_rows rows");
        let mut pad = vec![0u32; COLS];
        fill_row(&mut pad, self.lane);
        rows.resize(n, pad);
        std::array::from_fn(|ch| if ch == self.lane { rows.clone() } else { vec![vec![0u32; COLS]; n] })
    }
}

impl Air for MerkleAir {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"merkle-poseidon2-v2".to_vec();
        v.extend_from_slice(&(self.lane as u32).to_le_bytes());
        for c in &self.claims {
            for x in c.leaf.iter().chain(&c.root).chain([&c.index, &c.depth]) {
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
        if ch != self.lane {
            out.extend(std::iter::repeat_n(0, NUM_CONSTRAINTS));
            return;
        }
        let m = RNS_MODULI[ch];
        let mul = |a: u32, b: u32| mul_mod_channel(a, b, ch);
        out.push(mul(c[ACTIVE], sub_mod(c[ACTIVE], 1, m)));
        out.push(mul(c[BIT], sub_mod(c[BIT], 1, m)));
        for i in 0..8 {
            let (cur, sib) = (c[CUR + i], c[SIB + i]);
            out.push(sub_mod(c[LEFT + i], add_mod(cur, mul(c[BIT], sub_mod(sib, cur, m)), m), m));
            out.push(sub_mod(c[RIGHT + i], add_mod(sib, mul(c[BIT], sub_mod(cur, sib, m)), m), m));
        }
        let mut row = c.to_vec();
        parent_of(&mut row, false, Some(out), ch);
    }
    fn num_bus(&self) -> usize {
        2
    }
    fn bus(&self, c: &[u32], ch_c: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        if ch != self.lane {
            out.push(BusTerm { den: ch_c.beta, weight: 0 });
            out.push(BusTerm { den: ch_c.beta, weight: 0 });
            return;
        }
        let m = RNS_MODULI[ch];
        let idx = add_mod(add_mod(c[IDX_NEXT], c[IDX_NEXT], m), c[BIT], m);
        let mut row = c.to_vec();
        let parent = parent_of(&mut row, false, None, ch);
        out.push(BusTerm { den: token(ch_c, c[PID], c[LEVEL], &c[CUR..CUR + 8], idx, ch), weight: c[ACTIVE] });
        out.push(BusTerm { den: token(ch_c, c[PID], add_mod(c[LEVEL], 1, m), &parent, c[IDX_NEXT], ch), weight: sub_mod(0, c[ACTIVE], m) });
    }
    fn bus_sum(&self, ch_c: &Challenges, ch: usize) -> Extension4 {
        if ch != self.lane {
            return Extension4::ZERO;
        }
        let mut dens = Vec::new();
        for (pid, cl) in self.claims.iter().enumerate() {
            dens.push(token(ch_c, pid as u32, 0, &cl.leaf, cl.index, ch));
            dens.push(token(ch_c, pid as u32, cl.depth, &cl.root, 0, ch));
        }
        match crate::logup::batch_inverse_ext4(&dens, ch) {
            Some(inv) => inv.chunks(2).fold(Extension4::ZERO, |a, p| a.add(&p[0], ch).sub(&p[1], ch)),
            None => Extension4::ONE,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::hash;
    use crate::stark::{prove_air, verify_air, StarkParams};
    use crate::transcript::Transcript;

    const P: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };

    fn setup() -> (Tree, Vec<PathClaim>, Vec<Vec<Digest>>) {
        let leaves: Vec<Digest> = (0..64u32).map(|i| hash(&[i, i * i, 7])).collect();
        let tree = Tree::new(leaves.clone());
        let idxs = [0u32, 1, 17, 42, 63, 42];
        let claims = idxs.iter().map(|&i| PathClaim { leaf: leaves[i as usize], index: i, depth: tree.depth() as u32, root: tree.root() }).collect();
        let paths = idxs.iter().map(|&i| tree.path(i as usize)).collect();
        (tree, claims, paths)
    }

    fn run(air: &MerkleAir, traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]) -> bool {
        let proof = prove_air(air, traces, air.claims.len(), &P, &mut Transcript::new(b"merkle"));
        verify_air(air, &proof, usize::MAX, &P, &mut Transcript::new(b"merkle"))
    }

    #[test]
    fn honest_paths_verify() {
        let (_, claims, paths) = setup();
        let air = MerkleAir { claims, lane: LANE };
        assert!(run(&air, &air.traces(&paths, P.log_rows)));
    }

    #[test]
    fn wrong_leaf_root_or_index_is_rejected() {
        let (tree, claims, paths) = setup();
        let honest = MerkleAir { claims: claims.clone(), lane: LANE };
        let traces = honest.traces(&paths, P.log_rows);

        let mut c = claims.clone();
        c[2].leaf[0] ^= 1; // a leaf that is not in the tree
        assert!(!run(&MerkleAir { claims: c, lane: LANE }, &traces));

        let mut c = claims.clone();
        c[3].root = tree.levels[1][0]; // wrong root
        assert!(!run(&MerkleAir { claims: c, lane: LANE }, &traces));

        let mut c = claims.clone();
        c[3].index = 43; // the leaf at 42 claimed at 43
        assert!(!run(&MerkleAir { claims: c, lane: LANE }, &traces));
    }

    #[test]
    fn forged_rows_are_rejected() {
        let (_, claims, paths) = setup();
        let air = MerkleAir { claims, lane: LANE };
        let traces = air.traces(&paths, P.log_rows);
        for (row, col) in [(7, SIB + 2), (7, BIT), (13, LEFT), (20, SBOX + 5), (0, IDX_NEXT), (3, LEVEL), (3, PID)] {
            let mut bad = traces.clone();
            bad[LANE][row][col] = add_mod(bad[LANE][row][col], 1, RNS_MODULI[LANE]);
            assert!(!run(&air, &bad), "row {row} col {col}");
        }
        // A forged leaf with a consistent recomputed path still has to reach the public root.
        let mut c = air.claims.clone();
        c[0].leaf = hash(&[999]);
        let forged = MerkleAir { claims: c, lane: LANE };
        let mut p = paths.clone();
        p[0] = paths[0].clone();
        assert!(!run(&forged, &forged.traces(&p, P.log_rows)));
    }

    #[test]
    fn paths_verify_in_every_lane_field() {
        use crate::hash::HashMode;
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let leaves: Vec<Digest> = (0..32u32).map(|i| crate::poseidon2::hash_ch(&[i, 3 * i + 1], ch)).collect();
            let tree = Tree::new_ch(leaves.clone(), ch);
            let idxs = [0u32, 9, 31];
            let claims: Vec<PathClaim> = idxs.iter().map(|&i| PathClaim { leaf: leaves[i as usize], index: i, depth: tree.depth() as u32, root: tree.root() }).collect();
            let paths: Vec<Vec<Digest>> = idxs.iter().map(|&i| tree.path(i as usize)).collect();
            let air = MerkleAir { claims: claims.clone(), lane: ch };
            let t = || Transcript::with_mode(b"merkle", HashMode::Lane(ch as u8));
            let proof = prove_air(&air, &air.traces(&paths, P.log_rows), 3, &P, &mut t());
            assert!(verify_air(&air, &proof, usize::MAX, &P, &mut t()), "lane {ch}");
            let mut c = claims;
            c[1].leaf[2] ^= 1;
            let bad = MerkleAir { claims: c, lane: ch };
            let proof = prove_air(&bad, &air.traces(&paths, P.log_rows), 3, &P, &mut t());
            assert!(!verify_air(&bad, &proof, usize::MAX, &P, &mut t()), "lane {ch}: wrong leaf accepted");
        }
    }
}
