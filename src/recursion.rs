//! The recursive verifier of one lane, assembled from the recursion AIRs (docs/REKURSIONI.md, R7).
//!
//! Built up step by step; each step replaces a public claim with a link to another table of the
//! same stack:
//!   - R7.2a: composition rows -> FRI fold rows. The layer-0 values FRI folds are the f(x) the
//!     composition AIR recomputed from the opened values (bus `fri_air::LINK_LAYER0`).
//!   - R7.2b: composition rows -> leaf hashes -> Merkle paths. Every opened value is hashed into
//!     its leaf and the leaf is authenticated against the committed root (main, aux, quotient
//!     trees, at x and at the next row's point). Only the roots and positions stay public.
//!   - R7.2c: FRI fold rows -> leaf hashes -> Merkle paths: every pair FRI folds is authenticated
//!     against its layer root.

use crate::composition_air::{self, CompositionAir};
use crate::fri_air::FriFoldAir;
use crate::hash::hash_to_words;
use crate::leaf_air::{LeafHashAir, LeafSpec};
use crate::merkle_air::{Digest, MerkleAir, PathClaim};
use crate::multi_air::Stacked;
use crate::stark::{shift, Air, StarkParams, StarkProof, StarkView};
use crate::{Extension4, DEFAULT_RNS_CHANNELS};

/// Witness of the FRI fold table: pairs[q][l] of lane `j`.
pub fn fold_pairs(proof: &StarkProof, j: usize) -> Vec<Vec<[Extension4; 2]>> {
    proof.fri.queries.iter().map(|q| q.iter().map(|o| o.pair[j]).collect()).collect()
}

/// FRI fold claim of lane `j` of an inner per-lane proof.
pub fn fold_air(proof: &StarkProof, view: &StarkView, params: &StarkParams, j: usize) -> FriFoldAir {
    FriFoldAir {
        lane: j,
        shift: shift(j),
        log_n: params.log_rows + params.log_blowup,
        alphas: view.fri_alphas.iter().map(|a| a[j]).collect(),
        indices: view.indices.clone(),
        final_value: proof.fri.final_layer[j][0],
        link_layer0: true,
        link_leaves: true,
        leaf_base: 0,
    }
}

/// The lane's verifier tables, linked: composition, FRI fold, leaf hashes, Merkle paths.
pub struct LaneAlgebra<'a, A: Air> {
    pub composition: CompositionAir<'a, A>,
    pub fold: FriFoldAir,
    pub leaves: LeafHashAir,
    pub merkle: MerkleAir,
    pub opened: Vec<composition_air::OpenedRow>,
    pub pairs: Vec<Vec<[Extension4; 2]>>,
    pub leaf_words: Vec<Vec<u32>>,
    pub paths: Vec<Vec<Digest>>,
}

impl<'a, A: Air> LaneAlgebra<'a, A> {
    pub fn new(inner: &'a A, proof: &StarkProof, view: &StarkView, params: StarkParams) -> Self {
        let (mut composition, opened) = composition_air::from_proof(inner, proof, view, params);
        composition.link_fri = true;
        composition.link_leaves = true;
        let j = composition.lane;
        let n = 1usize << (params.log_rows + params.log_blowup);
        let blowup = 1usize << params.log_blowup;
        let depth = (params.log_rows + params.log_blowup) as u32;
        let roots: [Digest; 3] = [hash_to_words(&proof.main_root), hash_to_words(&proof.aux_root), hash_to_words(&proof.q_root)];
        let lens = composition.leaf_lens();
        let (mut specs, mut words, mut claims, mut paths) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        for (r, (claim, o)) in composition.claims.iter().zip(&opened).enumerate() {
            let next = (claim.pos + blowup) % n;
            let opens = &proof.openings[claim.q];
            let lw = composition.leaf_words(o);
            for kind in 0..composition_air::LEAVES_PER_ROW {
                let lid = composition_air::leaf_id(r, kind) as u32;
                let (index, opening) = if kind < 3 { (claim.pos, &opens[claim.slot]) } else { (next, &opens[claim.slot + 2]) };
                let path = match kind % 3 {
                    0 => &opening.main_path,
                    1 => &opening.aux_path,
                    _ => &opening.q_path,
                };
                assert_eq!(lw[kind].len(), lens[kind]);
                specs.push(LeafSpec { lid, index: index as u32, len: lens[kind] });
                claims.push(PathClaim { leaf: crate::poseidon2::hash_ch(&lw[kind], j), index: index as u32, depth, root: roots[kind % 3] });
                paths.push(path.iter().map(hash_to_words).collect());
                words.push(lw[kind].clone());
            }
        }
        // FRI layer trees: the fold rows send their pairs as leaves
        let mut fold = fold_air(proof, view, &params, j);
        fold.leaf_base = specs.len() as u32;
        let pairs = fold_pairs(proof, j);
        let rounds = fold.alphas.len();
        for (q, &i) in view.indices.iter().enumerate() {
            for l in 0..rounds {
                let half = n >> (l + 1);
                let lid = fold.leaf_base + (q * rounds + l) as u32;
                let pw: Vec<u32> = pairs[q][l].iter().flat_map(|e| e.c).collect();
                let w = fold.leaf_words(&pw, j);
                specs.push(LeafSpec { lid, index: (i % half) as u32, len: w.len() });
                claims.push(PathClaim { leaf: crate::poseidon2::hash_ch(&w, j), index: (i % half) as u32, depth: half.trailing_zeros(), root: hash_to_words(&proof.fri.layer_roots[l]) });
                paths.push(proof.fri.queries[q][l].path.iter().map(hash_to_words).collect());
                words.push(w);
            }
        }
        Self {
            fold,
            pairs,
            leaves: LeafHashAir { lane: j, leaves: specs, public_words: None, public_digests: None },
            merkle: MerkleAir { claims, lane: j, link_leaves: true },
            composition,
            opened,
            leaf_words: words,
            paths,
        }
    }

    pub fn stack(&self) -> Stacked<'_> {
        Stacked::new(vec![&self.composition, &self.fold, &self.leaves, &self.merkle])
    }

    /// Smallest stack height that fits every table.
    pub fn log_rows(&self) -> u32 {
        let merkle_rows: usize = self.merkle.claims.iter().map(|c| c.depth as usize).sum();
        let need = [self.opened.len() + 1, self.pairs.len() * self.fold.alphas.len() + 1, self.leaves.rows_needed() + 1, merkle_rows + 1, 256];
        need.iter().max().unwrap().next_power_of_two().trailing_zeros()
    }

    pub fn traces(&self, log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let parts = [
            self.composition.traces(&self.opened, log_rows),
            self.fold.traces(&self.pairs, log_rows),
            self.leaves.traces(&self.leaf_words, log_rows),
            self.merkle.traces(&self.paths, log_rows),
        ];
        self.stack().traces(&parts, log_rows)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::HashMode;
    use crate::stark::{prove_air, prove_air_lanes, verify_air, verify_air_view};
    use crate::transcript::Transcript;

    const INNER: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 4 };

    fn state_case() -> (crate::state::StateStatement, [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]) {
        use crate::state::{build, AccountState, Transfer};
        let addrs: Vec<[u8; 20]> = (0..30u8).map(|i| [i; 20]).collect();
        let old: Vec<AccountState> = (0..30).map(|i| AccountState { balance: 500_000 + i as u64, nonce: 0 }).collect();
        let mut nonces = vec![0u32; 30];
        let txs: Vec<Transfer> = (0..90u32)
            .map(|k| {
                let from = (k * 11) % 30;
                let tx = Transfer { from, to: (k * 7 + 3) % 30, amount: 50 + k as u64, nonce: nonces[from as usize] };
                nonces[from as usize] += 1;
                tx
            })
            .collect();
        build(&addrs, &old, &txs, INNER.log_rows, true).unwrap()
    }

    fn outer_ok<A: Air>(alg: &LaneAlgebra<A>) -> bool {
        let p = StarkParams { log_rows: alg.log_rows(), log_blowup: 2, num_queries: 16 };
        let traces = alg.traces(p.log_rows);
        let stack = alg.stack();
        let j = alg.composition.lane;
        let t = || Transcript::with_mode(b"recursion", HashMode::Lane(j as u8));
        let proof = prove_air(&stack, &traces, alg.composition.claims.len(), &p, &mut t());
        verify_air(&stack, &proof, 1 << p.log_rows, &p, &mut t())
    }

    fn lane(j: usize) -> (crate::state::StateStatement, StarkProof, [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]) {
        let (st, traces) = state_case();
        let proof = {
            let inner = crate::state::StateAir { st: &st };
            prove_air(&inner, &traces, st.num_txs(), &INNER, &mut Transcript::with_mode(b"inner", HashMode::Lane(j as u8)))
        };
        (st, proof, traces)
    }

    fn view_of<A: Air>(inner: &A, proof: &StarkProof, j: usize) -> StarkView {
        verify_air_view(inner, proof, 5 << INNER.log_rows, &INNER, &mut Transcript::with_mode(b"inner", HashMode::Lane(j as u8))).unwrap()
    }

    #[test]
    fn linked_verifier_tables_accept_honest_proofs_in_every_lane() {
        let (st, traces) = state_case();
        let inner = crate::state::StateAir { st: &st };
        let proofs = prove_air_lanes(&inner, &traces, st.num_txs(), &INNER, b"inner");
        for j in 0..DEFAULT_RNS_CHANNELS {
            let alg = LaneAlgebra::new(&inner, &proofs[j], &view_of(&inner, &proofs[j], j), INNER);
            let t0 = std::time::Instant::now();
            assert!(outer_ok(&alg), "lane {j}");
            if j == 0 {
                eprintln!("lane verifier stack: 2^{} rows, width {}, prove+verify {:?}", alg.log_rows(), alg.stack().width(), t0.elapsed());
            }
        }
    }

    #[test]
    fn fri_must_fold_the_values_the_composition_checked() {
        let j = 2;
        let (st, proof, _) = lane(j);
        let inner = crate::state::StateAir { st: &st };
        let view = view_of(&inner, &proof, j);
        // Replace query 1's layer-0 pair by another pair that folds to the same value, so the
        // FRI chain alone still holds: f0 += (1 - a/x) c, f1 -= (1 + a/x) c.
        let alg0 = LaneAlgebra::new(&inner, &proof, &view, INNER);
        let x = alg0.fold.traces(&alg0.pairs, 8)[j][alg0.fold.alphas.len()][7]; // X of row (q = 1, l = 0)
        let a_over_x = alg0.fold.alphas[0].mul_scalar(crate::mod_inv_single(x, crate::RNS_MODULI[j]), j);
        let c = Extension4::new(5, 6, 7, 8);
        let mut alg = LaneAlgebra::new(&inner, &proof, &view, INNER);
        alg.pairs[1][0][0] = alg.pairs[1][0][0].add(&Extension4::ONE.sub(&a_over_x, j).mul(&c, j), j);
        alg.pairs[1][0][1] = alg.pairs[1][0][1].sub(&Extension4::ONE.add(&a_over_x, j).mul(&c, j), j);
        assert!(!outer_ok(&alg), "fold of another layer-0 pair");
        // ...which the fold table alone accepts: the links are what reject it.
        assert!(fold_alone_ok(&mut alg), "the fold table alone accepts the forged pair");
    }

    /// Proves the FRI fold table on its own (no links): what a verifier without the
    /// recursion links would accept.
    fn fold_alone_ok<A: Air>(alg: &mut LaneAlgebra<A>) -> bool {
        alg.fold.link_layer0 = false;
        alg.fold.link_leaves = false;
        let p = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };
        let j = alg.fold.lane;
        let traces = alg.fold.traces(&alg.pairs, p.log_rows);
        let t = || Transcript::with_mode(b"fold-alone", HashMode::Lane(j as u8));
        let proof = prove_air(&alg.fold, &traces, 1, &p, &mut t());
        verify_air(&alg.fold, &proof, 1 << p.log_rows, &p, &mut t())
    }

    #[test]
    fn fri_layers_must_be_the_committed_ones() {
        // A cheating prover can build a fold-consistent chain from any layer-0 value down to the
        // final constant (pick the free slot of each layer, solve it in the last one). Only the
        // layer trees stop that.
        let j = 1;
        let (st, proof, _) = lane(j);
        let inner = crate::state::StateAir { st: &st };
        let view = view_of(&inner, &proof, j);
        let mut alg = LaneAlgebra::new(&inner, &proof, &view, INNER);
        let rounds = alg.fold.alphas.len();
        let rows = alg.fold.traces(&alg.pairs, 8)[j].clone();
        let (q, d) = (1usize, Extension4::new(1, 2, 3, 4));
        let half = (crate::RNS_MODULI[j] + 1) / 2;
        let fold = |p: &[Extension4; 2], a: &Extension4, x: u32| {
            let ax = a.mul_scalar(crate::mod_inv_single(x, crate::RNS_MODULI[j]), j);
            p[0].add(&p[1], j).add(&ax.mul(&p[0].sub(&p[1], j), j), j).mul_scalar(half, j)
        };
        let mut out = fold(&alg.pairs[q][0], &alg.fold.alphas[0], rows[q * rounds][7]);
        for l in 1..rounds {
            let sel = rows[q * rounds + l - 1][3] as usize;
            let x = rows[q * rounds + l][7];
            let a = alg.fold.alphas[l];
            alg.pairs[q][l][sel] = out;
            if l + 1 < rounds {
                alg.pairs[q][l][1 - sel] = alg.pairs[q][l][1 - sel].add(&d, j);
            } else {
                let ax = a.mul_scalar(crate::mod_inv_single(x, crate::RNS_MODULI[j]), j);
                let two_out = alg.fold.final_value.add(&alg.fold.final_value, j);
                let (plus, minus) = (Extension4::ONE.add(&ax, j), Extension4::ONE.sub(&ax, j));
                alg.pairs[q][l][1 - sel] = if sel == 0 {
                    two_out.sub(&out.mul(&plus, j), j).mul(&minus.inverse(j), j)
                } else {
                    two_out.sub(&out.mul(&minus, j), j).mul(&plus.inverse(j), j)
                };
            }
            out = fold(&alg.pairs[q][l], &a, x);
        }
        assert_eq!(out, alg.fold.final_value);
        // the hasher is given the forged pairs too
        for l in 0..rounds {
            let pw: Vec<u32> = alg.pairs[q][l].iter().flat_map(|e| e.c).collect();
            alg.leaf_words[alg.fold.leaf_base as usize + q * rounds + l] = alg.fold.leaf_words(&pw, j);
        }
        assert!(!outer_ok(&alg), "forged FRI chain");
        assert!(fold_alone_ok(&mut alg), "the forged chain is fold-consistent");
    }

    #[test]
    fn opened_values_must_be_the_committed_ones() {
        let j = 4;
        let (st, proof, _) = lane(j);
        let inner = crate::state::StateAir { st: &st };
        let view = view_of(&inner, &proof, j);

        // A changed opened value: its leaf no longer hashes to a leaf of the committed tree.
        let mut alg = LaneAlgebra::new(&inner, &proof, &view, INNER);
        alg.opened[2].main[3] = crate::add_mod(alg.opened[2].main[3], 1, crate::RNS_MODULI[j]);
        alg.leaf_words = LaneAlgebra::new(&inner, &proof, &view, INNER).leaf_words; // hasher keeps the honest words
        assert!(!outer_ok(&alg), "opened value differs from the hashed leaf");
        let words = alg.composition.leaf_words(&alg.opened[2]);
        alg.leaf_words[composition_air::leaf_id(2, 0)] = words[0].clone();
        assert!(!outer_ok(&alg), "hashed leaf not in the tree");

        // The next row's aux opening (only its running sum enters the composition) is bound too.
        let mut alg = LaneAlgebra::new(&inner, &proof, &view, INNER);
        alg.opened[1].aux_next[0] = alg.opened[1].aux_next[0].add(&Extension4::ONE, j);
        let words = alg.composition.leaf_words(&alg.opened[1]);
        alg.leaf_words[composition_air::leaf_id(1, 4)] = words[4].clone();
        assert!(!outer_ok(&alg), "next-row aux value");

        // A wrong public root.
        let mut alg = LaneAlgebra::new(&inner, &proof, &view, INNER);
        for c in alg.merkle.claims.iter_mut().filter(|c| c.root == hash_to_words(&proof.aux_root)) {
            c.root[0] ^= 1;
        }
        assert!(!outer_ok(&alg), "wrong aux root");
    }
}
