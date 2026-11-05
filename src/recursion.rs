//! The recursive verifier of one lane, assembled from the recursion AIRs (docs/REKURSIONI.md, R7).
//!
//! Built up step by step; each step replaces a public claim with a link to another table of the
//! same stack:
//!   - R7.2a: composition rows -> FRI fold rows. The layer-0 values FRI folds are the f(x) the
//!     composition AIR recomputed from the opened values (bus `fri_air::LINK_LAYER0`).

use crate::composition_air::{self, CompositionAir};
use crate::fri_air::FriFoldAir;
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
    }
}

/// The lane's algebra tables, linked: (composition, fold) and their stacked traces.
pub struct LaneAlgebra<'a, A: Air> {
    pub composition: CompositionAir<'a, A>,
    pub fold: FriFoldAir,
    pub opened: Vec<composition_air::OpenedRow>,
    pub pairs: Vec<Vec<[Extension4; 2]>>,
}

impl<'a, A: Air> LaneAlgebra<'a, A> {
    pub fn new(inner: &'a A, proof: &StarkProof, view: &StarkView, params: StarkParams) -> Self {
        let (mut composition, opened) = composition_air::from_proof(inner, proof, view, params);
        composition.link_fri = true;
        let j = composition.lane;
        Self { fold: fold_air(proof, view, &params, j), pairs: fold_pairs(proof, j), composition, opened }
    }

    pub fn stack(&self) -> Stacked<'_> {
        Stacked::new(vec![&self.composition, &self.fold])
    }

    pub fn traces(&self, log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        self.stack().traces(&[self.composition.traces(&self.opened, log_rows), self.fold.traces(&self.pairs, log_rows)], log_rows)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::HashMode;
    use crate::stark::{prove_air, prove_air_lanes, verify_air, verify_air_view};
    use crate::transcript::Transcript;

    const INNER: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 8 };
    const OUTER: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };

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

    fn outer_ok<A: Air>(alg: &LaneAlgebra<A>, traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]) -> bool {
        let stack = alg.stack();
        let j = alg.composition.lane;
        let t = || Transcript::with_mode(b"recursion", HashMode::Lane(j as u8));
        let proof = prove_air(&stack, traces, alg.composition.claims.len(), &OUTER, &mut t());
        verify_air(&stack, &proof, 1 << OUTER.log_rows, &OUTER, &mut t())
    }

    #[test]
    fn linked_algebra_verifies_in_every_lane() {
        let (st, traces) = state_case();
        let inner = crate::state::StateAir { st: &st };
        let proofs = prove_air_lanes(&inner, &traces, st.num_txs(), &INNER, b"inner");
        for j in 0..DEFAULT_RNS_CHANNELS {
            let view = verify_air_view(&inner, &proofs[j], 5 << INNER.log_rows, &INNER, &mut Transcript::with_mode(b"inner", HashMode::Lane(j as u8))).unwrap();
            let alg = LaneAlgebra::new(&inner, &proofs[j], &view, INNER);
            assert!(outer_ok(&alg, &alg.traces(OUTER.log_rows)), "lane {j}");
        }
    }

    #[test]
    fn fri_must_fold_the_values_the_composition_checked() {
        let (st, traces) = state_case();
        let inner = crate::state::StateAir { st: &st };
        let j = 2;
        let t = || Transcript::with_mode(b"inner", HashMode::Lane(j as u8));
        let proof = prove_air(&inner, &traces, st.num_txs(), &INNER, &mut t());
        let view = verify_air_view(&inner, &proof, 5 << INNER.log_rows, &INNER, &mut t()).unwrap();

        // Replace query 1's layer-0 pair by another pair that folds to the same value, so the FRI
        // chain alone still holds: f0 += (1 - a/x) c, f1 -= (1 + a/x) c.
        let alg0 = LaneAlgebra::new(&inner, &proof, &view, INNER);
        let x = alg0.fold.traces(&alg0.pairs, OUTER.log_rows)[j][alg0.fold.alphas.len()][7]; // X of row (q = 1, l = 0)
        let a_over_x = alg0.fold.alphas[0].mul_scalar(crate::mod_inv_single(x, crate::RNS_MODULI[j]), j);
        let c = Extension4::new(5, 6, 7, 8);
        let mut forged = alg0.pairs.clone();
        forged[1][0][0] = forged[1][0][0].add(&Extension4::ONE.sub(&a_over_x, j).mul(&c, j), j);
        forged[1][0][1] = forged[1][0][1].sub(&Extension4::ONE.add(&a_over_x, j).mul(&c, j), j);
        let mut alg = LaneAlgebra::new(&inner, &proof, &view, INNER);
        alg.pairs = forged.clone();
        assert!(!outer_ok(&alg, &alg.traces(OUTER.log_rows)), "fold of another layer-0 pair");
        // ...which the fold table alone accepts: the link is what rejects it.
        alg.fold.link_layer0 = false;
        alg.composition.link_fri = false;
        assert!(outer_ok(&alg, &alg.traces(OUTER.log_rows)), "unlinked tables accept the forged pair");

        // An opened value changed together with its quotient so that C = Q Z still fails or f
        // moves: either way the stack rejects.
        let mut alg = LaneAlgebra::new(&inner, &proof, &view, INNER);
        alg.opened[2].main[3] = crate::add_mod(alg.opened[2].main[3], 1, crate::RNS_MODULI[j]);
        assert!(!outer_ok(&alg, &alg.traces(OUTER.log_rows)), "opened value changed");

        // Without the link the fold table alone would accept a different layer 0: the link is
        // what binds them (sanity check of the test itself).
        let mut alg = LaneAlgebra::new(&inner, &proof, &view, INNER);
        alg.fold.link_layer0 = false;
        alg.composition.link_fri = false;
        assert!(outer_ok(&alg, &alg.traces(OUTER.log_rows)), "unlinked honest stack");
    }
}
