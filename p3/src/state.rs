//! The state-transition AIR (`ss_rap_v2::state`) on Plonky3, one proof per RNS lane.
//!
//! Same columns and constraints as the in-house AIR. The two buses become named Plonky3 buses:
//! "mem" (offline memory check: id, nonce, ts, balance bytes) and "tx" (t, from, to, nonce,
//! amount bytes); every byte column goes on the "byte" bus to `ByteTableAir`.
//!
//! The public side of the buses (initial table, final table, the lane's transactions) is
//! `PublicAir`: its tuples are *periodic columns* built from the statement. Plonky3 binds
//! periodic columns into the transcript and the verifier evaluates them itself, so they act
//! as public columns: the prover cannot change them, and Plonky3's terminal-sum check
//! (all buses sum to zero) then gives exactly init + writes = reads + final and
//! "every public transaction executed once, at its index".
use crate::mulmod::ByteTableAir;
use p3_air::{Air, AirBuilder, BaseAir, PermutationAirBuilder, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;
use ss_rap_v2::state::{StateStatement, ACTIVE, AMT, BYTE_COLS, CF, CT, D1, D2, FROM_ID, FROM_NEW, FROM_OLD, NONCE, T, TO_ID, TO_NEW, TO_NONCE, TO_OLD, TR1, TR2, WIDTH};
use std::borrow::Cow;

/// Main state AIR of one lane.
#[derive(Clone, Debug)]
pub struct StateLaneAir;

impl<F> BaseAir<F> for StateLaneAir {
    fn width(&self) -> usize {
        WIDTH
    }
}

fn mem<E: Clone>(id: E, nonce: E, ts: E, bal: &[E]) -> Vec<E> {
    let mut v = vec![id, nonce, ts];
    v.extend_from_slice(bal);
    v
}

impl<AB> Air<AB> for StateLaneAir
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let c: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nx_t: AB::Expr = main.next_slice()[T].into();
        let one = AB::Expr::ONE;
        let k256 = AB::Expr::from_u32(256);
        let two_t = c[T].clone() + c[T].clone();
        builder.assert_bool(c[ACTIVE].clone());
        builder.when_first_row().assert_eq(c[T].clone(), one.clone());
        builder.when_transition().assert_eq(nx_t, c[T].clone() + one.clone());
        builder.assert_eq(c[D1].clone() + c[D1 + 1].clone() * k256.clone(), two_t.clone() - c[TR1].clone() - one.clone());
        builder.assert_eq(c[D2].clone() + c[D2 + 1].clone() * k256.clone(), two_t.clone() - c[TR2].clone());
        for (lhs, rhs, carry) in [(FROM_NEW, FROM_OLD, CF), (TO_OLD, TO_NEW, CT)] {
            for k in 0..8 {
                let mut v = c[lhs + k].clone() + c[AMT + k].clone();
                if k > 0 {
                    v += c[carry + k - 1].clone();
                }
                v -= c[rhs + k].clone();
                if k < 7 {
                    v -= c[carry + k].clone() * k256.clone();
                }
                builder.assert_zero(v);
            }
            for k in 0..7 {
                builder.assert_bool(c[carry + k].clone());
            }
        }
        for j in 0..BYTE_COLS {
            builder.push_interaction("byte", [c[j].clone()], 1);
        }
        let act = c[ACTIVE].clone();
        let w = |e: AB::Expr| Count::bounded(e, 1);
        builder.push_interaction("mem", mem(c[FROM_ID].clone(), c[NONCE].clone(), c[TR1].clone(), &c[FROM_OLD..FROM_OLD + 8]), w(act.clone()));
        builder.push_interaction("mem", mem(c[FROM_ID].clone(), c[NONCE].clone() + one.clone(), two_t.clone(), &c[FROM_NEW..FROM_NEW + 8]), w(-act.clone()));
        builder.push_interaction("mem", mem(c[TO_ID].clone(), c[TO_NONCE].clone(), c[TR2].clone(), &c[TO_OLD..TO_OLD + 8]), w(act.clone()));
        builder.push_interaction("mem", mem(c[TO_ID].clone(), c[TO_NONCE].clone(), two_t + one, &c[TO_NEW..TO_NEW + 8]), w(-act.clone()));
        let mut tx = vec![c[T].clone(), c[FROM_ID].clone(), c[TO_ID].clone(), c[NONCE].clone()];
        tx.extend_from_slice(&c[AMT..AMT + 8]);
        builder.push_interaction("tx", tx, w(-act));
    }
}

/// Columns of `PublicAir`: 11 mem values + weight, 12 tx values + weight.
const PUB_MEM: usize = 11;
const PUB_TX: usize = 12;
const PUB_COLS: usize = PUB_MEM + 1 + PUB_TX + 1;

/// The public side of the "mem" and "tx" buses for lane `lane`, as periodic columns.
#[derive(Clone, Debug)]
pub struct PublicAir<F> {
    /// PUB_COLS columns, each of length `rows` (a power of two).
    pub cols: Vec<Vec<F>>,
    pub log_rows: usize,
}

fn bal_bytes(b: u64) -> [u32; 8] {
    std::array::from_fn(|k| ((b >> (8 * k)) & 0xff) as u32)
}

impl<F: Field> PublicAir<F> {
    /// init (weight -1), final (+1) and the lane's transactions (+1): minus what the
    /// in-house verifier adds as `bus_sum`, because Plonky3 checks that all buses sum to zero.
    pub fn new(st: &StateStatement, lane: usize) -> Self {
        let mut rows: Vec<Vec<F>> = Vec::new();
        let f = |x: u32| F::from_u32(x);
        let push_mem = |rows: &mut Vec<Vec<F>>, id: u32, nonce: u32, ts: u32, bal: u64, w: F| {
            let mut r = vec![f(id), f(nonce), f(ts)];
            r.extend(bal_bytes(bal).map(f));
            r.push(w);
            r.extend(std::iter::repeat_n(F::ZERO, PUB_TX + 1));
            rows.push(r);
        };
        for (id, s) in st.states[lane].iter().enumerate() {
            push_mem(&mut rows, id as u32, s.nonce, 0, s.balance, -F::ONE);
        }
        for (id, s) in st.states[lane + 1].iter().enumerate() {
            push_mem(&mut rows, id as u32, s.nonce, st.final_ts[lane][id], s.balance, F::ONE);
        }
        for (k, tx) in st.lanes[lane].iter().enumerate() {
            let mut r = vec![F::ZERO; PUB_MEM + 1];
            r.extend([f(k as u32 + 1), f(tx.from), f(tx.to), f(tx.nonce)]);
            r.extend(bal_bytes(tx.amount).map(f));
            r.push(F::ONE);
            rows.push(r);
        }
        let n = rows.len().next_power_of_two().max(4);
        rows.resize(n, vec![F::ZERO; PUB_COLS]);
        let cols = (0..PUB_COLS).map(|j| rows.iter().map(|r| r[j]).collect()).collect();
        Self { cols, log_rows: n.trailing_zeros() as usize }
    }

    /// The same values as a main trace (lookup trace generation reads main columns only); the
    /// AIR constrains every main column to equal its periodic (public) column.
    pub fn trace(&self) -> RowMajorMatrix<F> {
        let n = 1usize << self.log_rows;
        RowMajorMatrix::new((0..n).flat_map(|i| self.cols.iter().map(move |c| c[i])).collect(), PUB_COLS)
    }
}

impl<F: Field> BaseAir<F> for PublicAir<F> {
    fn width(&self) -> usize {
        PUB_COLS
    }
    fn num_periodic_columns(&self) -> usize {
        PUB_COLS
    }
    fn periodic_columns(&self) -> Cow<'_, [Vec<F>]> {
        Cow::Borrowed(&self.cols)
    }
}

impl<AB> Air<AB> for PublicAir<AB::F>
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let p: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let q: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        for (a, b) in p.iter().zip(q) {
            builder.assert_eq(a.clone(), b);
        }
        builder.push_interaction("mem", p[..PUB_MEM].to_vec(), Count::bounded(p[PUB_MEM].clone(), 1));
        builder.push_interaction("tx", p[PUB_MEM + 1..PUB_MEM + 1 + PUB_TX].to_vec(), Count::bounded(p[PUB_COLS - 1].clone(), 1));
    }
}

/// The three AIRs of one lane, in one batch proof.
#[derive(Clone, Debug)]
pub enum LaneAirs<F> {
    State(StateLaneAir),
    Bytes(ByteTableAir),
    Public(PublicAir<F>),
}

impl<F: Field> BaseAir<F> for LaneAirs<F> {
    fn width(&self) -> usize {
        match self {
            Self::State(a) => <StateLaneAir as BaseAir<F>>::width(a),
            Self::Bytes(a) => <ByteTableAir as BaseAir<F>>::width(a),
            Self::Public(a) => a.width(),
        }
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::Bytes(a) => a.preprocessed_trace(),
            _ => None,
        }
    }
    fn preprocessed_width(&self) -> usize {
        match self {
            Self::Bytes(_) => 1,
            _ => 0,
        }
    }
    fn num_periodic_columns(&self) -> usize {
        match self {
            Self::Public(a) => a.num_periodic_columns(),
            _ => 0,
        }
    }
    fn periodic_columns(&self) -> Cow<'_, [Vec<F>]> {
        match self {
            Self::Public(a) => a.periodic_columns(),
            _ => Cow::Borrowed(&[]),
        }
    }
}

impl<AB> Air<AB> for LaneAirs<AB::F>
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::State(a) => a.eval(builder),
            Self::Bytes(a) => a.eval(builder),
            Self::Public(a) => a.eval(builder),
        }
    }
}

/// AIRs and traces of lane `lane` (the trace rows come from `ss_rap_v2::state::build`).
pub fn lane_instance<F: Field>(st: &StateStatement, trace: &[Vec<u32>], lane: usize) -> (Vec<LaneAirs<F>>, Vec<RowMajorMatrix<F>>, Vec<usize>) {
    let n = trace.len();
    let mut counts = [0u64; 256];
    let mut v = Vec::with_capacity(n * WIDTH);
    for row in trace {
        for (j, &x) in row.iter().enumerate() {
            if j < BYTE_COLS {
                counts[x as usize] += 1;
            }
            v.push(F::from_u32(x));
        }
    }
    let public = PublicAir::new(st, lane);
    let pl = public.log_rows;
    let pt = public.trace();
    (
        vec![LaneAirs::State(StateLaneAir), LaneAirs::Bytes(ByteTableAir), LaneAirs::Public(public)],
        vec![RowMajorMatrix::new(v, WIDTH), ByteTableAir::from_counts(&counts), pt],
        vec![n.trailing_zeros() as usize, 8, pl],
    )
}

/// The AIRs the verifier builds from the statement alone (no trace).
pub fn lane_airs<F: Field>(st: &StateStatement, lane: usize) -> Vec<LaneAirs<F>> {
    vec![LaneAirs::State(StateLaneAir), LaneAirs::Bytes(ByteTableAir), LaneAirs::Public(PublicAir::new(st, lane))]
}

// ---------------------------------------------------------------------------------------------
// Prove / verify all 5 lanes
// ---------------------------------------------------------------------------------------------

use crate::config::{config, BabyBear, Config, KoalaBear, Lane3, Lane4, Lane5};
use p3_batch_stark::{prove_batch, verify_batch, BatchProof, ProverData, StarkInstance};
use p3_field::extension::BinomiallyExtendable;
use p3_field::{PrimeField32, TwoAdicField};

/// FRI parameters shared by the 5 lanes.
#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub log_rows: usize,
    pub log_blowup: usize,
    pub queries: usize,
    /// Lookup packing budget (see docs/PLONKY3.md).
    pub budget: usize,
}

pub struct StateProof {
    pub l0: BatchProof<Config<BabyBear>>,
    pub l1: BatchProof<Config<KoalaBear>>,
    pub l2: BatchProof<Config<Lane3>>,
    pub l3: BatchProof<Config<Lane4>>,
    pub l4: BatchProof<Config<Lane5>>,
}

fn degrees(st: &StateStatement, lane: usize, p: &Params) -> Vec<usize> {
    vec![p.log_rows, 8, PublicAir::<BabyBear>::new(st, lane).log_rows]
}

fn prove_lane<F>(st: &StateStatement, trace: &[Vec<u32>], lane: usize, p: &Params) -> BatchProof<Config<F>>
where
    F: PrimeField32 + TwoAdicField + BinomiallyExtendable<4>,
{
    assert_eq!(trace.len(), 1 << p.log_rows);
    let cfg = config::<F>(p.log_blowup, p.queries);
    let (airs, traces, degs) = lane_instance::<F>(st, trace, lane);
    let pd = ProverData::<Config<F>>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &degs, &vec![p.budget; 3], p.log_blowup).unwrap();
    let refs: Vec<&RowMajorMatrix<F>> = traces.iter().collect();
    let inst = StarkInstance::new_multiple(&airs, &refs, &[vec![], vec![], vec![]]);
    prove_batch(&cfg, &inst, &pd).expect("prove")
}

fn verify_lane<F>(st: &StateStatement, proof: &BatchProof<Config<F>>, lane: usize, p: &Params) -> bool
where
    F: PrimeField32 + TwoAdicField + BinomiallyExtendable<4>,
{
    let cfg = config::<F>(p.log_blowup, p.queries);
    let airs = lane_airs::<F>(st, lane);
    let Ok(pd) = ProverData::<Config<F>>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &degrees(st, lane, p), &vec![p.budget; 3], p.log_blowup) else {
        return false;
    };
    verify_batch(&cfg, &airs, proof, &[vec![], vec![], vec![]], &pd.common).is_ok()
}

/// Proves the 5 lanes (one after another; each uses all cores).
pub fn prove(st: &StateStatement, traces: &[Vec<Vec<u32>>; 5], p: &Params) -> StateProof {
    StateProof {
        l0: prove_lane::<BabyBear>(st, &traces[0], 0, p),
        l1: prove_lane::<KoalaBear>(st, &traces[1], 1, p),
        l2: prove_lane::<Lane3>(st, &traces[2], 2, p),
        l3: prove_lane::<Lane4>(st, &traces[3], 3, p),
        l4: prove_lane::<Lane5>(st, &traces[4], 4, p),
    }
}

/// Verifies that `st` takes `old_root` to `new_root` (as `ss_rap_v2::state::verify`).
pub fn verify(st: &StateStatement, old_root: &[u8; 32], new_root: &[u8; 32], proof: &StateProof, p: &Params) -> bool {
    p.log_rows <= ss_rap_v2::state::MAX_LOG_ROWS as usize
        && st.well_formed(1 << p.log_rows)
        && &st.old_root() == old_root
        && &st.new_root() == new_root
        && verify_lane::<BabyBear>(st, &proof.l0, 0, p)
        && verify_lane::<KoalaBear>(st, &proof.l1, 1, p)
        && verify_lane::<Lane3>(st, &proof.l2, 2, p)
        && verify_lane::<Lane4>(st, &proof.l3, 3, p)
        && verify_lane::<Lane5>(st, &proof.l4, 4, p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ss_rap_v2::state::{build, AccountState, Transfer};

    fn case(n_tx: u32, log_rows: u32) -> (StateStatement, [Vec<Vec<u32>>; 5]) {
        let k = 10usize;
        let addrs: Vec<[u8; 20]> = (0..k).map(|i| [i as u8 + 1; 20]).collect();
        let old: Vec<AccountState> = (0..k).map(|i| AccountState { balance: 1_000_000 + i as u64, nonce: 0 }).collect();
        let mut nonces = vec![0u32; k];
        let txs: Vec<Transfer> = (0..n_tx)
            .map(|j| {
                let from = (j * 3 + 1) % k as u32;
                let tx = Transfer { from, to: (j * 7 + 2) % k as u32, amount: 5 + j as u64, nonce: nonces[from as usize] };
                nonces[from as usize] += 1;
                tx
            })
            .collect();
        build(&addrs, &old, &txs, log_rows, true).unwrap()
    }

    const P: Params = Params { log_rows: 8, log_blowup: 1, queries: 20, budget: 3 };

    #[test]
    fn state_lanes_verify_and_forged_statements_do_not() {
        let (st, traces) = case(1100, 8); // 256 per lane, lane 4 holds 76
        let proof = prove(&st, &traces, &P);
        assert!(verify(&st, &st.old_root(), &st.new_root(), &proof, &P), "honest");
        // a different final balance in lane 2's output table
        let mut bad = st.clone();
        bad.states[3][4].balance += 1;
        assert!(!verify_lane::<Lane3>(&bad, &proof.l2, 2, &P), "final table of lane 2");
        assert!(!verify_lane::<Lane4>(&bad, &proof.l3, 3, &P), "initial table of lane 3");
        // a different transaction in lane 0
        let mut bad = st.clone();
        bad.lanes[0][5].amount += 1;
        assert!(!verify_lane::<BabyBear>(&bad, &proof.l0, 0, &P), "tx amount");
        let mut bad = st.clone();
        bad.lanes[1].swap(0, 1);
        assert!(!verify_lane::<KoalaBear>(&bad, &proof.l1, 1, &P), "tx order");
        // a dropped transaction
        let mut bad = st.clone();
        assert!(bad.lanes[4].pop().is_some());
        assert!(!verify_lane::<Lane5>(&bad, &proof.l4, 4, &P), "dropped tx");
    }

    #[test]
    fn overspending_batch_does_not_verify() {
        let addrs: Vec<[u8; 20]> = (0..4u8).map(|i| [i + 1; 20]).collect();
        let old = vec![AccountState { balance: 100, nonce: 0 }; 4];
        let txs = vec![Transfer { from: 0, to: 1, amount: 500, nonce: 0 }];
        let (st, traces) = build(&addrs, &old, &txs, 8, false).unwrap();
        let proof = std::panic::catch_unwind(|| prove(&st, &traces, &P));
        if let Ok(proof) = proof {
            assert!(!verify(&st, &st.old_root(), &st.new_root(), &proof, &P), "overspend accepted");
        }
    }
}
