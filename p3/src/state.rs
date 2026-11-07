//! The state-transition AIR (`ss_rap_v2::state`) on Plonky3, one BabyBear proof per lane (the 5 lanes split the transfers).
//!
//! Same columns and constraints as the in-house AIR. The memory bus becomes the named Plonky3
//! bus "mem" (offline memory check: id, nonce, ts, balance bytes); every byte column goes on the
//! "byte" bus to `ByteTableAir`.
//!
//! The transfers are private: they live only in the committed lane traces, and the statement
//! the proof is about is the account tables alone (`StateStatement::public_part`). The proof
//! says: the final tables follow from the initial ones by valid transfers (balance and nonce
//! rules of every row), whatever those transfers were. So the size of what the verifier, and the
//! Groth16 wrapper, evaluates does not grow with the number of transfers. Binding the transfers
//! to the published blob (and their signatures) is a separate step, not done here.
//!
//! The public side of the memory bus (initial and final tables) is `PublicAir`: its tuples are
//! *periodic columns* built from the statement. Plonky3 binds periodic columns into the
//! transcript and the verifier evaluates them itself, so they act as public columns: the prover
//! cannot change them, and Plonky3's terminal-sum check (all buses sum to zero) then gives
//! exactly init + writes = reads + final.
//!
//! Fiat-Shamir binding of the statement: `p3-batch-stark` 0.9.0-rc.2 does NOT observe periodic
//! columns (nor `BaseAir::periodic_statement`) in its transcript. Without more, a prover could
//! commit a public trace with made-up tuples, learn zeta, and only then pick a statement whose
//! periodic columns satisfy the one combined check at zeta. So the lane-0 public AIR declares
//! `DIGEST_LIMBS` public values, the statement digest (`public_part().digest()`, Poseidon-BN254)
//! in 30-bit limbs: Plonky3 observes public values right after the main commitment, before
//! any challenge, and the verifier recomputes them from the statement it is given.
use crate::blob_eval::{BlobClaim, BlobEvalAir, BlobInput, BytePairTableAir, PAIR_LOG_ROWS};
use crate::tx_bind::{addr_rows, AddrAir, TxAir};
use crate::mulmod::ByteTableAir;
use p3_air::{Air, AirBuilder, BaseAir, PermutationAirBuilder, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;
use ss_rap_v2::state::{StateStatement, ACTIVE, AMT, BYTE_COLS, CF, CT, D1, D2, FROM_ID, FROM_NEW, FROM_OLD, NONCE, T, TO_ID, TO_NEW, TO_NONCE, TO_OLD, TR1, TR2, WIDTH};
use std::borrow::Cow;

/// Main state AIR of one lane. Its "mem" and "tx" tuples start with the lane number, so the
/// 5 lanes can share one batch proof (and its buses) without one lane's rows cancelling another's.
#[derive(Clone, Debug)]
pub struct StateLaneAir {
    pub lane: u32,
    /// receive every active row's transfer from `tx_bind::TxAir` on the "tx" bus (H-01 (b))
    pub bind: bool,
}

impl<F> BaseAir<F> for StateLaneAir {
    fn width(&self) -> usize {
        WIDTH
    }
}

fn mem<E: Clone>(tag: &E, id: E, nonce: E, ts: E, bal: &[E]) -> Vec<E> {
    let mut v = vec![tag.clone(), id, nonce, ts];
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
        let tag = AB::Expr::from_u32(self.lane);
        let w = |e: AB::Expr| Count::bounded(e, 1);
        builder.push_interaction("mem", mem(&tag, c[FROM_ID].clone(), c[NONCE].clone(), c[TR1].clone(), &c[FROM_OLD..FROM_OLD + 8]), w(act.clone()));
        builder.push_interaction("mem", mem(&tag, c[FROM_ID].clone(), c[NONCE].clone() + one.clone(), two_t.clone(), &c[FROM_NEW..FROM_NEW + 8]), w(-act.clone()));
        builder.push_interaction("mem", mem(&tag, c[TO_ID].clone(), c[TO_NONCE].clone(), c[TR2].clone(), &c[TO_OLD..TO_OLD + 8]), w(act.clone()));
        builder.push_interaction("mem", mem(&tag, c[TO_ID].clone(), c[TO_NONCE].clone(), two_t + one, &c[TO_NEW..TO_NEW + 8]), w(-act.clone()));
        if self.bind {
            let mut t = vec![tag.clone(), c[T].clone(), c[FROM_ID].clone(), c[TO_ID].clone()];
            t.extend(c[AMT..AMT + 8].iter().cloned());
            t.push(c[NONCE].clone());
            builder.push_interaction("tx", t, w(-act.clone()));
        }
    }
}

/// Columns of `PublicAir`: 11 mem values + weight.
const PUB_MEM: usize = 11;
const PUB_COLS: usize = PUB_MEM + 1;

/// Public values of the lane-0 public AIR: the statement digest in 30-bit limbs.
pub const DIGEST_LIMBS: usize = 9;
pub const LIMB_BITS: usize = 30;

/// The statement digest (LE bytes of a BN254 element) as `DIGEST_LIMBS` limbs of `LIMB_BITS`.
pub fn digest_limbs(st: &StateStatement) -> Vec<u32> {
    let d = st.public_part().digest();
    let bit = |i: usize| if i < 256 { ((d[i / 8] >> (i % 8)) & 1) as u32 } else { 0 };
    (0..DIGEST_LIMBS).map(|k| (0..LIMB_BITS).map(|b| bit(k * LIMB_BITS + b) << b).sum()).collect()
}

/// The public values of every AIR in `airs` (the digest limbs where a public AIR declares them).
pub fn public_values<F: Field>(st: &StateStatement, airs: &[LaneAirs<F>]) -> Vec<Vec<F>> {
    let limbs: Vec<F> = digest_limbs(st).into_iter().map(F::from_u32).collect();
    airs.iter().map(|a| if matches!(a, LaneAirs::Public(_)) && a.num_public_values() > 0 { limbs.clone() } else { vec![] }).collect()
}

/// The public values of the single proof: the statement digest, and the blob claim.
pub fn all_public_values<F: Field>(st: &StateStatement, airs: &[LaneAirs<F>], blobs: &BlobClaim) -> Vec<Vec<F>> {
    let mut pv = public_values(st, airs);
    for (v, a) in pv.iter_mut().zip(airs) {
        if matches!(a, LaneAirs::Blob(_)) {
            *v = blobs.public_values();
        }
    }
    pv
}

/// Height of every lane's public table: initial + final accounts, as a power of two (at
/// least 4). It does not depend on the number of transfers.
pub fn public_rows(st: &StateStatement) -> usize {
    (2 * st.addrs.len()).next_power_of_two().max(4)
}

/// The public side of the "mem" and "tx" buses for lane `lane`, as periodic columns.
#[derive(Clone, Debug)]
pub struct PublicAir<F> {
    /// PUB_COLS columns, each of length `rows` (a power of two).
    pub cols: Vec<Vec<F>>,
    pub log_rows: usize,
    pub lane: u32,
}

fn bal_bytes(b: u64) -> [u32; 8] {
    std::array::from_fn(|k| ((b >> (8 * k)) & 0xff) as u32)
}

impl<F: Field> PublicAir<F> {
    /// init (weight -1) and final (+1) account tables: minus what the
    /// in-house verifier adds as `bus_sum`, because Plonky3 checks that all buses sum to zero.
    pub fn new(st: &StateStatement, lane: usize) -> Self {
        let mut rows: Vec<Vec<F>> = Vec::new();
        let f = |x: u32| F::from_u32(x);
        let push_mem = |rows: &mut Vec<Vec<F>>, id: u32, nonce: u32, ts: u32, bal: u64, w: F| {
            let mut r = vec![f(id), f(nonce), f(ts)];
            r.extend(bal_bytes(bal).map(f));
            r.push(w);
            rows.push(r);
        };
        for (id, s) in st.states[lane].iter().enumerate() {
            push_mem(&mut rows, id as u32, s.nonce, 0, s.balance, -F::ONE);
        }
        for (id, s) in st.states[lane + 1].iter().enumerate() {
            push_mem(&mut rows, id as u32, s.nonce, st.final_ts[lane][id], s.balance, F::ONE);
        }
        // every lane's public table has the height of the largest one: one evaluation domain
        // for all 5 (a verifier shares the barycentric weights)
        let n = public_rows(st);
        rows.resize(n, vec![F::ZERO; PUB_COLS]);
        let cols = (0..PUB_COLS).map(|j| rows.iter().map(|r| r[j]).collect()).collect();
        Self { cols, log_rows: n.trailing_zeros() as usize, lane: lane as u32 }
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
    fn num_public_values(&self) -> usize {
        if self.lane == 0 { DIGEST_LIMBS } else { 0 }
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
        let tag = AB::Expr::from_u32(self.lane);
        let with_tag = |v: &[AB::Expr]| std::iter::once(tag.clone()).chain(v.iter().cloned()).collect::<Vec<_>>();
        builder.push_interaction("mem", with_tag(&p[..PUB_MEM]), Count::bounded(p[PUB_MEM].clone(), 1));
    }
}

/// The AIRs of the batch proof: per lane the state and public AIRs, the shared byte table, and
/// (in the single proof) the blob AIR.
#[derive(Clone, Debug)]
pub enum LaneAirs<F> {
    State(StateLaneAir),
    Bytes(ByteTableAir),
    Public(PublicAir<F>),
    /// The statement's address table ("addr" bus).
    Addr(AddrAir<F>),
    /// The blob's transaction slots (H-01 (b)).
    Tx(TxAir),
    /// The byte-pair table of the blob AIR ("byte2" bus).
    Pairs(BytePairTableAir),
    Blob(BlobEvalAir),
}

impl<F: Field> BaseAir<F> for LaneAirs<F> {
    fn width(&self) -> usize {
        match self {
            Self::State(a) => <StateLaneAir as BaseAir<F>>::width(a),
            Self::Bytes(a) => <ByteTableAir as BaseAir<F>>::width(a),
            Self::Public(a) => a.width(),
            Self::Pairs(a) => <BytePairTableAir as BaseAir<F>>::width(a),
            Self::Addr(a) => a.width(),
            Self::Tx(a) => <TxAir as BaseAir<F>>::width(a),
            Self::Blob(a) => <BlobEvalAir as BaseAir<F>>::width(a),
        }
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::Bytes(a) => a.preprocessed_trace(),
            Self::Pairs(a) => a.preprocessed_trace(),
            Self::Tx(a) => a.preprocessed_trace(),
            Self::Blob(a) => a.preprocessed_trace(),
            _ => None,
        }
    }
    fn preprocessed_width(&self) -> usize {
        match self {
            Self::Bytes(_) => 1,
            Self::Pairs(a) => <BytePairTableAir as BaseAir<F>>::preprocessed_width(a),
            Self::Tx(a) => <TxAir as BaseAir<F>>::preprocessed_width(a),
            Self::Blob(a) => <BlobEvalAir as BaseAir<F>>::preprocessed_width(a),
            _ => 0,
        }
    }
    fn num_periodic_columns(&self) -> usize {
        match self {
            Self::Public(a) => a.num_periodic_columns(),
            Self::Addr(a) => a.num_periodic_columns(),
            _ => 0,
        }
    }
    fn num_public_values(&self) -> usize {
        match self {
            Self::Public(a) => <PublicAir<F> as BaseAir<F>>::num_public_values(a),
            Self::Blob(a) => <BlobEvalAir as BaseAir<F>>::num_public_values(a),
            _ => 0,
        }
    }
    fn periodic_columns(&self) -> Cow<'_, [Vec<F>]> {
        match self {
            Self::Public(a) => a.periodic_columns(),
            Self::Addr(a) => a.periodic_columns(),
            _ => Cow::Borrowed(&[]),
        }
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::Addr(_) | Self::Tx(_) => vec![],
            _ => (0..<Self as BaseAir<F>>::width(self)).collect(),
        }
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::Tx(_) => vec![],
            _ => (0..<Self as BaseAir<F>>::preprocessed_width(self)).collect(),
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
            Self::Pairs(a) => a.eval(builder),
            Self::Addr(a) => a.eval(builder),
            Self::Tx(a) => a.eval(builder),
            Self::Blob(a) => a.eval(builder),
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
        vec![LaneAirs::State(StateLaneAir { lane: lane as u32, bind: false }), LaneAirs::Bytes(ByteTableAir), LaneAirs::Public(public)],
        vec![RowMajorMatrix::new(v, WIDTH), ByteTableAir::from_counts(&counts), pt],
        vec![n.trailing_zeros() as usize, 8, pl],
    )
}

/// All 5 lanes and the blobs in one batch proof: [State 0..5, Bytes (shared), Public 0..5, Pairs, Blob].
pub fn all_instance<F: Field + p3_field::PrimeField32>(st: &StateStatement, traces: &[Vec<Vec<u32>>; 5], blobs: &BlobInput) -> (Vec<LaneAirs<F>>, Vec<RowMajorMatrix<F>>, Vec<usize>) {
    let (blob_trace, _, _) = crate::blob_eval::trace::<F>(&blobs.blobs, blobs.slots, &blobs.z);
    let pairs = BytePairTableAir::from_counts(&crate::blob_eval::pair_counts(&blob_trace));
    let mut counts = [0u64; 256];
    let mut mains = Vec::new();
    for t in traces {
        let mut v = Vec::with_capacity(t.len() * WIDTH);
        for row in t {
            for (j, &x) in row.iter().enumerate() {
                if j < BYTE_COLS {
                    counts[x as usize] += 1;
                }
                v.push(F::from_u32(x));
            }
        }
        mains.push(RowMajorMatrix::new(v, WIDTH));
    }
    let log_rows = traces[0].len().trailing_zeros() as usize;
    let airs = all_airs::<F>(st, log_rows, blobs.slots);
    let txa = TxAir::new(blobs.slots, log_rows);
    let tx_trace = txa.trace::<F>(&st.addrs, &blobs.blobs).expect("the blobs hold the batch's transactions");
    TxAir::byte_counts(&tx_trace, &mut counts);
    let addr = AddrAir::<F>::new(st);
    let addr_trace = addr.trace(&TxAir::addr_counts(&tx_trace, st.addrs.len()));
    let mut degs: Vec<usize> = traces.iter().map(|t| t.len().trailing_zeros() as usize).collect();
    degs.push(8);
    let mut mats = mains;
    mats.push(ByteTableAir::from_counts(&counts));
    for a in &airs[6..11] {
        let LaneAirs::Public(p) = a else { unreachable!() };
        degs.push(p.log_rows);
        mats.push(p.trace());
    }
    degs.push(addr.log_rows);
    mats.push(addr_trace);
    degs.push(txa.log_height());
    mats.push(tx_trace);
    degs.push(PAIR_LOG_ROWS);
    mats.push(pairs);
    degs.push(BlobEvalAir::new(blobs.slots).log_rows());
    mats.push(blob_trace);
    (airs, mats, degs)
}

/// The 15 AIRs of the single proof, from the statement, the lane height and the number of
/// blob slots: [State 0..5, Bytes, Public 0..5, Addr, Tx, Pairs, Blob] (Blob last).
pub fn all_airs<F: Field>(st: &StateStatement, log_rows: usize, blob_slots: usize) -> Vec<LaneAirs<F>> {
    let mut v: Vec<LaneAirs<F>> = (0..5).map(|l| LaneAirs::State(StateLaneAir { lane: l, bind: true })).collect();
    v.push(LaneAirs::Bytes(ByteTableAir));
    v.extend((0..5).map(|l| LaneAirs::Public(PublicAir::new(st, l))));
    v.push(LaneAirs::Addr(AddrAir::new(st)));
    v.push(LaneAirs::Tx(TxAir::new(blob_slots, log_rows)));
    v.push(LaneAirs::Pairs(BytePairTableAir));
    v.push(LaneAirs::Blob(BlobEvalAir::bound(blob_slots)));
    v
}

/// The trace heights of the single proof.
pub fn all_degrees(st: &StateStatement, p: &Params, blob_slots: usize) -> Vec<usize> {
    let mut d = vec![p.log_rows; 5];
    d.push(8);
    d.extend((0..5).map(|l| PublicAir::<crate::config::BabyBear>::new(st, l).log_rows));
    d.push(addr_rows(st.addrs.len()).trailing_zeros() as usize);
    d.push(TxAir::new(blob_slots, p.log_rows).log_height());
    d.push(PAIR_LOG_ROWS);
    d.push(BlobEvalAir::new(blob_slots).log_rows());
    d
}

/// The AIRs the verifier builds from the statement alone (no trace).
pub fn lane_airs<F: Field>(st: &StateStatement, lane: usize) -> Vec<LaneAirs<F>> {
    vec![LaneAirs::State(StateLaneAir { lane: lane as u32, bind: false }), LaneAirs::Bytes(ByteTableAir), LaneAirs::Public(PublicAir::new(st, lane))]
}

// ---------------------------------------------------------------------------------------------
// Prove / verify all 5 lanes, for each hash backend (Keccak, Poseidon2-BN254)
// ---------------------------------------------------------------------------------------------

/// FRI parameters shared by the 5 lanes.
#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub log_rows: usize,
    pub log_blowup: usize,
    pub queries: usize,
    /// Lookup packing budget (see docs/PLONKY3.md).
    pub budget: usize,
    /// Grinding bits before the FRI query indices.
    pub query_pow: usize,
}

/// Conjectured security floor of a production profile (audit H-02): the FRI part of the
/// soundness, `log_blowup * queries + query_pow` bits under the usual proximity-gap
/// conjecture. This is not a whole-system proof: the quartic BabyBear challenge field
/// (|K| ~ 2^123.6), the lookup argument, Fiat-Shamir over Poseidon2-BN254 and the outer
/// Groth16 each need their own analysis (docs/SIGURIA.md).
pub const MIN_PRODUCTION_BITS: usize = 100;

impl Params {
    /// The production profile for traces of 2^`log_rows` rows: blowup 8, 28 queries, 16 bits
    /// of query grinding = 3 * 28 + 16 = 100 conjectured bits.
    pub const fn production(log_rows: usize) -> Self {
        Self { log_rows, log_blowup: 3, queries: 28, budget: 3, query_pow: 16 }
    }

    /// Conjectured FRI security bits: log_blowup * queries + query_pow.
    pub const fn conjectured_bits(&self) -> usize {
        self.log_blowup * self.queries + self.query_pow
    }

    /// Whether this profile may secure real funds (`MIN_PRODUCTION_BITS` or more).
    pub const fn is_production(&self) -> bool {
        self.conjectured_bits() >= MIN_PRODUCTION_BITS
    }
}

fn degrees(st: &StateStatement, lane: usize, p: &Params) -> Vec<usize> {
    vec![p.log_rows, 8, PublicAir::<crate::config::BabyBear>::new(st, lane).log_rows]
}

macro_rules! backend {
    ($m:ident, $cfg:path) => {
        pub mod $m {
            use super::*;
            use crate::config::BabyBear;
            use $cfg as cfgmod;
            use cfgmod::{config_pow, Config};
            use p3_batch_stark::{prove_batch, verify_batch, BatchProof, ProverData, StarkInstance};
            use p3_field::extension::BinomiallyExtendable;
            use p3_field::{PrimeField32, TwoAdicField};

            /// One BabyBear batch proof per lane (the lanes split the transfers; same field).
            pub struct StateProof {
                pub lanes: [BatchProof<Config<BabyBear>>; 5],
            }

            pub fn prove_lane<F>(st: &StateStatement, trace: &[Vec<u32>], lane: usize, p: &Params) -> BatchProof<Config<F>>
            where
                F: PrimeField32 + TwoAdicField + BinomiallyExtendable<4>,
            {
                assert_eq!(trace.len(), 1 << p.log_rows);
                let cfg = config_pow::<F>(p.log_blowup, p.queries, p.query_pow);
                let (airs, traces, degs) = lane_instance::<F>(st, trace, lane);
                let pd = ProverData::<Config<F>>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &degs, &vec![p.budget; 3], p.log_blowup).unwrap();
                let refs: Vec<&RowMajorMatrix<F>> = traces.iter().collect();
                let pv = public_values(st, &airs);
                let inst = StarkInstance::new_multiple(&airs, &refs, &pv);
                prove_batch(&cfg, &inst, &pd).expect("prove")
            }

            pub fn verify_lane<F>(st: &StateStatement, proof: &BatchProof<Config<F>>, lane: usize, p: &Params) -> bool
            where
                F: PrimeField32 + TwoAdicField + BinomiallyExtendable<4>,
            {
                let cfg = config_pow::<F>(p.log_blowup, p.queries, p.query_pow);
                let airs = lane_airs::<F>(st, lane);
                let Ok(pd) = ProverData::<Config<F>>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &degrees(st, lane, p), &vec![p.budget; 3], p.log_blowup) else {
                    return false;
                };
                verify_batch(&cfg, &airs, proof, &public_values(st, &airs), &pd.common).is_ok()
            }

            /// Proves the 5 lanes (one after another; each uses all cores).
            pub fn prove(st: &StateStatement, traces: &[Vec<Vec<u32>>; 5], p: &Params) -> StateProof {
                StateProof { lanes: std::array::from_fn(|l| prove_lane::<BabyBear>(st, &traces[l], l, p)) }
            }

            /// All 5 lanes and the blobs in ONE batch proof (one FRI, one set of openings):
            /// what the Groth16 circuit verifies, since its cost grows with the number of proofs
            /// and queries.
            pub fn prove_one(st: &StateStatement, traces: &[Vec<Vec<u32>>; 5], blobs: &BlobInput, p: &Params) -> BatchProof<Config<BabyBear>> {
                prove_one_with(st, traces, blobs, p, &|_| {})
            }

            /// `prove_one` with the traces changed by `tamper` first (tests of forged traces).
            #[doc(hidden)]
            pub fn prove_one_with(st: &StateStatement, traces: &[Vec<Vec<u32>>; 5], blobs: &BlobInput, p: &Params, tamper: &dyn Fn(&mut Vec<RowMajorMatrix<BabyBear>>)) -> BatchProof<Config<BabyBear>> {
                for t in traces {
                    assert_eq!(t.len(), 1 << p.log_rows);
                }
                let cfg = config_pow::<BabyBear>(p.log_blowup, p.queries, p.query_pow);
                let (airs, mut traces, degs) = all_instance::<BabyBear>(st, traces, blobs);
                tamper(&mut traces);
                let pd = ProverData::<Config<BabyBear>>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &degs, &vec![p.budget; airs.len()], p.log_blowup).unwrap();
                let refs: Vec<&RowMajorMatrix<BabyBear>> = traces.iter().collect();
                let pv = all_public_values(st, &airs, &blobs.claim());
                let inst = StarkInstance::new_multiple(&airs, &refs, &pv);
                prove_batch(&cfg, &inst, &pd).expect("prove")
            }

            /// Verifies a `prove_one` proof that `st` takes `old_root` to `new_root`, with the
            /// blob claim `blobs`.
            pub fn verify_one(st: &StateStatement, old_root: &[u8; 32], new_root: &[u8; 32], proof: &BatchProof<Config<BabyBear>>, blobs: &BlobClaim, p: &Params) -> bool {
                if !(p.log_rows <= ss_rap_v2::state::MAX_LOG_ROWS as usize && st.well_formed(1 << p.log_rows) && &st.old_root() == old_root && &st.new_root() == new_root) {
                    return false;
                }
                let cfg = config_pow::<BabyBear>(p.log_blowup, p.queries, p.query_pow);
                let airs = all_airs::<BabyBear>(st, p.log_rows, blobs.slots());
                let Ok(pd) = ProverData::<Config<BabyBear>>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &all_degrees(st, p, blobs.slots()), &vec![p.budget; airs.len()], p.log_blowup) else {
                    return false;
                };
                verify_batch(&cfg, &airs, proof, &all_public_values(st, &airs, blobs), &pd.common).is_ok()
            }

            /// Verifies that `st` takes `old_root` to `new_root` (as `ss_rap_v2::state::verify`).
            pub fn verify(st: &StateStatement, old_root: &[u8; 32], new_root: &[u8; 32], proof: &StateProof, p: &Params) -> bool {
                p.log_rows <= ss_rap_v2::state::MAX_LOG_ROWS as usize
                    && st.well_formed(1 << p.log_rows)
                    && &st.old_root() == old_root
                    && &st.new_root() == new_root
                    && (0..5).all(|l| verify_lane::<BabyBear>(st, &proof.lanes[l], l, p))
            }
        }
    };
}

backend!(keccak, crate::config);
backend!(poseidon2_bn254, crate::bn254);
pub use keccak::{prove, verify, StateProof};


/// Test helper: a statement with `n_tx` transfers over 10 accounts.
#[doc(hidden)]
pub fn tests_case(n_tx: u32, log_rows: u32) -> (StateStatement, [Vec<Vec<u32>>; 5]) {
    use ss_rap_v2::state::{build, AccountState, Transfer};
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

/// Test helper: the blobs of the statement's transfers (made-up signatures), at a fixed point.
#[doc(hidden)]
pub fn tests_blobs(st: &StateStatement) -> BlobInput {
    use num_bigint::BigUint;
    let txs: Vec<[u8; crate::tx_bind::TX_BYTES]> = st.lanes.iter().flatten().enumerate().map(|(g, t)| crate::tx_bind::encode_transfer(st, t, 0, &[(g as u8) ^ 0x5a; 65])).collect();
    let blobs = crate::tx_bind::blob_elements(&txs);
    BlobInput { slots: blobs.len().next_power_of_two(), blobs, z: BigUint::parse_bytes(b"1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef", 16).unwrap() }
}

#[cfg(test)]
mod tests {
    use super::keccak::verify_lane;
    use super::*;
    use crate::config::BabyBear;
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

    const P: Params = Params { log_rows: 8, log_blowup: 1, queries: 20, budget: 3, query_pow: 0 };

    #[test]
    fn production_profile_meets_the_floor_and_proves() {
        let prod = Params::production(6);
        assert_eq!(prod.conjectured_bits(), 100);
        assert!(prod.is_production());
        // the CI / testnet profiles are below it
        assert!(!P.is_production());
        assert!(!Params { log_rows: 5, log_blowup: 1, queries: 4, budget: 3, query_pow: 8 }.is_production());
        // blowup 8 works with the AIRs' constraint degrees: the batch proof verifies
        let (st, traces) = case(200, 6);
        let b = tests_blobs(&st);
        let proof = poseidon2_bn254::prove_one(&st, &traces, &b, &prod);
        assert!(poseidon2_bn254::verify_one(&st, &st.old_root(), &st.new_root(), &proof, &b.claim(), &prod));
    }

    #[test]
    fn state_lanes_verify_and_forged_statements_do_not() {
        let (st, traces) = case(1100, 8); // 256 per lane, lane 4 holds 76
        let proof = prove(&st, &traces, &P);
        assert!(verify(&st, &st.old_root(), &st.new_root(), &proof, &P), "honest");
        // a different final balance in lane 2's output table
        let mut bad = st.clone();
        bad.states[3][4].balance += 1;
        assert!(!verify_lane::<BabyBear>(&bad, &proof.lanes[2], 2, &P), "final table of lane 2");
        assert!(!verify_lane::<BabyBear>(&bad, &proof.lanes[3], 3, &P), "initial table of lane 3");
        let mut bad = st.clone();
        bad.states[1][0].nonce += 1;
        assert!(!verify_lane::<BabyBear>(&bad, &proof.lanes[0], 0, &P), "nonce in the table after lane 0");
        // the transfers are private: the statement is the tables alone
        let mut other = st.clone();
        other.lanes[0][5].amount += 1;
        other.lanes[4].pop();
        assert!(verify_lane::<BabyBear>(&other, &proof.lanes[0], 0, &P) && other.public_part() == st.public_part());
    }

    #[test]
    fn one_proof_for_all_lanes_verifies_and_forgeries_do_not() {
        let (st, traces) = case(1100, 8);
        let b = tests_blobs(&st);
        let claim = b.claim();
        let proof = super::keccak::prove_one(&st, &traces, &b, &P);
        let ok = |s: &StateStatement| super::keccak::verify_one(s, &s.old_root(), &s.new_root(), &proof, &claim, &P);
        assert!(ok(&st), "honest");
        let mut bad = st.clone();
        bad.states[3][4].balance += 1;
        assert!(!ok(&bad), "intermediate table");
        let mut bad = st.clone();
        bad.final_ts[2][1] += 1;
        assert!(!ok(&bad), "final timestamp");
        // the public statement has no transfers: proving with them or without gives the same proof statement
        assert!(ok(&st.public_part()), "public part");
        // the blob claim is part of the statement
        let mut other = claim.clone();
        other.s[0] += 1u32;
        assert!(!super::keccak::verify_one(&st, &st.old_root(), &st.new_root(), &proof, &other, &P), "blob sum");
        let mut other = claim.clone();
        other.d[0][2] ^= 1;
        assert!(!super::keccak::verify_one(&st, &st.old_root(), &st.new_root(), &proof, &other, &P), "blob digest");
        let proof = super::poseidon2_bn254::prove_one(&st, &traces, &b, &P);
        assert!(super::poseidon2_bn254::verify_one(&st, &st.old_root(), &st.new_root(), &proof, &claim, &P));
    }

    /// Audit H-01 (b): the blobs must hold exactly the executed transfers, each in its slot.
    #[test]
    fn the_blob_holds_exactly_the_executed_transfers() {
        use crate::tx_bind::{blob_elements, encode_transfer, TX_BYTES};
        let (st, traces) = case(300, P.log_rows as u32);
        let txs: Vec<[u8; TX_BYTES]> = st.lanes.iter().flatten().enumerate().map(|(g, t)| encode_transfer(&st, t, 0, &[(g as u8) | 1; 65])).collect();
        let with = |txs: &[[u8; TX_BYTES]]| BlobInput { blobs: blob_elements(txs), ..tests_blobs(&st) };
        // a prover panic (a bus or constraint that does not hold) counts as rejection
        let accepts = |b: &BlobInput, tamper: &dyn Fn(&mut Vec<RowMajorMatrix<BabyBear>>)| {
            let claim = b.claim();
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| super::keccak::prove_one_with(&st, &traces, b, &P, tamper)))
                .map(|proof| super::keccak::verify_one(&st, &st.old_root(), &st.new_root(), &proof, &claim, &P))
                .unwrap_or(false)
        };
        assert!(accepts(&with(&txs), &|_| {}), "honest");
        let mut t = txs.clone();
        t[17][47] ^= 1; // amount
        assert!(!accepts(&with(&t), &|_| {}), "another amount");
        let mut t = txs.clone();
        t[3][21] ^= 1; // recipient (an address outside the table)
        let r = std::panic::catch_unwind(|| accepts(&with(&t), &|_| {}));
        assert!(!r.unwrap_or(false), "unknown recipient");
        let mut t = txs.clone();
        t[3][20..40].copy_from_slice(&st.addrs[(st.lanes[0][3].to as usize + 1) % st.addrs.len()]);
        assert!(!accepts(&with(&t), &|_| {}), "another known recipient");
        let mut t = txs.clone();
        t.swap(5, 6);
        assert!(!accepts(&with(&t), &|_| {}), "two transfers swapped");
        let mut t = txs.clone();
        t.pop();
        assert!(!accepts(&with(&t), &|_| {}), "a transfer missing");
        let mut t = txs.clone();
        t.push(t[0]);
        assert!(!accepts(&with(&t), &|_| {}), "a transfer the lanes did not run");
        // a slot marked inactive while its bytes hold a transfer
        let tx_at = 13; // [State 0..5, Bytes, Public 0..5, Addr, Tx, ...]
        let width = crate::tx_bind::SLOT_BYTES + 3;
        assert!(!accepts(&with(&txs), &|m| m[tx_at].values[7 * width + crate::tx_bind::SLOT_BYTES] = BabyBear::ZERO), "slot switched off");
    }

    #[test]
    fn poseidon2_bn254_backend_verifies() {
        let (st, traces) = case(600, 8);
        let proof = poseidon2_bn254::prove(&st, &traces, &P);
        assert!(poseidon2_bn254::verify(&st, &st.old_root(), &st.new_root(), &proof, &P));
        let mut bad = st.clone();
        bad.states[5][0].balance ^= 1;
        assert!(!poseidon2_bn254::verify_lane::<BabyBear>(&bad, &proof.lanes[4], 4, &P));
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
