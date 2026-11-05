//! State-transition AIR: account transfers proven against the old and new state.
//!
//! This is what links the STARK to real transactions. For a batch of transfers it proves that
//! the new account table is exactly the old one after applying every transfer in order, with
//!   - no balance ever going negative and no balance overflowing u64 (byte limbs + carries),
//!   - the sender's nonce matching the transaction and increasing by one,
//!   - every transaction of the public list executed exactly once, at its position.
//!
//! Memory is checked offline (Blum et al.): every access reads (id, nonce, ts, balance) and
//! writes the updated tuple with a strictly larger timestamp. With multisets over a LogUp bus,
//!
//! ```text
//! init  +  writes  =  reads  +  final
//! ```
//!
//! where init (all timestamps 0) and final are public tables the verifier folds in itself.
//! Transactions travel on a second bus: each active row consumes the fingerprint of the tx it
//! executes, the verifier adds the public list, so the two must match as multisets, and the
//! tx index is the row counter t, which fixes the order.
//!
//! Lanes: each of the 5 RNS channels proves a consecutive slice of the batch in its own field.
//! The public table after lane j is the table before lane j+1, so the lanes chain:
//! old state -> lane 0 -> ... -> lane 4 -> new state. All values are bytes or small integers
//! (ids, nonces < 2^30, timestamps <= 2N+1), every identity stays far below m_j / 2, so each
//! lane is sound in its own field (see `uint256.rs` for why this matters).
//!
//! Row (one transfer, from-access at timestamp 2t, to-access at 2t+1), width 66:
//!   bytes  : amount[8], from_old[8], from_new[8], to_old[8], to_new[8], d1[2], d2[2]
//!   fields : active, t, from_id, to_id, nonce, tr1, to_nonce, tr2, cf[7], ct[7]
//! Constraints:
//!   active * (active - 1)                     active rows are 0/1
//!   (t - 1) * first_row                       counter starts at 1
//!   (t_next - t - 1) * not_last               counter steps by 1
//!   d1 - (2t - tr1 - 1),  d2 - (2t - tr2)     reads are strictly older than the writes
//!   from_new_k + amount_k + cf_{k-1} - from_old_k - 256 cf_k     (k = 0..7, cf_7 = 0)
//!   to_old_k + amount_k + ct_{k-1} - to_new_k - 256 ct_k         (k = 0..7, ct_7 = 0)
//!   cf_k, ct_k boolean
//!
//! MVP scope: the public tables hold every account of the (small) state, so the verifier work is
//! O(accounts). Production replaces them with the touched accounts plus sparse-Merkle paths
//! against the state roots, without changing the AIR.

use crate::stark::{self, Air, BusTerm, BusTuple, Challenges, Point, StarkParams, StarkProof};
use crate::transcript::Transcript;
use crate::{add_mod, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

pub type Address = [u8; 20];

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AccountState {
    pub balance: u64,
    pub nonce: u32,
}

impl AccountState {
    pub fn is_empty(&self) -> bool {
        self.balance == 0 && self.nonce == 0
    }
}

/// A transfer between two accounts, by their index in the address table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Transfer {
    pub from: u32,
    pub to: u32,
    pub amount: u64,
    pub nonce: u32,
}

/// Nonces must stay small field elements in every lane.
pub const MAX_NONCE: u32 = 1 << 30;
/// Timestamps 2t+1 must fit the 2-byte read-age columns.
pub const MAX_LOG_ROWS: u32 = 15;

/// Canonical state root: Blake3 over the non-empty accounts in address order.
pub fn state_root(addrs: &[Address], states: &[AccountState]) -> [u8; 32] {
    assert_eq!(addrs.len(), states.len());
    let mut idx: Vec<usize> = (0..addrs.len()).collect();
    idx.sort_by_key(|&i| addrs[i]);
    let mut h = blake3::Hasher::new();
    h.update(b"SS-RAP/v2/state");
    for i in idx {
        if !states[i].is_empty() {
            h.update(&addrs[i]);
            h.update(&states[i].balance.to_be_bytes());
            h.update(&states[i].nonce.to_be_bytes());
        }
    }
    *h.finalize().as_bytes()
}

/// Everything public about a batch: the address table, the table after every lane (states[0] is
/// the old state, states[5] the new one), each lane's final access timestamps and transfers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateStatement {
    pub addrs: Vec<Address>,
    pub states: [Vec<AccountState>; DEFAULT_RNS_CHANNELS + 1],
    pub final_ts: [Vec<u32>; DEFAULT_RNS_CHANNELS],
    pub lanes: [Vec<Transfer>; DEFAULT_RNS_CHANNELS],
}

impl StateStatement {
    pub fn old_root(&self) -> [u8; 32] {
        state_root(&self.addrs, &self.states[0])
    }
    pub fn new_root(&self) -> [u8; 32] {
        state_root(&self.addrs, &self.states[DEFAULT_RNS_CHANNELS])
    }
    pub fn num_txs(&self) -> usize {
        self.lanes.iter().map(Vec::len).sum()
    }
    pub fn digest(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"SS-RAP/v2/state-statement");
        h.update(&(self.addrs.len() as u64).to_le_bytes());
        for a in &self.addrs {
            h.update(a);
        }
        for table in &self.states {
            for s in table {
                h.update(&s.balance.to_le_bytes());
                h.update(&s.nonce.to_le_bytes());
            }
        }
        for ts in &self.final_ts {
            for t in ts {
                h.update(&t.to_le_bytes());
            }
        }
        for lane in &self.lanes {
            h.update(&(lane.len() as u64).to_le_bytes());
            for tx in lane {
                h.update(&tx.from.to_le_bytes());
                h.update(&tx.to.to_le_bytes());
                h.update(&tx.amount.to_le_bytes());
                h.update(&tx.nonce.to_le_bytes());
            }
        }
        *h.finalize().as_bytes()
    }

    /// Shape checks the verifier does on the public data before touching the proof.
    fn well_formed(&self, n_rows: usize) -> bool {
        let k = self.addrs.len();
        let max_ts = 2 * n_rows as u32 + 1;
        k > 0
            && k < MAX_NONCE as usize
            && self.addrs.windows(2).all(|w| w[0] < w[1])
            && self.states.iter().all(|t| t.len() == k && t.iter().all(|s| s.nonce < MAX_NONCE))
            && self.final_ts.iter().all(|t| t.len() == k && t.iter().all(|&x| x <= max_ts))
            && self.lanes.iter().all(|l| l.len() <= n_rows && l.iter().all(|tx| (tx.from as usize) < k && (tx.to as usize) < k && tx.nonce < MAX_NONCE))
    }
}

// ---- column layout
const AMT: usize = 0;
const FROM_OLD: usize = 8;
const FROM_NEW: usize = 16;
const TO_OLD: usize = 24;
const TO_NEW: usize = 32;
const D1: usize = 40;
const D2: usize = 42;
const BYTE_COLS: usize = 44;
const ACTIVE: usize = 44;
const T: usize = 45;
const FROM_ID: usize = 46;
const TO_ID: usize = 47;
const NONCE: usize = 48;
const TR1: usize = 49;
const TO_NONCE: usize = 50;
const TR2: usize = 51;
const CF: usize = 52;
const CT: usize = 59;
pub const WIDTH: usize = 66;
pub const CONSTRAINTS: usize = 5 + 2 * (8 + 7);

const TAG_MEM: u32 = 1;
const TAG_TX: u32 = 2;

fn mem_values(id: u32, nonce: u32, ts: u32, bal: &[u32]) -> [u32; 11] {
    let mut v = [0u32; 11];
    v[0] = id;
    v[1] = nonce;
    v[2] = ts;
    v[3..].copy_from_slice(bal);
    v
}

fn bal_bytes(b: u64) -> [u32; 8] {
    std::array::from_fn(|k| ((b >> (8 * k)) & 0xff) as u32)
}

/// The state AIR for one batch (all 5 lanes).
pub struct StateAir<'a> {
    pub st: &'a StateStatement,
}

impl Air for StateAir<'_> {
    fn statement(&self) -> Vec<u8> {
        [b"state-transfer-v1".as_slice(), &self.st.digest()].concat()
    }
    fn width(&self) -> usize {
        WIDTH
    }
    fn byte_cols(&self) -> usize {
        BYTE_COLS
    }
    fn num_constraints(&self) -> usize {
        CONSTRAINTS
    }
    fn eval(&self, c: &[u32], nx: &[u32], pt: &Point, ch: usize, out: &mut Vec<u32>) {
        let m = RNS_MODULI[ch];
        let mul = |a: u32, b: u32| mul_mod_channel(a, b, ch);
        let two_t = add_mod(c[T], c[T], m);
        out.push(mul(c[ACTIVE], sub_mod(c[ACTIVE], 1, m)));
        out.push(mul(sub_mod(c[T], 1, m), pt.first_row));
        out.push(mul(sub_mod(sub_mod(nx[T], c[T], m), 1, m), pt.not_last));
        let d1 = add_mod(c[D1], mul(c[D1 + 1], 256), m);
        out.push(sub_mod(d1, sub_mod(sub_mod(two_t, c[TR1], m), 1, m), m));
        let d2 = add_mod(c[D2], mul(c[D2 + 1], 256), m);
        out.push(sub_mod(d2, sub_mod(two_t, c[TR2], m), m));
        // from_new + amount = from_old  and  to_old + amount = to_new, byte by byte
        for (lhs, rhs, carry) in [(FROM_NEW, FROM_OLD, CF), (TO_OLD, TO_NEW, CT)] {
            for k in 0..8 {
                let mut v = add_mod(c[lhs + k], c[AMT + k], m);
                if k > 0 {
                    v = add_mod(v, c[carry + k - 1], m);
                }
                v = sub_mod(v, c[rhs + k], m);
                if k < 7 {
                    v = sub_mod(v, mul(c[carry + k], 256), m);
                }
                out.push(v);
            }
            for k in 0..7 {
                out.push(mul(c[carry + k], sub_mod(c[carry + k], 1, m)));
            }
        }
    }
    fn num_bus(&self) -> usize {
        5
    }
    fn bus(&self, c: &[u32], ch_c: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        let mut tuples = Vec::with_capacity(5);
        self.bus_tuples(c, ch, &mut tuples);
        stark::bus_from_tuples(&tuples, ch_c, ch, out);
    }
    fn bus_tuples(&self, c: &[u32], ch: usize, out: &mut Vec<BusTuple>) {
        let m = RNS_MODULI[ch];
        let two_t = add_mod(c[T], c[T], m);
        let act = c[ACTIVE];
        let neg = sub_mod(0, act, m);
        let mem = |values: [u32; 11], weight: u32| BusTuple { tag: TAG_MEM, values: values.to_vec(), weight };
        out.push(mem(mem_values(c[FROM_ID], c[NONCE], c[TR1], &c[FROM_OLD..FROM_OLD + 8]), act));
        out.push(mem(mem_values(c[FROM_ID], add_mod(c[NONCE], 1, m), two_t, &c[FROM_NEW..FROM_NEW + 8]), neg));
        out.push(mem(mem_values(c[TO_ID], c[TO_NONCE], c[TR2], &c[TO_OLD..TO_OLD + 8]), act));
        out.push(mem(mem_values(c[TO_ID], c[TO_NONCE], add_mod(two_t, 1, m), &c[TO_NEW..TO_NEW + 8]), neg));
        let mut tx = vec![c[T], c[FROM_ID], c[TO_ID], c[NONCE]];
        tx.extend_from_slice(&c[AMT..AMT + 8]);
        out.push(BusTuple { tag: TAG_TX, values: tx, weight: neg });
    }
    /// init - final - public txs, in lane `ch`'s field.
    fn bus_sum(&self, ch_c: &Challenges, ch: usize) -> Extension4 {
        let tuples = self.public_tuples(ch);
        let dens: Vec<Extension4> = tuples.iter().map(|t| ch_c.fingerprint(t.tag, &t.values, ch)).collect();
        let Some(inv) = crate::logup::batch_inverse_ext4(&dens, ch) else {
            return Extension4::ONE; // beta hit a public fingerprint (negligible); the proof will fail
        };
        inv.iter().zip(&tuples).fold(Extension4::ZERO, |acc, (x, t)| acc.add(&x.mul_scalar(t.weight, ch), ch))
    }
    fn public_tuples(&self, ch: usize) -> Vec<BusTuple> {
        let st = self.st;
        let m = RNS_MODULI[ch];
        let mut out = Vec::new();
        for (id, s) in st.states[ch].iter().enumerate() {
            out.push(BusTuple { tag: TAG_MEM, values: mem_values(id as u32, s.nonce, 0, &bal_bytes(s.balance)).to_vec(), weight: 1 });
        }
        for (id, s) in st.states[ch + 1].iter().enumerate() {
            out.push(BusTuple { tag: TAG_MEM, values: mem_values(id as u32, s.nonce, st.final_ts[ch][id], &bal_bytes(s.balance)).to_vec(), weight: m - 1 });
        }
        for (k, tx) in st.lanes[ch].iter().enumerate() {
            let mut v = vec![k as u32 + 1, tx.from, tx.to, tx.nonce];
            v.extend_from_slice(&bal_bytes(tx.amount));
            out.push(BusTuple { tag: TAG_TX, values: v, weight: m - 1 });
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateError {
    BadNonce { tx: usize },
    InsufficientBalance { tx: usize },
    Overflow { tx: usize },
    UnknownAccount { tx: usize },
    TooManyTxs,
}

/// Prover side: executes the batch lane by lane and builds the statement and the traces.
/// With `checked = false` invalid transfers are written as they are (wrapping arithmetic, the
/// tx nonce as the read nonce), which is what a cheating prover would try; used by the tests.
pub fn build(addrs: &[Address], old: &[AccountState], txs: &[Transfer], log_rows: u32, checked: bool) -> Result<(StateStatement, [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]), StateError> {
    assert!(log_rows <= MAX_LOG_ROWS);
    let n_rows = 1usize << log_rows;
    if txs.len() > n_rows * DEFAULT_RNS_CHANNELS {
        return Err(StateError::TooManyTxs);
    }
    let k = addrs.len();
    let mut cur = old.to_vec();
    let mut states: Vec<Vec<AccountState>> = vec![cur.clone()];
    let mut final_ts: Vec<Vec<u32>> = Vec::new();
    let mut lanes: Vec<Vec<Transfer>> = Vec::new();
    let mut traces: Vec<Vec<Vec<u32>>> = Vec::new();
    for lane in 0..DEFAULT_RNS_CHANNELS {
        let slice: Vec<Transfer> = txs.iter().skip(lane * n_rows).take(n_rows).copied().collect();
        let mut last = vec![0u32; k];
        let mut trace = Vec::with_capacity(n_rows);
        for r in 0..n_rows {
            let t = r as u32 + 1;
            let mut row = vec![0u32; WIDTH];
            row[T] = t;
            if let Some(tx) = slice.get(r) {
                let gi = lane * n_rows + r;
                let (f, to) = (tx.from as usize, tx.to as usize);
                if f >= k || to >= k {
                    return Err(StateError::UnknownAccount { tx: gi });
                }
                let fs = cur[f];
                if checked && fs.nonce != tx.nonce {
                    return Err(StateError::BadNonce { tx: gi });
                }
                if checked && fs.balance < tx.amount {
                    return Err(StateError::InsufficientBalance { tx: gi });
                }
                let f_new = fs.balance.wrapping_sub(tx.amount);
                row[ACTIVE] = 1;
                row[FROM_ID] = tx.from;
                row[TO_ID] = tx.to;
                row[NONCE] = tx.nonce;
                row[TR1] = last[f];
                put_add(&mut row, f_new, tx.amount, FROM_NEW, CF);
                row[FROM_OLD..FROM_OLD + 8].copy_from_slice(&bal_bytes(fs.balance));
                row[AMT..AMT + 8].copy_from_slice(&bal_bytes(tx.amount));
                cur[f] = AccountState { balance: f_new, nonce: tx.nonce.wrapping_add(1) };
                last[f] = 2 * t;

                let ts = cur[to];
                let Some(t_new) = ts.balance.checked_add(tx.amount).or(if checked { None } else { Some(ts.balance.wrapping_add(tx.amount)) }) else {
                    return Err(StateError::Overflow { tx: gi });
                };
                row[TO_NONCE] = ts.nonce;
                row[TR2] = last[to];
                put_add(&mut row, ts.balance, tx.amount, TO_OLD, CT);
                row[TO_NEW..TO_NEW + 8].copy_from_slice(&bal_bytes(t_new));
                cur[to] = AccountState { balance: t_new, nonce: ts.nonce };
                last[to] = 2 * t + 1;
            } else {
                row[TR1] = 2 * t - 1;
                row[TR2] = 2 * t;
            }
            let d1 = 2 * t - 1 - row[TR1];
            let d2 = 2 * t - row[TR2];
            row[D1] = d1 & 0xff;
            row[D1 + 1] = d1 >> 8;
            row[D2] = d2 & 0xff;
            row[D2 + 1] = d2 >> 8;
            trace.push(row);
        }
        states.push(cur.clone());
        final_ts.push(last);
        lanes.push(slice);
        traces.push(trace);
    }
    let st = StateStatement {
        addrs: addrs.to_vec(),
        states: states.try_into().unwrap(),
        final_ts: final_ts.try_into().unwrap(),
        lanes: lanes.try_into().unwrap(),
    };
    Ok((st, traces.try_into().unwrap()))
}

/// Writes x's bytes at `x_col` and the byte carries of x + y at `carry_col`.
fn put_add(row: &mut [u32], x: u64, y: u64, x_col: usize, carry_col: usize) {
    let (xb, yb) = (bal_bytes(x), bal_bytes(y));
    let mut c = 0u32;
    for k in 0..8 {
        row[x_col + k] = xb[k];
        let s = xb[k] + yb[k] + c;
        c = s >> 8;
        if k < 7 {
            row[carry_col + k] = c;
        }
    }
}

pub fn params(txs: usize, log_blowup: u32, num_queries: usize) -> StarkParams {
    let log_rows = txs.div_ceil(DEFAULT_RNS_CHANNELS).max(256).next_power_of_two().trailing_zeros();
    StarkParams { log_rows, log_blowup, num_queries }
}

pub fn prove(st: &StateStatement, traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS], params: &StarkParams, t: &mut Transcript) -> StarkProof {
    stark::prove_air(&StateAir { st }, traces, st.num_txs(), params, t)
}

/// Verifies that `st` takes `old_root` to `new_root` and that the proof is valid for it.
pub fn verify(st: &StateStatement, old_root: &[u8; 32], new_root: &[u8; 32], proof: &StarkProof, params: &StarkParams, t: &mut Transcript) -> bool {
    let n_rows = 1usize << params.log_rows;
    params.log_rows <= MAX_LOG_ROWS
        && st.well_formed(n_rows)
        && &st.old_root() == old_root
        && &st.new_root() == new_root
        && proof.rows == st.num_txs()
        && stark::verify_air(&StateAir { st }, proof, n_rows * DEFAULT_RNS_CHANNELS, params, t)
}

#[cfg(test)]
mod tests {
    use super::*;

    const P: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };

    fn setup(n_tx: usize) -> (Vec<Address>, Vec<AccountState>, Vec<Transfer>) {
        let k = 12u32;
        let addrs: Vec<Address> = (0..k as u8).map(|i| [i + 1; 20]).collect();
        let old: Vec<AccountState> = (0..k).map(|i| AccountState { balance: 1_000_000 + i as u64, nonce: 0 }).collect();
        let mut nonces = vec![0u32; k as usize];
        let txs = (0..n_tx)
            .map(|i| {
                let from = (i as u32 * 5) % k;
                let to = (from + 1 + (i as u32 % (k - 1))) % k;
                let tx = Transfer { from, to, amount: 1 + (i as u64 * 7919) % 5000, nonce: nonces[from as usize] };
                nonces[from as usize] += 1;
                tx
            })
            .collect();
        (addrs, old, txs)
    }

    fn prove_and_verify(st: &StateStatement, traces: &[Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS], old: [u8; 32], new: [u8; 32]) -> bool {
        let proof = prove(st, traces, &P, &mut Transcript::new(b"state-test"));
        verify(st, &old, &new, &proof, &P, &mut Transcript::new(b"state-test"))
    }

    #[test]
    fn honest_batch_across_all_lanes_verifies() {
        let (addrs, old, txs) = setup(5 * 256 - 3);
        let (st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        assert!(st.lanes.iter().all(|l| !l.is_empty()), "every lane is used");
        let total: u64 = st.states[5].iter().map(|s| s.balance).sum();
        assert_eq!(total, old.iter().map(|s| s.balance).sum::<u64>(), "transfers conserve value");
        assert!(prove_and_verify(&st, &traces, st.old_root(), st.new_root()));
    }

    #[test]
    fn self_transfer_and_partial_lane() {
        let (addrs, old, _) = setup(0);
        let txs = vec![Transfer { from: 2, to: 2, amount: 10, nonce: 0 }, Transfer { from: 2, to: 3, amount: 5, nonce: 1 }];
        let (st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        assert_eq!(st.states[5][2], AccountState { balance: old[2].balance - 5, nonce: 2 });
        assert!(prove_and_verify(&st, &traces, st.old_root(), st.new_root()));
    }

    #[test]
    fn forged_new_root_is_rejected() {
        let (addrs, old, txs) = setup(300);
        let (mut st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        let honest_new = st.new_root();
        // Credit account 0 with extra funds in the claimed final table.
        st.states[5][0].balance += 1_000;
        assert!(!prove_and_verify(&st, &traces, st.old_root(), st.new_root()));
        // And the honest statement does not verify against a different root.
        let (st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        assert!(!prove_and_verify(&st, &traces, st.old_root(), [7u8; 32]));
        assert!(prove_and_verify(&st, &traces, st.old_root(), honest_new));
    }

    #[test]
    fn overspending_is_rejected() {
        let (addrs, old, mut txs) = setup(40);
        txs[10].amount = old[txs[10].from as usize].balance + 1; // more than the sender has
        assert_eq!(build(&addrs, &old, &txs, 8, true).unwrap_err(), StateError::InsufficientBalance { tx: 10 });
        let (st, traces) = build(&addrs, &old, &txs, 8, false).unwrap();
        assert!(!prove_and_verify(&st, &traces, st.old_root(), st.new_root()));
    }

    #[test]
    fn wrong_nonce_and_replay_are_rejected() {
        let (addrs, old, mut txs) = setup(40);
        txs[7].nonce += 1;
        assert!(matches!(build(&addrs, &old, &txs, 8, true), Err(StateError::BadNonce { tx: 7 })));
        let (st, traces) = build(&addrs, &old, &txs, 8, false).unwrap();
        assert!(!prove_and_verify(&st, &traces, st.old_root(), st.new_root()));

        let (addrs, old, mut txs) = setup(40);
        let dup = txs[3];
        txs.insert(4, dup); // replay with the same nonce
        let (st, traces) = build(&addrs, &old, &txs, 8, false).unwrap();
        assert!(!prove_and_verify(&st, &traces, st.old_root(), st.new_root()));
    }

    #[test]
    fn statement_must_match_the_trace() {
        let (addrs, old, txs) = setup(100);
        let (st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        // Dropping a transaction from the public list (censoring it from the blob).
        let mut st2 = st.clone();
        st2.lanes[0].pop();
        assert!(!prove_and_verify(&st2, &traces, st2.old_root(), st2.new_root()));
        // Changing an amount in the public list.
        let mut st3 = st.clone();
        st3.lanes[0][5].amount += 1;
        assert!(!prove_and_verify(&st3, &traces, st3.old_root(), st3.new_root()));
        // Swapping two transactions (order is bound by the row counter).
        let mut st4 = st.clone();
        st4.lanes[0].swap(1, 2);
        assert!(!prove_and_verify(&st4, &traces, st4.old_root(), st4.new_root()));
    }

    #[test]
    fn rejections_come_from_the_proof_not_the_shape_checks() {
        let (addrs, old, mut txs) = setup(40);
        txs[10].amount = old[txs[10].from as usize].balance + 1;
        let (st, _) = build(&addrs, &old, &txs, 8, false).unwrap();
        assert!(st.well_formed(256), "the overspend statement is well formed; only the AIR rejects it");
    }

    #[test]
    fn tampering_any_kind_of_cell_is_rejected() {
        let (addrs, old, txs) = setup(60);
        let (st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        for col in [AMT + 1, FROM_OLD, FROM_NEW + 3, TO_NEW, D1, ACTIVE, T, FROM_ID, NONCE, TR1, TO_NONCE, CF, CT + 2] {
            let mut bad = traces.clone();
            bad[0][17][col] = (bad[0][17][col] + 1) % 256;
            assert!(!prove_and_verify(&st, &bad, st.old_root(), st.new_root()), "column {col}");
        }
        // A padding row switched on.
        let mut bad = traces.clone();
        bad[4][200][ACTIVE] = 1;
        assert!(!prove_and_verify(&st, &bad, st.old_root(), st.new_root()));
    }

    #[test]
    fn poseidon_mode_proves_and_rejects() {
        use crate::hash::HashMode;
        let (addrs, old, txs) = setup(300);
        let (st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        let t = || Transcript::with_mode(b"state-test", HashMode::Poseidon);
        let t0 = std::time::Instant::now();
        let proof = prove(&st, &traces, &P, &mut t());
        eprintln!("poseidon state proof: {:?}", t0.elapsed());
        assert!(verify(&st, &st.old_root(), &st.new_root(), &proof, &P, &mut t()));
        // A Blake3 verifier does not accept a Poseidon proof, and tampering is caught.
        assert!(!verify(&st, &st.old_root(), &st.new_root(), &proof, &P, &mut Transcript::new(b"state-test")));
        let mut bad = proof.clone();
        bad.openings[0][0].main[1][3] ^= 1;
        assert!(!verify(&st, &st.old_root(), &st.new_root(), &bad, &P, &mut t()));
    }

    #[test]
    fn poseidon2_mode_proves_and_rejects() {
        use crate::hash::HashMode;
        let (addrs, old, txs) = setup(300);
        let (st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        let t = || Transcript::with_mode(b"state-test", HashMode::Poseidon2);
        let t0 = std::time::Instant::now();
        let proof = prove(&st, &traces, &P, &mut t());
        eprintln!("poseidon2 state proof: {:?}", t0.elapsed());
        assert!(verify(&st, &st.old_root(), &st.new_root(), &proof, &P, &mut t()));
        assert!(!verify(&st, &st.old_root(), &st.new_root(), &proof, &P, &mut Transcript::with_mode(b"state-test", HashMode::Poseidon)));
        let mut bad = proof.clone();
        bad.openings[2][1].aux[4][7].c[0] ^= 1;
        assert!(!verify(&st, &st.old_root(), &st.new_root(), &bad, &P, &mut t()));
    }

    /// Recursion path: one proof per lane, each with Poseidon2 over its own field.
    #[test]
    fn per_lane_proofs_each_verify_in_their_own_field() {
        use crate::hash::HashMode;
        let (addrs, old, txs) = setup(300);
        let (st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        let t0 = std::time::Instant::now();
        let proofs = stark::prove_air_lanes(&StateAir { st: &st }, &traces, st.num_txs(), &P, b"state-test");
        eprintln!("5 per-lane state proofs: {:?}", t0.elapsed());
        for (j, pr) in proofs.iter().enumerate() {
            let t = || Transcript::with_mode(b"state-test", HashMode::Lane(j as u8));
            assert!(verify(&st, &st.old_root(), &st.new_root(), pr, &P, &mut t()), "lane {j}");
            let mut bad = pr.clone();
            bad.openings[1][0].aux[j][2].c[1] ^= 1;
            assert!(!verify(&st, &st.old_root(), &st.new_root(), &bad, &P, &mut t()));
            let mut other = st.clone();
            other.final_ts[j][0] += 2;
            assert!(!verify(&other, &other.old_root(), &other.new_root(), pr, &P, &mut t()));
        }
    }

    #[test]
    fn proof_from_one_lane_split_cannot_be_reused() {
        let (addrs, old, txs) = setup(100);
        let (st, traces) = build(&addrs, &old, &txs, 8, true).unwrap();
        let proof = prove(&st, &traces, &P, &mut Transcript::new(b"state-test"));
        let mut other = st.clone();
        other.final_ts[0][0] += 2;
        assert!(!verify(&other, &other.old_root(), &other.new_root(), &proof, &P, &mut Transcript::new(b"state-test")));
    }
}
