//! Minimal sequencer: validates transactions, applies them immediately and returns a soft
//! confirmation (PDF goal: < 200 ms in the app), then seals batches for proving and settlement.
//!
//! Every sealed batch carries what the state AIR (`ss_rap_v2::state`) needs to prove it: the
//! address table, the accounts at the start of the batch and the transfers by account index.
//!
//! MVP simplifications, each with its production replacement:
//! - state root = Blake3 over the sorted non-empty accounts (`state::state_root`); production
//!   uses a sparse Merkle tree so that users can get inclusion proofs and the escape hatch works.
//! - soft confirmations are returned in-process; production signs them with the sequencer key
//!   (HSM) and backs them with a bond (docs/INSTITUCIONAL.md, A.2).
//! - fees are recorded per transaction in micro-USD; production collects them through a
//!   stablecoin paymaster.

use crate::fees::{FeeSchedule, TxKind};
use crate::public_input::keccak256;
pub use ss_rap_v2::state::{AccountState, Address};
use ss_rap_v2::state::{state_root, Transfer, MAX_NONCE};
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tx {
    pub from: Address,
    pub to: Address,
    pub amount: u64,
    pub nonce: u32,
    pub kind: TxKind,
}

impl Tx {
    pub fn hash(&self) -> [u8; 32] {
        let mut v = Vec::with_capacity(20 + 20 + 8 + 4 + 1);
        v.extend_from_slice(&self.from);
        v.extend_from_slice(&self.to);
        v.extend_from_slice(&self.amount.to_be_bytes());
        v.extend_from_slice(&self.nonce.to_be_bytes());
        v.push(match self.kind {
            TxKind::Transfer => 0,
            TxKind::Swap => 1,
        });
        keccak256(&v)
    }
}

#[derive(Clone, Debug)]
pub struct SoftConfirmation {
    pub tx_hash: [u8; 32],
    pub batch_number: u64,
    pub index: usize,
    pub fee_micro_usd: u64,
    pub latency: Duration,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeqError {
    BadNonce { expected: u32, got: u32 },
    InsufficientBalance,
    BalanceOverflow,
    NonceExhausted,
    BatchFull,
    SelfTransfer,
}

#[derive(Clone, Debug)]
pub struct SealedBatch {
    pub batch_number: u64,
    pub old_state_root: [u8; 32],
    pub new_state_root: [u8; 32],
    pub txs: Vec<Tx>,
    pub fees_micro_usd: Vec<u64>,
    /// Sorted addresses of every account that exists or is touched in this batch.
    pub addrs: Vec<Address>,
    /// Their state at the start of the batch (empty for accounts created by the batch).
    pub old_states: Vec<AccountState>,
}

impl SealedBatch {
    pub fn kinds(&self) -> Vec<TxKind> {
        self.txs.iter().map(|t| t.kind).collect()
    }
    /// Serialized transaction data posted to L1 as the EIP-4844 blob.
    pub fn blob_data(&self) -> Vec<u8> {
        self.txs.iter().flat_map(|t| t.hash()).collect()
    }
    /// The transactions as transfers between indices of `addrs`.
    pub fn transfers(&self) -> Vec<Transfer> {
        let id = |a: &Address| self.addrs.binary_search(a).expect("address in table") as u32;
        self.txs.iter().map(|t| Transfer { from: id(&t.from), to: id(&t.to), amount: t.amount, nonce: t.nonce }).collect()
    }
}

pub struct Sequencer {
    accounts: BTreeMap<Address, AccountState>,
    batch_start: BTreeMap<Address, AccountState>,
    pending: Vec<Tx>,
    pending_fees: Vec<u64>,
    batch_number: u64,
    batch_start_root: [u8; 32],
    pub max_batch: usize,
    pub schedule: FeeSchedule,
    /// Current cost per tx (micro-USD), updated from the cost model; drives the fee floor.
    pub cost_per_tx_micro_usd: u64,
}

impl Sequencer {
    pub fn new(genesis: &[(Address, u64)], max_batch: usize, schedule: FeeSchedule) -> Self {
        let accounts: BTreeMap<Address, AccountState> = genesis.iter().map(|(a, b)| (*a, AccountState { balance: *b, nonce: 0 })).collect();
        let mut s = Self {
            batch_start: accounts.clone(),
            accounts,
            pending: Vec::new(),
            pending_fees: Vec::new(),
            batch_number: 1,
            batch_start_root: [0; 32],
            max_batch,
            schedule,
            cost_per_tx_micro_usd: 0,
        };
        s.batch_start_root = s.state_root();
        s
    }

    pub fn state_root(&self) -> [u8; 32] {
        let (addrs, states): (Vec<Address>, Vec<AccountState>) = self.accounts.iter().map(|(a, s)| (*a, *s)).unzip();
        state_root(&addrs, &states)
    }

    pub fn balance(&self, a: &Address) -> u64 {
        self.accounts.get(a).map(|x| x.balance).unwrap_or(0)
    }

    pub fn pending_len(&self) -> usize {
        self.pending.len()
    }

    /// Validate, apply and soft-confirm one transaction.
    pub fn submit(&mut self, tx: Tx) -> Result<SoftConfirmation, SeqError> {
        let t0 = Instant::now();
        if self.pending.len() >= self.max_batch {
            return Err(SeqError::BatchFull);
        }
        if tx.from == tx.to {
            return Err(SeqError::SelfTransfer);
        }
        let from = self.accounts.get(&tx.from).cloned().unwrap_or_default();
        if tx.nonce != from.nonce {
            return Err(SeqError::BadNonce { expected: from.nonce, got: tx.nonce });
        }
        if from.balance < tx.amount {
            return Err(SeqError::InsufficientBalance);
        }
        if from.nonce + 1 >= MAX_NONCE {
            return Err(SeqError::NonceExhausted);
        }
        if self.balance(&tx.to).checked_add(tx.amount).is_none() {
            return Err(SeqError::BalanceOverflow);
        }
        let fee = self.schedule.price(tx.kind, self.cost_per_tx_micro_usd);
        let f = self.accounts.entry(tx.from).or_default();
        f.balance -= tx.amount;
        f.nonce += 1;
        self.accounts.entry(tx.to).or_default().balance += tx.amount;
        let hash = tx.hash();
        self.pending.push(tx);
        self.pending_fees.push(fee);
        Ok(SoftConfirmation {
            tx_hash: hash,
            batch_number: self.batch_number,
            index: self.pending.len() - 1,
            fee_micro_usd: fee,
            latency: t0.elapsed(),
        })
    }

    /// Close the current batch and start the next one.
    pub fn seal(&mut self) -> SealedBatch {
        let new_root = self.state_root();
        let txs = std::mem::take(&mut self.pending);
        let mut addrs: BTreeSet<Address> = self.batch_start.keys().copied().collect();
        addrs.extend(txs.iter().flat_map(|t| [t.from, t.to]));
        let addrs: Vec<Address> = addrs.into_iter().collect();
        let old_states = addrs.iter().map(|a| self.batch_start.get(a).copied().unwrap_or_default()).collect();
        let batch = SealedBatch {
            batch_number: self.batch_number,
            old_state_root: self.batch_start_root,
            new_state_root: new_root,
            txs,
            fees_micro_usd: std::mem::take(&mut self.pending_fees),
            addrs,
            old_states,
        };
        self.batch_number += 1;
        self.batch_start_root = new_root;
        self.batch_start = self.accounts.clone();
        batch
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn addr(i: u8) -> Address {
        [i; 20]
    }

    #[test]
    fn transfers_update_state_and_roots_chain() {
        let mut s = Sequencer::new(&[(addr(1), 1000), (addr(2), 0)], 10, FeeSchedule::default());
        let r0 = s.state_root();
        let c = s.submit(Tx { from: addr(1), to: addr(2), amount: 300, nonce: 0, kind: TxKind::Transfer }).unwrap();
        assert_eq!(c.fee_micro_usd, 6_000);
        assert_eq!((s.balance(&addr(1)), s.balance(&addr(2))), (700, 300));
        let b1 = s.seal();
        assert_eq!(b1.old_state_root, r0);
        assert_ne!(b1.new_state_root, r0);
        s.submit(Tx { from: addr(2), to: addr(1), amount: 100, nonce: 0, kind: TxKind::Swap }).unwrap();
        let b2 = s.seal();
        assert_eq!(b2.batch_number, 2);
        assert_eq!(b2.old_state_root, b1.new_state_root, "batches must chain");
    }

    #[test]
    fn invalid_transactions_are_refused() {
        let mut s = Sequencer::new(&[(addr(1), 10)], 1, FeeSchedule::default());
        let t = |amount, nonce| Tx { from: addr(1), to: addr(2), amount, nonce, kind: TxKind::Transfer };
        assert_eq!(s.submit(t(5, 1)).unwrap_err(), SeqError::BadNonce { expected: 0, got: 1 });
        assert_eq!(s.submit(t(50, 0)).unwrap_err(), SeqError::InsufficientBalance);
        let selfie = Tx { from: addr(1), to: addr(1), amount: 1, nonce: 0, kind: TxKind::Transfer };
        assert_eq!(s.submit(selfie).unwrap_err(), SeqError::SelfTransfer);
        s.submit(t(5, 0)).unwrap();
        assert_eq!(s.submit(t(1, 1)).unwrap_err(), SeqError::BatchFull);
    }

    #[test]
    fn replay_is_refused() {
        let mut s = Sequencer::new(&[(addr(1), 10)], 10, FeeSchedule::default());
        let tx = Tx { from: addr(1), to: addr(2), amount: 1, nonce: 0, kind: TxKind::Transfer };
        s.submit(tx.clone()).unwrap();
        assert!(matches!(s.submit(tx), Err(SeqError::BadNonce { .. })));
    }
}
