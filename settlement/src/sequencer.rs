//! Minimal sequencer: validates transactions, applies them immediately and returns a soft
//! confirmation (PDF goal: < 200 ms in the app), then seals batches for proving and settlement.
//!
//! Every sealed batch carries what the state AIR (`ss_rap_v2::state`) needs to prove it: the
//! address table, the accounts at the start of the batch and the transfers by account index.
//!
//! Every transaction is signed by its sender (secp256k1 ECDSA, Ethereum addresses: the last
//! 20 bytes of keccak256 of the public key) over a domain-separated hash that includes the chain
//! id; `submit` recovers the signer and refuses the transaction unless it is `from`. The
//! signature is checked here, not yet inside the STARK: a malicious sequencer could still sign
//! nothing and prove a transfer (proving signatures in-circuit is a later step).
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

/// Domain of the transaction signatures.
pub const TX_DOMAIN: &[u8] = b"SS-RAP-v2 transfer";
/// Bytes of one transaction in the blob: from, to, amount, nonce, kind, signature (r, s, v).
pub const TX_BYTES: usize = 20 + 20 + 8 + 4 + 1 + 65;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tx {
    pub from: Address,
    pub to: Address,
    pub amount: u64,
    pub nonce: u32,
    pub kind: TxKind,
    /// r (32) || s (32) || recovery id (1), over `signing_hash(chain_id)`.
    pub sig: [u8; 65],
}

/// The Ethereum address of a secp256k1 public key.
pub fn address_of(key: &k256::ecdsa::VerifyingKey) -> Address {
    let p = key.to_encoded_point(false);
    let h = keccak256(&p.as_bytes()[1..]);
    h[12..].try_into().unwrap()
}

/// A deterministic key for tests and examples (NOT for real funds).
pub fn dev_key(i: u64) -> k256::ecdsa::SigningKey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&(i + 1).to_be_bytes());
    b[31] = 1;
    k256::ecdsa::SigningKey::from_slice(&b).expect("valid scalar")
}

impl Tx {
    /// A transaction from the owner of `key`, signed for `chain_id`.
    pub fn signed(key: &k256::ecdsa::SigningKey, to: Address, amount: u64, nonce: u32, kind: TxKind, chain_id: u64) -> Self {
        let mut tx = Tx { from: address_of(key.verifying_key()), to, amount, nonce, kind, sig: [0; 65] };
        let (sig, rec) = key.sign_prehash_recoverable(&tx.signing_hash(chain_id)).expect("sign");
        tx.sig[..64].copy_from_slice(&sig.to_bytes());
        tx.sig[64] = rec.to_byte();
        tx
    }

    fn body(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(TX_BYTES);
        v.extend_from_slice(&self.from);
        v.extend_from_slice(&self.to);
        v.extend_from_slice(&self.amount.to_be_bytes());
        v.extend_from_slice(&self.nonce.to_be_bytes());
        v.push(match self.kind {
            TxKind::Transfer => 0,
            TxKind::Swap => 1,
        });
        v
    }

    /// What the sender signs: keccak256(domain || chain id || body).
    pub fn signing_hash(&self, chain_id: u64) -> [u8; 32] {
        let mut v = TX_DOMAIN.to_vec();
        v.extend_from_slice(&chain_id.to_be_bytes());
        v.extend(self.body());
        keccak256(&v)
    }

    /// The address that signed this transaction for `chain_id`, if the signature is valid.
    pub fn signer(&self, chain_id: u64) -> Option<Address> {
        use k256::ecdsa::{RecoveryId, Signature, VerifyingKey};
        let sig = Signature::from_slice(&self.sig[..64]).ok()?;
        // only low-s signatures: one valid signature per transaction
        if sig.normalize_s().is_some() {
            return None;
        }
        let rec = RecoveryId::from_byte(self.sig[64])?;
        let key = VerifyingKey::recover_from_prehash(&self.signing_hash(chain_id), &sig, rec).ok()?;
        Some(address_of(&key))
    }

    /// The transaction as posted in the blob (`TX_BYTES` bytes).
    pub fn encode(&self) -> Vec<u8> {
        let mut v = self.body();
        v.extend_from_slice(&self.sig);
        v
    }

    pub fn decode(b: &[u8]) -> Option<Self> {
        if b.len() != TX_BYTES {
            return None;
        }
        let kind = match b[52] {
            0 => TxKind::Transfer,
            1 => TxKind::Swap,
            _ => return None,
        };
        Some(Tx {
            from: b[0..20].try_into().unwrap(),
            to: b[20..40].try_into().unwrap(),
            amount: u64::from_be_bytes(b[40..48].try_into().unwrap()),
            nonce: u32::from_be_bytes(b[48..52].try_into().unwrap()),
            kind,
            sig: b[53..].try_into().unwrap(),
        })
    }

    pub fn hash(&self) -> [u8; 32] {
        keccak256(&self.encode())
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
    /// The signature is malformed or was not made by `from` for this chain.
    BadSignature,
    /// Zero-amount transfers are refused: they would let anyone grow the state for free.
    ZeroAmount,
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
    /// The transactions posted to L1 as the EIP-4844 blob: every field and signature
    /// (`TX_BYTES` each), so that anyone can re-execute the batch from L1 data alone.
    pub fn blob_data(&self) -> Vec<u8> {
        self.txs.iter().flat_map(|t| t.encode()).collect()
    }
    /// The transactions as transfers between indices of `addrs`.
    /// The transactions of a blob (`blob_data`), or None if it is malformed.
    pub fn decode_blob(blob: &[u8]) -> Option<Vec<Tx>> {
        if blob.len() % TX_BYTES != 0 {
            return None;
        }
        blob.chunks(TX_BYTES).map(Tx::decode).collect()
    }

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
    /// Chain the signatures are bound to (the settlement contract's chain).
    pub chain_id: u64,
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
            chain_id: 31337,
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
        if tx.signer(self.chain_id) != Some(tx.from) {
            return Err(SeqError::BadSignature);
        }
        if tx.from == tx.to {
            return Err(SeqError::SelfTransfer);
        }
        if tx.amount == 0 {
            return Err(SeqError::ZeroAmount);
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

    const CHAIN: u64 = 31337;

    fn addr(i: u64) -> Address {
        address_of(dev_key(i).verifying_key())
    }

    fn tx(i: u64, to: Address, amount: u64, nonce: u32, kind: TxKind) -> Tx {
        Tx::signed(&dev_key(i), to, amount, nonce, kind, CHAIN)
    }

    #[test]
    fn transfers_update_state_and_roots_chain() {
        let mut s = Sequencer::new(&[(addr(1), 1000), (addr(2), 0)], 10, FeeSchedule::default());
        let r0 = s.state_root();
        let c = s.submit(tx(1, addr(2), 300, 0, TxKind::Transfer)).unwrap();
        assert_eq!(c.fee_micro_usd, 6_000);
        assert_eq!((s.balance(&addr(1)), s.balance(&addr(2))), (700, 300));
        let b1 = s.seal();
        assert_eq!(b1.old_state_root, r0);
        assert_ne!(b1.new_state_root, r0);
        s.submit(tx(2, addr(1), 100, 0, TxKind::Swap)).unwrap();
        let b2 = s.seal();
        assert_eq!(b2.batch_number, 2);
        assert_eq!(b2.old_state_root, b1.new_state_root, "batches must chain");
    }

    #[test]
    fn invalid_transactions_are_refused() {
        let mut s = Sequencer::new(&[(addr(1), 10)], 1, FeeSchedule::default());
        let t = |amount, nonce| tx(1, addr(2), amount, nonce, TxKind::Transfer);
        assert_eq!(s.submit(t(5, 1)).unwrap_err(), SeqError::BadNonce { expected: 0, got: 1 });
        assert_eq!(s.submit(t(50, 0)).unwrap_err(), SeqError::InsufficientBalance);
        assert_eq!(s.submit(tx(1, addr(1), 1, 0, TxKind::Transfer)).unwrap_err(), SeqError::SelfTransfer);
        assert_eq!(s.submit(t(0, 0)).unwrap_err(), SeqError::ZeroAmount);
        s.submit(t(5, 0)).unwrap();
        assert_eq!(s.submit(t(1, 1)).unwrap_err(), SeqError::BatchFull);
    }

    #[test]
    fn replay_is_refused() {
        let mut s = Sequencer::new(&[(addr(1), 10)], 10, FeeSchedule::default());
        let t = tx(1, addr(2), 1, 0, TxKind::Transfer);
        s.submit(t.clone()).unwrap();
        assert!(matches!(s.submit(t), Err(SeqError::BadNonce { .. })));
    }

    /// Audit finding: anyone could move anyone's funds (no sender authentication).
    #[test]
    fn only_the_owner_can_spend() {
        let mut s = Sequencer::new(&[(addr(1), 1000)], 10, FeeSchedule::default());
        // the attacker (key 9) signs a transfer out of account 1
        let mut forged = tx(9, addr(9), 1000, 0, TxKind::Transfer);
        forged.from = addr(1);
        assert_eq!(s.submit(forged).unwrap_err(), SeqError::BadSignature);
        // no signature at all
        let mut unsigned = tx(1, addr(9), 1000, 0, TxKind::Transfer);
        unsigned.sig = [0; 65];
        assert_eq!(s.submit(unsigned).unwrap_err(), SeqError::BadSignature);
        // a signature of another amount, or for another chain
        let mut changed = tx(1, addr(9), 1, 0, TxKind::Transfer);
        changed.amount = 1000;
        assert_eq!(s.submit(changed).unwrap_err(), SeqError::BadSignature);
        let other_chain = Tx::signed(&dev_key(1), addr(9), 1000, 0, TxKind::Transfer, 1);
        assert_eq!(s.submit(other_chain).unwrap_err(), SeqError::BadSignature);
        // the high-s twin of a valid signature
        let good = tx(1, addr(9), 10, 0, TxKind::Transfer);
        let sig = k256::ecdsa::Signature::from_slice(&good.sig[..64]).unwrap();
        let (r, sv) = sig.split_scalars();
        let high = k256::ecdsa::Signature::from_scalars(r.to_bytes(), (-*sv).to_bytes()).unwrap();
        let mut twin = good.clone();
        twin.sig[..64].copy_from_slice(&high.to_bytes());
        twin.sig[64] ^= 1;
        assert_eq!(s.submit(twin).unwrap_err(), SeqError::BadSignature);
        assert_eq!(s.balance(&addr(1)), 1000);
        s.submit(good).unwrap();
        assert_eq!(s.balance(&addr(9)), 10);
    }

    /// Audit finding: the blob held only transaction hashes.
    #[test]
    fn the_blob_holds_every_transaction() {
        let mut s = Sequencer::new(&[(addr(1), 1000), (addr(2), 1000)], 10, FeeSchedule::default());
        s.submit(tx(1, addr(2), 7, 0, TxKind::Transfer)).unwrap();
        s.submit(tx(2, addr(3), 9, 0, TxKind::Swap)).unwrap();
        let b = s.seal();
        let blob = b.blob_data();
        assert_eq!(blob.len(), 2 * TX_BYTES);
        let txs = SealedBatch::decode_blob(&blob).unwrap();
        assert_eq!(txs, b.txs);
        assert!(txs.iter().all(|t| t.signer(CHAIN) == Some(t.from)), "anyone can re-check the signatures");
        // 1000 transfers fit in one blob (4096 field elements x 31 usable bytes)
        assert!(1000 * TX_BYTES <= 4096 * 31);
        assert!(SealedBatch::decode_blob(&blob[1..]).is_none());
    }
}
