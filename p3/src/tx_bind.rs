//! Audit H-01 (b): the blob's bytes are the transactions the lanes executed.
//!
//! Blob layout (`settlement::blob::txs_to_blobs`): every transaction takes 4 field elements of
//! 31 data bytes (124 bytes: the 118-byte `Tx::encode`, then 6 zero bytes), so a blob holds
//! `TXS_PER_BLOB` = 1024 slots and transaction g of the batch is slot g (blob g / 1024). An empty
//! slot is all zero. The batch executes transaction g in lane g / 2^log_rows, row g mod
//! 2^log_rows (`ss_rap_v2::state::build`), so the position in the blob fixes where it runs.
//!
//! `TxAir` has one row per slot. Per row it
//! - receives the slot's 4 elements from `BlobEvalAir` on the "elem" bus, (4 r + e, 31 bytes);
//!   the blob AIR sends every element of every blob slot once, so all bytes of the blob are
//!   consumed;
//! - is active or not: inactive rows hold only zero bytes, so a blob can't carry a transaction
//!   the lanes did not execute;
//! - when active, sends (lane, t, from id, to id, amount bytes, nonce) on the "tx" bus, which
//!   every active lane row receives (so every executed transfer is in the blob, at its place),
//!   and (id, address) for sender and recipient on the "addr" bus to `AddrAir`, the statement's
//!   address table (public, as periodic columns).
//!
//! The signature bytes (53..118) are carried but not checked here: that is audit C-02.

use crate::blob_eval::ROWS;
use num_bigint::BigUint;
use p3_air::{Air, AirBuilder, BaseAir, PermutationAirBuilder, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;
use ss_rap_v2::state::{Address, StateStatement, MAX_NONCE};
use ss_rap_v2::DEFAULT_RNS_CHANNELS;
use std::borrow::Cow;

/// Bytes of an encoded transaction (`Tx::encode`): from 20, to 20, amount 8 (BE), nonce 4 (BE),
/// kind 1, signature 65.
pub const TX_BYTES: usize = 118;
/// Field elements per transaction slot.
pub const ELEMS: usize = 4;
/// Data bytes per element.
pub const ELEM_BYTES: usize = 31;
/// Bytes of a slot.
pub const SLOT_BYTES: usize = ELEMS * ELEM_BYTES;
/// Transaction slots of one blob.
pub const TXS_PER_BLOB: usize = ROWS / ELEMS;
const LOG_TXS: usize = 10;
const _: () = assert!(1 << LOG_TXS == TXS_PER_BLOB);

const AMOUNT: usize = 40;
const NONCE: usize = 48;
const KIND: usize = 52;

// main columns
const ACT: usize = SLOT_BYTES;
const FROM_ID: usize = ACT + 1;
const TO_ID: usize = ACT + 2;
const WIDTH: usize = ACT + 3;
// preprocessed: row index, lane, row in the lane (t = row + 1), whether the slot can run
const PRE_R: usize = 0;
const PRE_LANE: usize = 1;
const PRE_T: usize = 2;
const PRE_CAN: usize = 3;
const PRE_WIDTH: usize = 4;

/// Address limbs on the "addr" bus: 3 bytes each (the last one 2), little-endian in the limb.
pub const ADDR_LIMBS: usize = 7;

fn addr_limbs<R: PrimeCharacteristicRing>(a: &[R]) -> [R; ADDR_LIMBS] {
    core::array::from_fn(|l| (0..3).filter(|t| 3 * l + t < 20).fold(R::ZERO, |acc, t| acc + a[3 * l + t].clone() * R::from_u32(1 << (8 * t))))
}

/// The limbs of an address (the values the circuit derives from the statement).
pub fn addr_limb_values(a: &Address) -> [u32; ADDR_LIMBS] {
    core::array::from_fn(|l| (0..3).filter(|t| 3 * l + t < 20).map(|t| (a[3 * l + t] as u32) << (8 * t)).sum())
}

/// The transaction AIR with `slots` blob slots, for lanes of 2^`log_rows` rows.
#[derive(Clone, Debug)]
pub struct TxAir {
    pub slots: usize,
    pub log_rows: usize,
}

impl TxAir {
    pub fn new(slots: usize, log_rows: usize) -> Self {
        assert!(slots.is_power_of_two());
        Self { slots, log_rows }
    }
    pub fn log_height(&self) -> usize {
        LOG_TXS + self.slots.trailing_zeros() as usize
    }
    fn rows(&self) -> usize {
        1 << self.log_height()
    }
    /// The trace for the blobs' elements (per blob, `ROWS` canonical values below 2^248) and
    /// the statement's address table. None if an active slot names an unknown address or is
    /// malformed.
    pub fn trace<F: Field>(&self, addrs: &[Address], blobs: &[Vec<BigUint>]) -> Option<RowMajorMatrix<F>> {
        assert!(blobs.len() <= self.slots);
        let mut v = F::zero_vec(self.rows() * WIDTH);
        for r in 0..self.rows() {
            let (j, k) = (r / TXS_PER_BLOB, r % TXS_PER_BLOB);
            let Some(blob) = blobs.get(j) else { continue };
            let bytes = slot_bytes(blob, k);
            if bytes.iter().all(|&b| b == 0) {
                continue;
            }
            let tx = Decoded::of(&bytes)?;
            if r >= DEFAULT_RNS_CHANNELS << self.log_rows {
                return None;
            }
            let id = |a: &Address| addrs.binary_search(a).ok().map(|i| i as u32);
            let row = &mut v[r * WIDTH..(r + 1) * WIDTH];
            for (m, b) in bytes.iter().enumerate() {
                row[m] = F::from_u32(*b as u32);
            }
            row[ACT] = F::ONE;
            row[FROM_ID] = F::from_u32(id(&tx.from)?);
            row[TO_ID] = F::from_u32(id(&tx.to)?);
        }
        Some(RowMajorMatrix::new(v, WIDTH))
    }
    /// How often the trace looks up each byte on the "byte" bus (the nonce's top byte check).
    pub fn byte_counts<F: p3_field::PrimeField32>(t: &RowMajorMatrix<F>, m: &mut [u64; 256]) {
        for row in t.values.chunks(WIDTH) {
            m[4 * row[NONCE].as_canonical_u32() as usize] += 1;
        }
    }
    /// How often each address id is looked up (the `AddrAir` multiplicities).
    pub fn addr_counts<F: p3_field::PrimeField32>(t: &RowMajorMatrix<F>, accounts: usize) -> Vec<u64> {
        let mut m = vec![0u64; accounts];
        for row in t.values.chunks(WIDTH) {
            if row[ACT] == F::ONE {
                m[row[FROM_ID].as_canonical_u32() as usize] += 1;
                m[row[TO_ID].as_canonical_u32() as usize] += 1;
            }
        }
        m
    }
}

/// The 124 bytes of slot `k` of a blob given as its elements.
pub fn slot_bytes(blob: &[BigUint], k: usize) -> [u8; SLOT_BYTES] {
    let mut out = [0u8; SLOT_BYTES];
    for e in 0..ELEMS {
        let b = blob[ELEMS * k + e].to_bytes_be();
        assert!(b.len() <= ELEM_BYTES, "blob element of more than 31 bytes");
        out[e * ELEM_BYTES + ELEM_BYTES - b.len()..(e + 1) * ELEM_BYTES].copy_from_slice(&b);
    }
    out
}

/// The fields the AIR reads from a slot.
pub struct Decoded {
    pub from: Address,
    pub to: Address,
    pub amount: u64,
    pub nonce: u32,
}

impl Decoded {
    /// The transaction of a non-empty slot, or None if the AIR would reject it.
    pub fn of(b: &[u8; SLOT_BYTES]) -> Option<Self> {
        let nonce = u32::from_be_bytes(b[NONCE..NONCE + 4].try_into().unwrap());
        if b[TX_BYTES..].iter().any(|&x| x != 0) || b[KIND] > 1 || nonce >= MAX_NONCE {
            return None;
        }
        Some(Self { from: b[..20].try_into().unwrap(), to: b[20..40].try_into().unwrap(), amount: u64::from_be_bytes(b[AMOUNT..AMOUNT + 8].try_into().unwrap()), nonce })
    }
}

/// A transfer of statement `st` encoded as a transaction (`Tx::encode`) of `kind`, signed `sig`.
pub fn encode_transfer(st: &StateStatement, t: &ss_rap_v2::state::Transfer, kind: u8, sig: &[u8; 65]) -> [u8; TX_BYTES] {
    let mut v = Vec::with_capacity(TX_BYTES);
    v.extend_from_slice(&st.addrs[t.from as usize]);
    v.extend_from_slice(&st.addrs[t.to as usize]);
    v.extend_from_slice(&t.amount.to_be_bytes());
    v.extend_from_slice(&t.nonce.to_be_bytes());
    v.push(kind);
    v.extend_from_slice(sig);
    v.try_into().unwrap()
}

/// The elements of the blobs holding `txs` (encoded transactions, `TX_BYTES` each) in the slot
/// layout: `TXS_PER_BLOB` per blob, at least one blob.
pub fn blob_elements(txs: &[[u8; TX_BYTES]]) -> Vec<Vec<BigUint>> {
    let n = txs.len().div_ceil(TXS_PER_BLOB).max(1);
    (0..n)
        .map(|j| {
            let mut e = vec![BigUint::from(0u32); ROWS];
            for (k, tx) in txs.iter().skip(j * TXS_PER_BLOB).take(TXS_PER_BLOB).enumerate() {
                let mut s = [0u8; SLOT_BYTES];
                s[..TX_BYTES].copy_from_slice(tx);
                for (i, c) in s.chunks(ELEM_BYTES).enumerate() {
                    e[ELEMS * k + i] = BigUint::from_bytes_be(c);
                }
            }
            e
        })
        .collect()
}

impl<F: Field> BaseAir<F> for TxAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let n = 1usize << self.log_rows;
        let mut v = Vec::with_capacity(self.rows() * PRE_WIDTH);
        for r in 0..self.rows() {
            let can = r < DEFAULT_RNS_CHANNELS * n;
            v.extend([F::from_usize(r), F::from_usize(if can { r / n } else { 0 }), F::from_usize(if can { r % n + 1 } else { 0 }), F::from_bool(can)]);
        }
        Some(RowMajorMatrix::new(v, PRE_WIDTH))
    }
    fn preprocessed_width(&self) -> usize {
        PRE_WIDTH
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB> Air<AB> for TxAir
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let c: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let pre = builder.preprocessed();
        let p: Vec<AB::Expr> = pre.current_slice().iter().map(|&x| x.into()).collect();
        let act = c[ACT].clone();
        let off = AB::Expr::ONE - act.clone();
        builder.assert_bool(act.clone());
        builder.assert_zero(act.clone() * (AB::Expr::ONE - p[PRE_CAN].clone()));
        for m in 0..SLOT_BYTES {
            builder.assert_zero(off.clone() * c[m].clone());
        }
        for m in TX_BYTES..SLOT_BYTES {
            builder.assert_zero(c[m].clone());
        }
        builder.assert_bool(c[KIND].clone());
        // nonce < 2^30 = MAX_NONCE: its top byte times 4 is a byte
        builder.push_interaction("byte", [c[NONCE].clone() * AB::Expr::from_u32(4)], 1);
        // the slot's elements
        for e in 0..ELEMS {
            let mut t = vec![p[PRE_R].clone() * AB::Expr::from_u32(ELEMS as u32) + AB::Expr::from_u32(e as u32)];
            t.extend(c[e * ELEM_BYTES..(e + 1) * ELEM_BYTES].iter().cloned());
            builder.push_interaction("elem", t, -1);
        }
        // the transfer the lanes execute: (lane, t, from, to, amount LE bytes, nonce)
        let k256 = AB::Expr::from_u32(256);
        let nonce = (0..4).fold(AB::Expr::ZERO, |acc, k| acc * k256.clone() + c[NONCE + k].clone());
        let mut t = vec![p[PRE_LANE].clone(), p[PRE_T].clone(), c[FROM_ID].clone(), c[TO_ID].clone()];
        t.extend((0..8).map(|k| c[AMOUNT + 7 - k].clone()));
        t.push(nonce);
        builder.push_interaction("tx", t, Count::bounded(act.clone(), 1));
        for (id, at) in [(FROM_ID, 0), (TO_ID, 20)] {
            let mut t = vec![c[id].clone()];
            t.extend(addr_limbs(&c[at..at + 20]));
            builder.push_interaction("addr", t, Count::bounded(act.clone(), 1));
        }
    }
}

/// Columns of `AddrAir`: valid, id, limbs; the main trace adds the multiplicity.
const ADDR_COLS: usize = 2 + ADDR_LIMBS;

/// The statement's address table (id, address limbs) as periodic columns: the provided side of
/// the "addr" bus. Padding rows (valid = 0) provide nothing.
#[derive(Clone, Debug)]
pub struct AddrAir<F> {
    pub cols: Vec<Vec<F>>,
    pub log_rows: usize,
}

/// Height of the address table.
pub fn addr_rows(accounts: usize) -> usize {
    accounts.next_power_of_two().max(4)
}

impl<F: Field> AddrAir<F> {
    pub fn new(st: &StateStatement) -> Self {
        let n = addr_rows(st.addrs.len());
        let mut cols = vec![F::zero_vec(n); ADDR_COLS];
        for (id, a) in st.addrs.iter().enumerate() {
            cols[0][id] = F::ONE;
            cols[1][id] = F::from_usize(id);
            for (l, x) in addr_limb_values(a).iter().enumerate() {
                cols[2 + l][id] = F::from_u32(*x);
            }
        }
        Self { cols, log_rows: n.trailing_zeros() as usize }
    }
    /// The main trace: the periodic values and the multiplicities `m` (one per account).
    pub fn trace(&self, m: &[u64]) -> RowMajorMatrix<F> {
        let n = 1usize << self.log_rows;
        RowMajorMatrix::new((0..n).flat_map(|i| self.cols.iter().map(move |c| c[i]).chain([F::from_u64(m.get(i).copied().unwrap_or(0))])).collect(), ADDR_COLS + 1)
    }
}

impl<F: Field> BaseAir<F> for AddrAir<F> {
    fn width(&self) -> usize {
        ADDR_COLS + 1
    }
    fn num_periodic_columns(&self) -> usize {
        ADDR_COLS
    }
    fn periodic_columns(&self) -> Cow<'_, [Vec<F>]> {
        Cow::Borrowed(&self.cols)
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB> Air<AB> for AddrAir<AB::F>
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let c: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let q: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        for (a, b) in c.iter().zip(q) {
            builder.assert_eq(a.clone(), b);
        }
        let m = c[ADDR_COLS].clone();
        builder.assert_zero(m.clone() * (AB::Expr::ONE - c[0].clone()));
        builder.push_interaction("addr", c[1..ADDR_COLS].to_vec(), Count::provided(-m));
    }
}
