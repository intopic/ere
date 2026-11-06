//! R8.4a: the state statement as a circuit witness.
//!
//! The circuit does not know the batch when it is set up, only its shape (accounts, transfers per
//! lane, trace rows). The statement is witnessed, range-checked and checked well formed exactly
//! as `StateStatement::well_formed` does natively; from it the circuit computes
//! - the statement digest the STARK transcript absorbs (Poseidon over `StateStatement::elements`),
//! - the old and new state roots (Poseidon hash chain over the non-empty accounts),
//! - the public bus tuples of every lane (initial and final accounts, transfers).
//! So a proof for one statement cannot be passed off as a proof for another: the roots that reach
//! the public input are the roots of the statement the STARK verified.

use super::fp31::{range_witness, M31};
use super::stark_var::TupleVar;
use ark_bn254::Fr;
use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::select::CondSelectGadget;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use num_bigint::BigUint;
use ss_rap_v2::hash::{poseidon_config, tag_fr, PACK};
use ss_rap_v2::state::{StateStatement, Transfer, MAX_NONCE, TAG_MEM, TAG_TX};
use ss_rap_v2::{DEFAULT_RNS_CHANNELS, RNS_MODULI};

type R<T> = Result<T, SynthesisError>;

/// What the circuit is built for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StatementShape {
    pub accounts: usize,
    pub lane_txs: [usize; DEFAULT_RNS_CHANNELS],
    pub log_rows: u32,
}

impl StatementShape {
    pub fn of(st: &StateStatement, log_rows: u32) -> Self {
        Self { accounts: st.addrs.len(), lane_txs: std::array::from_fn(|ch| st.lanes[ch].len()), log_rows }
    }
}

/// A witnessed integer with its value.
#[derive(Clone)]
struct Int {
    v: FpVar<Fr>,
}

fn int(cs: &ConstraintSystemRef<Fr>, x: Option<u64>, bits: u64) -> R<Int> {
    Ok(Int { v: range_witness(cs, x.map(BigUint::from), bits)? })
}

/// x <= max (x already range-checked to `bits` bits): max - x fits in `bits` bits too.
fn at_most(cs: &ConstraintSystemRef<Fr>, x: &Int, xv: Option<u64>, max: u64, bits: u64) -> R<()> {
    let d = range_witness(cs, xv.map(|x| BigUint::from(max.saturating_sub(x))), bits)?;
    (&x.v + &d).enforce_equal(&FpVar::constant(Fr::from(max)))
}

#[derive(Clone)]
struct AccountVar {
    nonce: Int,
    bytes: Vec<Int>,
    /// balance 2^32 + nonce
    fr: FpVar<Fr>,
}

#[derive(Clone)]
struct TxVar {
    from: Int,
    to: Int,
    nonce: Int,
    bytes: Vec<Int>,
    fr: FpVar<Fr>,
}

pub struct StatementVar {
    pub shape: StatementShape,
    addrs: Vec<FpVar<Fr>>,
    states: Vec<Vec<AccountVar>>,
    final_ts: Vec<Vec<Int>>,
    lanes: Vec<Vec<TxVar>>,
    pub digest: FpVar<Fr>,
    pub old_root: FpVar<Fr>,
    pub new_root: FpVar<Fr>,
}

fn bits_for(max: u64) -> u64 {
    64 - max.leading_zeros() as u64
}

fn account(cs: &ConstraintSystemRef<Fr>, s: Option<&ss_rap_v2::state::AccountState>) -> R<AccountVar> {
    let nonce = int(cs, s.map(|s| s.nonce as u64), 30)?; // < MAX_NONCE = 2^30
    let bytes = (0..8).map(|k| int(cs, s.map(|s| (s.balance >> (8 * k)) & 0xff), 8)).collect::<R<Vec<_>>>()?;
    let bal = bytes.iter().rev().fold(FpVar::zero(), |acc, b| acc * Fr::from(256u64) + &b.v);
    let fr = bal * Fr::from(1u64 << 32) + &nonce.v;
    Ok(AccountVar { nonce, bytes, fr })
}

fn transfer(cs: &ConstraintSystemRef<Fr>, tx: Option<&Transfer>, accounts: usize) -> R<TxVar> {
    let ib = bits_for(accounts as u64 - 1).max(1);
    let from = int(cs, tx.map(|t| t.from as u64), ib)?;
    at_most(cs, &from, tx.map(|t| t.from as u64), accounts as u64 - 1, ib)?;
    let to = int(cs, tx.map(|t| t.to as u64), ib)?;
    at_most(cs, &to, tx.map(|t| t.to as u64), accounts as u64 - 1, ib)?;
    let nonce = int(cs, tx.map(|t| t.nonce as u64), 30)?;
    let bytes = (0..8).map(|k| int(cs, tx.map(|t| (t.amount >> (8 * k)) & 0xff), 8)).collect::<R<Vec<_>>>()?;
    let amount = bytes.iter().rev().fold(FpVar::zero(), |acc, b| acc * Fr::from(256u64) + &b.v);
    let s32 = Fr::from(1u64 << 32);
    let fr = &from.v + &to.v * s32 + &nonce.v * (s32 * s32) + amount * (s32 * s32 * s32);
    Ok(TxVar { from, to, nonce, bytes, fr })
}

fn poseidon(cs: &ConstraintSystemRef<Fr>, inputs: &[FpVar<Fr>]) -> R<FpVar<Fr>> {
    let mut s = PoseidonSpongeVar::new(cs.clone(), poseidon_config());
    s.absorb(&inputs.to_vec())?;
    Ok(s.squeeze_field_elements(1)?.remove(0))
}

fn root(cs: &ConstraintSystemRef<Fr>, addrs: &[FpVar<Fr>], table: &[AccountVar]) -> R<FpVar<Fr>> {
    let mut h = FpVar::constant(tag_fr(b"SS-RAP/v2/state"));
    for (a, s) in addrs.iter().zip(table) {
        let next = poseidon(cs, &[h.clone(), a.clone(), s.fr.clone()])?;
        let empty = s.fr.is_zero()?;
        h = FpVar::conditionally_select(&empty, &h, &next)?;
    }
    Ok(h)
}

/// Where a public-table cell comes from in the statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Src {
    /// nonce of account `id` in state table `t`
    Nonce(usize, usize),
    /// balance byte `k` of account `id` in state table `t`
    Byte(usize, usize, usize),
    /// final timestamp of account `id` in lane `l`
    Ts(usize, usize),
    From(usize, usize),
    To(usize, usize),
    TxNonce(usize, usize),
    /// amount byte `k` of transfer `j` in lane `l`
    Amt(usize, usize, usize),
}

/// A cell of a public table: a constant of the shape, or a statement value of at most `bits` bits.
#[derive(Clone, Copy, Debug)]
pub enum Cell {
    Const(u32),
    Var(Src, u64),
}

/// The columns of `ss_rap_p3::state::PublicAir::new(st, lane)` for any statement of shape
/// `shape`: initial accounts (weight -1), final accounts (+1), then the lane's transfers (+1),
/// padded with zero rows to the height of the largest lane's table (`public_rows`).
pub fn p3_layout(shape: &StatementShape, lane: usize) -> Vec<Vec<Cell>> {
    const P: u32 = 2013265921;
    let k = |c: u32| Cell::Const(c);
    let zeros = |n: usize| vec![k(0); n];
    let mut rows: Vec<Vec<Cell>> = Vec::new();
    for (t, w) in [(lane, P - 1), (lane + 1, 1)] {
        for id in 0..shape.accounts {
            let ts = if t == lane { k(0) } else { Cell::Var(Src::Ts(lane, id), 31) };
            let mut r = vec![k(id as u32), Cell::Var(Src::Nonce(t, id), 30), ts];
            r.extend((0..8).map(|b| Cell::Var(Src::Byte(t, id, b), 8)));
            r.push(k(w));
            r.extend(zeros(13));
            rows.push(r);
        }
    }
    for j in 0..shape.lane_txs[lane] {
        let mut r = zeros(12);
        r.extend([k(j as u32 + 1), Cell::Var(Src::From(lane, j), 31), Cell::Var(Src::To(lane, j), 31), Cell::Var(Src::TxNonce(lane, j), 30)]);
        r.extend((0..8).map(|b| Cell::Var(Src::Amt(lane, j, b), 8)));
        r.push(k(1));
        rows.push(r);
    }
    // as `ss_rap_p3::state::public_rows`
    let n = shape.lane_txs.iter().map(|&t| 2 * shape.accounts + t).max().unwrap().next_power_of_two().max(4);
    rows.resize(n, zeros(25));
    (0..25).map(|j| rows.iter().map(|r| r[j]).collect()).collect()
}

/// The value of a cell's source in `st`.
pub fn src_value(st: &StateStatement, s: Src) -> u64 {
    match s {
        Src::Nonce(t, id) => st.states[t][id].nonce as u64,
        Src::Byte(t, id, k) => (st.states[t][id].balance >> (8 * k)) & 0xff,
        Src::Ts(l, id) => st.final_ts[l][id] as u64,
        Src::From(l, j) => st.lanes[l][j].from as u64,
        Src::To(l, j) => st.lanes[l][j].to as u64,
        Src::TxNonce(l, j) => st.lanes[l][j].nonce as u64,
        Src::Amt(l, j, k) => (st.lanes[l][j].amount >> (8 * k)) & 0xff,
    }
}

impl StatementVar {
    pub fn witness(cs: &ConstraintSystemRef<Fr>, st: Option<&StateStatement>, shape: StatementShape) -> R<Self> {
        let k = shape.accounts;
        assert!(k > 0 && (k as u32) < MAX_NONCE);
        if let Some(st) = st {
            assert_eq!(StatementShape::of(st, shape.log_rows), shape, "statement of another shape");
        }
        let n_rows = 1u64 << shape.log_rows;
        assert!(shape.lane_txs.iter().all(|&l| l as u64 <= n_rows));
        // addresses: 160 bits, strictly increasing
        let addrs: Vec<FpVar<Fr>> = (0..k)
            .map(|i| range_witness(cs, st.map(|st| BigUint::from_bytes_be(&st.addrs[i])), 160))
            .collect::<R<_>>()?;
        for i in 1..k {
            let d = range_witness(
                cs,
                st.map(|st| {
                    let (a, b) = (BigUint::from_bytes_be(&st.addrs[i]), BigUint::from_bytes_be(&st.addrs[i - 1]) + 1u32);
                    if a >= b { a - b } else { BigUint::from(0u32) } // out of order: unsatisfiable
                }),
                160,
            )?;
            (&addrs[i - 1] + d + FpVar::one()).enforce_equal(&addrs[i])?;
        }
        let states = (0..=DEFAULT_RNS_CHANNELS)
            .map(|t| (0..k).map(|i| account(cs, st.map(|st| &st.states[t][i]))).collect::<R<Vec<_>>>())
            .collect::<R<Vec<_>>>()?;
        let max_ts = 2 * n_rows + 1;
        let tb = bits_for(max_ts);
        let final_ts = (0..DEFAULT_RNS_CHANNELS)
            .map(|ch| {
                (0..k)
                    .map(|i| {
                        let xv = st.map(|st| st.final_ts[ch][i] as u64);
                        let x = int(cs, xv, tb)?;
                        at_most(cs, &x, xv, max_ts, tb)?;
                        Ok(x)
                    })
                    .collect::<R<Vec<_>>>()
            })
            .collect::<R<Vec<_>>>()?;
        let lanes = (0..DEFAULT_RNS_CHANNELS)
            .map(|ch| (0..shape.lane_txs[ch]).map(|j| transfer(cs, st.map(|st| &st.lanes[ch][j]), k)).collect::<R<Vec<_>>>())
            .collect::<R<Vec<_>>>()?;

        // digest: Poseidon over `StateStatement::elements`
        let mut el = vec![FpVar::constant(tag_fr(b"SS-RAP/v2/state-statement")), FpVar::constant(Fr::from(k as u64))];
        el.extend(addrs.iter().cloned());
        for table in &states {
            el.extend(table.iter().map(|a| a.fr.clone()));
        }
        for ts in &final_ts {
            for chunk in ts.chunks(PACK) {
                el.push(chunk.iter().rev().fold(FpVar::zero(), |acc, x| acc * Fr::from(1u64 << 31) + &x.v));
            }
        }
        for lane in &lanes {
            el.push(FpVar::constant(Fr::from(lane.len() as u64)));
            el.extend(lane.iter().map(|t| t.fr.clone()));
        }
        let digest = poseidon(cs, &el)?;
        let old_root = root(cs, &addrs, &states[0])?;
        let new_root = root(cs, &addrs, &states[DEFAULT_RNS_CHANNELS])?;
        Ok(Self { shape, addrs, states, final_ts, lanes, digest, old_root, new_root })
    }

    /// The public tuples of lane `ch`, as `StateAir::public_tuples`.
    pub fn public_tuples(&self, ch: usize) -> Vec<TupleVar> {
        let m = RNS_MODULI[ch];
        let val = |x: &Int, bits: u64| M31 { v: x.v.clone(), bound: BigUint::from(1u64) << bits, ch };
        let k = |c: u32| M31::constant(c, ch);
        let mut out = Vec::new();
        for (id, s) in self.states[ch].iter().enumerate() {
            let mut v = vec![k(id as u32), val(&s.nonce, 30), k(0)];
            v.extend(s.bytes.iter().map(|b| val(b, 8)));
            out.push((TAG_MEM, v, k(1)));
        }
        for (id, s) in self.states[ch + 1].iter().enumerate() {
            let mut v = vec![k(id as u32), val(&s.nonce, 30), val(&self.final_ts[ch][id], 31)];
            v.extend(s.bytes.iter().map(|b| val(b, 8)));
            out.push((TAG_MEM, v, k(m - 1)));
        }
        for (j, tx) in self.lanes[ch].iter().enumerate() {
            let mut v = vec![k(j as u32 + 1), val(&tx.from, 31), val(&tx.to, 31), val(&tx.nonce, 30)];
            v.extend(tx.bytes.iter().map(|b| val(b, 8)));
            out.push((TAG_TX, v, k(m - 1)));
        }
        out
    }

    /// The periodic columns of `ss_rap_p3::state::PublicAir::new(st, lane)` (BabyBear), see
    /// `p3_layout`.
    pub fn p3_public_cols(&self, lane: usize) -> Vec<Vec<M31>> {
        p3_layout(&self.shape, lane)
            .iter()
            .map(|c| {
                c.iter()
                    .map(|cell| match cell {
                        Cell::Const(v) => M31::constant(*v, 0),
                        Cell::Var(src, bits) => M31 { v: self.src(*src).clone(), bound: BigUint::from(1u64) << *bits, ch: 0 },
                    })
                    .collect()
            })
            .collect()
    }

    /// The witnessed integer behind a public-table cell.
    pub fn src(&self, s: Src) -> &FpVar<Fr> {
        match s {
            Src::Nonce(t, id) => &self.states[t][id].nonce.v,
            Src::Byte(t, id, k) => &self.states[t][id].bytes[k].v,
            Src::Ts(l, id) => &self.final_ts[l][id].v,
            Src::From(l, j) => &self.lanes[l][j].from.v,
            Src::To(l, j) => &self.lanes[l][j].to.v,
            Src::TxNonce(l, j) => &self.lanes[l][j].nonce.v,
            Src::Amt(l, j, k) => &self.lanes[l][j].bytes[k].v,
        }
    }

    /// The digest as `ss_rap_p3::state::digest_limbs` (30-bit limbs of its canonical bits).
    pub fn digest_limbs(&self) -> R<Vec<FpVar<Fr>>> {
        use ark_r1cs_std::boolean::Boolean;
        use ark_r1cs_std::prelude::ToBitsGadget;
        let bits = self.digest.to_bits_le()?;
        let (n, lb) = (ss_rap_p3::state::DIGEST_LIMBS, ss_rap_p3::state::LIMB_BITS);
        assert!(n * lb >= bits.len());
        (0..n).map(|i| Boolean::le_bits_to_fp(&bits[(i * lb).min(bits.len())..((i + 1) * lb).min(bits.len())])).collect()
    }

    pub fn num_txs(&self) -> usize {
        self.shape.lane_txs.iter().sum()
    }

    #[allow(dead_code)]
    fn addrs(&self) -> &[FpVar<Fr>] {
        &self.addrs
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use ss_rap_v2::hash::hash_to_fr;
    use ss_rap_v2::state::{self, AccountState};

    fn case() -> StateStatement {
        let accounts = 9usize;
        let addrs: Vec<[u8; 20]> = (0..accounts).map(|i| [i as u8 * 3 + 1; 20]).collect();
        let mut old: Vec<AccountState> = (0..accounts).map(|i| AccountState { balance: 1_000_000 + i as u64, nonce: 0 }).collect();
        old[8] = AccountState::default(); // created by the batch
        let mut nonces = vec![0u32; accounts];
        let txs: Vec<Transfer> = (0..17u32)
            .map(|k| {
                let from = (k * 5 + 1) % 8;
                let tx = Transfer { from, to: (from + 1 + k % 7) % accounts as u32, amount: 10 + k as u64, nonce: nonces[from as usize] };
                nonces[from as usize] += 1;
                tx
            })
            .collect();
        state::build(&addrs, &old, &txs, 8, true).unwrap().0
    }

    #[test]
    fn digest_roots_and_tuples_match_native() {
        let st = case();
        let shape = StatementShape::of(&st, 8);
        let cs = ConstraintSystem::<Fr>::new_ref();
        let sv = StatementVar::witness(&cs, Some(&st), shape).unwrap();
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(sv.digest.value().unwrap(), hash_to_fr(&st.digest()));
        assert_eq!(sv.old_root.value().unwrap(), hash_to_fr(&st.old_root()));
        assert_eq!(sv.new_root.value().unwrap(), hash_to_fr(&st.new_root()));
        use ss_rap_v2::stark::Air;
        let air = state::StateAir { st: &st };
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let native = air.public_tuples(ch);
            let circ = sv.public_tuples(ch);
            assert_eq!(native.len(), circ.len());
            for (a, (tag, vals, w)) in native.iter().zip(&circ) {
                assert_eq!(a.tag, *tag);
                assert_eq!(a.weight, w.value().unwrap());
                assert_eq!(a.values, vals.iter().map(|v| v.value().unwrap()).collect::<Vec<_>>());
            }
        }
        // the Plonky3 public AIRs' periodic columns and the digest limbs
        type BB = p3_baby_bear::BabyBear;
        use p3_field::PrimeField32;
        for lane in 0..DEFAULT_RNS_CHANNELS {
            let native = ss_rap_p3::state::PublicAir::<BB>::new(&st, lane).cols;
            let circ = sv.p3_public_cols(lane);
            assert_eq!(native.len(), circ.len());
            for (a, b) in native.iter().zip(&circ) {
                assert_eq!(a.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(), b.iter().map(|v| v.value().unwrap()).collect::<Vec<_>>());
            }
        }
        let limbs: Vec<Fr> = sv.digest_limbs().unwrap().iter().map(|x| x.value().unwrap()).collect();
        assert_eq!(limbs, ss_rap_p3::state::digest_limbs(&st).into_iter().map(|v| Fr::from(v as u64)).collect::<Vec<_>>());
        assert!(cs.is_satisfied().unwrap());
        eprintln!("statement ({} accounts, {} txs): {} constraints", shape.accounts, st.num_txs(), cs.num_constraints());
    }

    #[test]
    fn malformed_statements_are_unsatisfiable() {
        let st = case();
        let shape = StatementShape::of(&st, 8);
        let ok = |st: &StateStatement| {
            let cs = ConstraintSystem::<Fr>::new_ref();
            StatementVar::witness(&cs, Some(st), shape).unwrap();
            cs.is_satisfied().unwrap()
        };
        assert!(ok(&st));
        let mut bad = st.clone();
        bad.addrs.swap(2, 3);
        assert!(!ok(&bad), "addresses out of order");
        let mut bad = st.clone();
        bad.addrs[4] = bad.addrs[3];
        assert!(!ok(&bad), "duplicate address");
        let mut bad = st.clone();
        let lane = (0..DEFAULT_RNS_CHANNELS).find(|&ch| !st.lanes[ch].is_empty()).unwrap();
        bad.lanes[lane][0].to = st.addrs.len() as u32;
        assert!(!ok(&bad), "transfer to an account outside the table");
        let mut bad = st.clone();
        bad.final_ts[2][1] = 2 * 256 + 2;
        assert!(!ok(&bad), "timestamp beyond the trace");
    }
}
