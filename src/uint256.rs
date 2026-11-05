//! EVM `uint256` MULMOD as an AIR that is sound in EACH 31-bit RNS channel on its own.
//!
//! Why byte limbs and not 64-bit limbs: a STARK commits each channel's trace in its own field,
//! and nothing binds the integers committed in channel i to those in channel j (they live in
//! different fields; see `stark::tests::lanes_are_independent`). So the CRT argument "checked
//! mod every m_j, hence over Z" cannot be used across channels inside the STARK. Instead every
//! identity below is an integer of magnitude < 2^24 < m_j / 2 whenever its inputs are bytes
//! (LogUp range check, same channel), so "= 0 mod m_j" already implies "= 0 over Z" in a single
//! channel. The 5 RNS channels then work as 5 independent parallel lanes, each proving its own
//! share of the batch. This is the standard way uint256 is arithmetised over 31-bit fields.
//!
//! "Don't compute, verify": the prover supplies q, r, s and the carries as witnesses; the
//! constraints never divide, are degree <= 2 and are independent of each other.
//!
//! Witness per row (all bytes, every byte range-checked with LogUp):
//!   a, b, q, r, s           5 x 32 bytes
//!   c_0..c_61              62 x 2 bytes   product-column carries, stored as c_k + 2^14
//!   d_0..d_30              31 x 1 byte    carries of the canonical check s + r + 1 = P
//!
//! Constraints (all must be 0):
//!   product column k = 0..62:
//!     sum_{i+l=k} a_i*b_l - sum_{i+l=k} q_i*P_l - [k<32] r_k + c_{k-1} - 256 * c_k
//!   canonical column k = 0..31   (forces r < P):
//!     s_k + r_k + [k=0] + d_{k-1} - P_k - 256 * d_k
//!   with c_{-1} = d_{-1} = 0 and no carry out of the top column (c_62 = d_31 = 0).
//! Bounds: each sum has <= 32 products of bytes (< 2^21), |c_k| < 2^13, so every product
//! column is < 2^24 in absolute value; canonical columns are < 2^17.
//! Summing column_k * 256^k telescopes the carries away, giving a*b = q*P + r and
//! s + r + 1 = P over Z, hence r = a*b mod P with r < P.

use crate::{add_mod, mul_mod_channel, sub_mod, DEFAULT_RNS_CHANNELS, RNS_MODULI};

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::One;

pub const BYTES: usize = 32;
pub const PRODUCT_COLUMNS: usize = 2 * BYTES - 1; // 63
pub const CARRY_BYTES: usize = 2;
/// Carries are stored with this offset so that they are non-negative: |c_k| < 2^13.
pub const CARRY_OFFSET_BITS: u32 = 14;
pub const CONSTRAINTS_PER_CHANNEL: usize = PRODUCT_COLUMNS + BYTES; // 95

pub const SECP256K1_P_HEX: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
pub const BN254_P_HEX: &str = "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47";

pub type U256Bytes = [u8; 32];

pub(crate) fn to_bytes32(x: &BigUint) -> U256Bytes {
    let v = x.to_bytes_le();
    assert!(v.len() <= 32, "value does not fit in 256 bits");
    let mut out = [0u8; 32];
    out[..v.len()].copy_from_slice(&v);
    out
}

/// A 256-bit modulus (public constant of the circuit).
#[derive(Clone, Debug)]
pub struct Modulus256 {
    pub value: BigUint,
    pub bytes: U256Bytes,
}

impl Modulus256 {
    pub fn from_hex(hex: &str) -> Self {
        let value = BigUint::parse_bytes(hex.as_bytes(), 16).expect("bad hex");
        assert!(value > BigUint::one(), "modulus must be > 1");
        Self { bytes: to_bytes32(&value), value }
    }
    pub fn secp256k1() -> Self {
        Self::from_hex(SECP256K1_P_HEX)
    }
    pub fn bn254() -> Self {
        Self::from_hex(BN254_P_HEX)
    }
}

/// Witness row for r = a * b mod P.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MulModRow {
    pub a: U256Bytes,
    pub b: U256Bytes,
    pub q: U256Bytes,
    pub r: U256Bytes,
    pub s: U256Bytes,
    pub c: [[u8; CARRY_BYTES]; PRODUCT_COLUMNS - 1],
    pub d: [u8; BYTES - 1],
}

/// Integer value of product column k before carries.
fn column_value(a: &U256Bytes, b: &U256Bytes, q: &U256Bytes, r: &U256Bytes, p: &U256Bytes, k: usize) -> i64 {
    let mut col = 0i64;
    for i in k.saturating_sub(BYTES - 1)..=k.min(BYTES - 1) {
        col += a[i] as i64 * b[k - i] as i64 - q[i] as i64 * p[k - i] as i64;
    }
    if k < BYTES {
        col -= r[k] as i64;
    }
    col
}

/// Product-column carries for given a, b, q, r. `None` when they do not fit the carry columns.
/// For honest values every column is divisible; for forged ones this is the best-effort fit
/// (floor division) used by the attack tests.
fn carries(a: &U256Bytes, b: &U256Bytes, q: &U256Bytes, r: &U256Bytes, p: &U256Bytes) -> Option<([[u8; CARRY_BYTES]; PRODUCT_COLUMNS - 1], i64, bool)> {
    let mut c = [[0u8; CARRY_BYTES]; PRODUCT_COLUMNS - 1];
    let mut carry = 0i64;
    let mut exact = true;
    for k in 0..PRODUCT_COLUMNS - 1 {
        let col = column_value(a, b, q, r, p, k) + carry;
        exact &= col.rem_euclid(256) == 0;
        let next = col.div_euclid(256);
        let stored = next + (1i64 << CARRY_OFFSET_BITS);
        if !(0..1 << (8 * CARRY_BYTES)).contains(&stored) {
            return None;
        }
        c[k] = (stored as u16).to_le_bytes();
        carry = next;
    }
    let top = column_value(a, b, q, r, p, PRODUCT_COLUMNS - 1) + carry;
    Some((c, top, exact))
}

impl MulModRow {
    /// Honest witness generation (this is the only place that "computes"; the circuit verifies).
    pub fn generate(a: &BigUint, b: &BigUint, p: &Modulus256) -> Self {
        assert!(a.bits() <= 256 && b.bits() <= 256, "operands must be uint256");
        let (q, r) = (a * b).div_rem(&p.value);
        assert!(q.bits() <= 256, "a*b/P must fit in 256 bits");
        let s = &p.value - &r - BigUint::one();
        let (a_b, b_b, q_b, r_b, s_b) = (to_bytes32(a), to_bytes32(b), to_bytes32(&q), to_bytes32(&r), to_bytes32(&s));
        let (c, top, exact) = carries(&a_b, &b_b, &q_b, &r_b, &p.bytes).expect("carries fit");
        assert!(exact && top == 0, "honest columns must telescope");

        let mut d = [0u8; BYTES - 1];
        let mut dc = 0u32;
        for k in 0..BYTES {
            let col = s_b[k] as u32 + r_b[k] as u32 + (k == 0) as u32 + dc;
            let pk = p.bytes[k] as u32;
            assert!(col >= pk && (col - pk) % 256 == 0);
            dc = (col - pk) / 256;
            if k < BYTES - 1 {
                d[k] = dc as u8;
            } else {
                assert_eq!(dc, 0);
            }
        }
        Self { a: a_b, b: b_b, q: q_b, r: r_b, s: s_b, c, d }
    }

    pub fn r_value(&self) -> BigUint {
        BigUint::from_bytes_le(&self.r)
    }

    /// Evaluates all constraints in channel `ch`. Honest rows give all zeros.
    pub fn evaluate(&self, p: &Modulus256, ch: usize) -> [u32; CONSTRAINTS_PER_CHANNEL] {
        eval_columns(&self.limbs(), &p_columns(p, ch), ch)
    }

    /// Satisfied in one channel. Because the AIR is sound per channel, this alone implies the
    /// identities over Z (for byte-valued columns).
    pub fn is_satisfied_in(&self, p: &Modulus256, ch: usize) -> bool {
        self.evaluate(p, ch).iter().all(|&x| x == 0)
    }

    pub fn is_satisfied(&self, p: &Modulus256) -> bool {
        (0..DEFAULT_RNS_CHANNELS).all(|ch| self.is_satisfied_in(p, ch))
    }

    /// Every byte of the row, for the LogUp range check.
    pub fn limbs(&self) -> Vec<u32> {
        let mut v: Vec<u32> = Vec::with_capacity(NUM_COLUMNS);
        for x in [&self.a, &self.b, &self.q, &self.r, &self.s] {
            v.extend(x.iter().map(|&b| b as u32));
        }
        for c in &self.c {
            v.extend(c.iter().map(|&b| b as u32));
        }
        v.extend(self.d.iter().map(|&b| b as u32));
        v
    }
}

pub const NUM_COLUMNS: usize = 5 * BYTES + (PRODUCT_COLUMNS - 1) * CARRY_BYTES + (BYTES - 1); // 315
const COL_A: usize = 0;
const COL_B: usize = BYTES;
const COL_Q: usize = 2 * BYTES;
const COL_R: usize = 3 * BYTES;
const COL_S: usize = 4 * BYTES;
const COL_C: usize = 5 * BYTES;
const COL_D: usize = COL_C + (PRODUCT_COLUMNS - 1) * CARRY_BYTES;

/// Bytes of P (public constants of the AIR; identical in every channel since they are < 256).
pub type PColumns = [u32; BYTES];
pub fn p_columns(p: &Modulus256, _ch: usize) -> PColumns {
    std::array::from_fn(|i| p.bytes[i] as u32)
}

/// The MULMOD AIR as polynomial constraints over column values in F_{m_ch}. `cols` holds the
/// byte columns in the order of `MulModRow::limbs()`. On byte values this is exactly
/// `MulModRow::evaluate`; the STARK evaluates it on low-degree extensions of the columns.
pub fn eval_columns(cols: &[u32], pl: &PColumns, ch: usize) -> [u32; CONSTRAINTS_PER_CHANNEL] {
    let m = RNS_MODULI[ch];
    let m2 = (m as u64) * (m as u64);
    let offset = 1u32 << CARRY_OFFSET_BITS;
    let carry = |k: usize| -> u32 {
        let base = COL_C + CARRY_BYTES * k;
        let v = add_mod(cols[base], mul_mod_channel(cols[base + 1], 256, ch), m);
        sub_mod(v, offset, m)
    };
    let (a, b, q, r, s) = (&cols[COL_A..], &cols[COL_B..], &cols[COL_Q..], &cols[COL_R..], &cols[COL_S..]);

    let mut out = [0u32; CONSTRAINTS_PER_CHANNEL];
    for k in 0..PRODUCT_COLUMNS {
        // sum a_i*b_l - q_i*P_l with lazy reduction: each term < m^2, keep the sum below 2^64.
        let mut pos = 0u64;
        let mut neg = 0u64;
        for i in k.saturating_sub(BYTES - 1)..=k.min(BYTES - 1) {
            pos += a[i] as u64 * b[k - i] as u64;
            neg += q[i] as u64 * pl[k - i] as u64;
            if pos >= m2 * 7 {
                pos %= m as u64;
            }
            if neg >= m2 * 7 {
                neg %= m as u64;
            }
        }
        let mut v = sub_mod((pos % m as u64) as u32, (neg % m as u64) as u32, m);
        if k > 0 {
            v = add_mod(v, carry(k - 1), m);
        }
        if k < BYTES {
            v = sub_mod(v, r[k], m);
        }
        if k < PRODUCT_COLUMNS - 1 {
            v = sub_mod(v, mul_mod_channel(carry(k), 256, ch), m);
        }
        out[k] = v;
    }
    for k in 0..BYTES {
        let mut v = add_mod(s[k], r[k], m);
        v = add_mod(v, if k == 0 { 1 } else { cols[COL_D + k - 1] }, m);
        v = sub_mod(v, pl[k] % m, m);
        if k < BYTES - 1 {
            v = sub_mod(v, mul_mod_channel(cols[COL_D + k], 256, ch), m);
        }
        out[PRODUCT_COLUMNS + k] = v;
    }
    out
}

/// Best-effort carries for a (possibly forged) a, b, q, r. Used by the attack tests.
#[cfg(test)]
fn carries_for(a: &U256Bytes, b: &U256Bytes, q: &U256Bytes, r: &U256Bytes, p: &Modulus256) -> Option<[[u8; CARRY_BYTES]; PRODUCT_COLUMNS - 1]> {
    carries(a, b, q, r, &p.bytes).map(|(c, _, _)| c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logup;
    use crate::transcript::Transcript;
    use num_traits::Zero;

    fn rng(state: &mut u64) -> BigUint {
        let words: Vec<u32> = (0..8)
            .map(|_| {
                *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                (*state >> 32) as u32
            })
            .collect();
        BigUint::new(words)
    }

    #[test]
    fn honest_rows_satisfy_on_secp256k1_and_bn254() {
        let mut seed = 42u64;
        for p in [Modulus256::secp256k1(), Modulus256::bn254()] {
            let max = (BigUint::one() << 256u32) - BigUint::one();
            let edge = [BigUint::zero(), BigUint::one(), &p.value - BigUint::one(), max.clone()];
            let mut cases: Vec<(BigUint, BigUint)> = Vec::new();
            for x in &edge {
                for y in &edge {
                    cases.push((x.clone(), y.clone()));
                }
            }
            for _ in 0..200 {
                cases.push((rng(&mut seed), rng(&mut seed)));
            }
            for (a, b) in cases {
                // EVM MULMOD semantics on uint256 inputs; q = a*b/P must fit in 256 bits.
                if (&a * &b / &p.value).bits() > 256 {
                    continue;
                }
                let row = MulModRow::generate(&a, &b, &p);
                assert_eq!(row.r_value(), (&a * &b) % &p.value);
                assert!(row.is_satisfied(&p), "honest row rejected");
            }
        }
    }

    #[test]
    fn forged_result_is_rejected() {
        let p = Modulus256::secp256k1();
        let mut seed = 7u64;
        for _ in 0..50 {
            let (a, b) = (rng(&mut seed) % &p.value, rng(&mut seed) % &p.value);
            let honest = MulModRow::generate(&a, &b, &p);
            // Claim r + 1 (keeping s consistent) and re-fit every product carry as well as possible.
            let fake_r = (honest.r_value() + 1u32) % &p.value;
            let mut row = honest.clone();
            row.r = to_bytes32(&fake_r);
            row.s = to_bytes32(&(&p.value - &fake_r - 1u32));
            if let Some(c) = carries_for(&row.a, &row.b, &row.q, &row.r, &p) {
                row.c = c;
            }
            assert!(!row.is_satisfied(&p), "forged r accepted");
        }
    }

    #[test]
    fn non_canonical_result_is_rejected() {
        // r' = r + P with q' = q - 1 satisfies a*b = q'P + r' over Z, so every product column
        // passes; only the canonical check s + r + 1 = P can catch it.
        let p = Modulus256::bn254(); // small enough that r + P < 2^256
        let mut seed = 99u64;
        let mut tried = 0;
        while tried < 20 {
            let (a, b) = (rng(&mut seed) % &p.value, rng(&mut seed) % &p.value);
            let honest = MulModRow::generate(&a, &b, &p);
            let q = BigUint::from_bytes_le(&honest.q);
            if q.is_zero() {
                continue;
            }
            tried += 1;
            let mut row = honest.clone();
            row.q = to_bytes32(&(q - 1u32));
            row.r = to_bytes32(&(honest.r_value() + &p.value));
            row.c = carries_for(&row.a, &row.b, &row.q, &row.r, &p).expect("carries fit");
            row.s = [0u8; 32];
            row.d = [0u8; BYTES - 1];
            let ok_products = (0..DEFAULT_RNS_CHANNELS).all(|ch| row.evaluate(&p, ch)[..PRODUCT_COLUMNS].iter().all(|&x| x == 0));
            assert!(ok_products, "product columns should pass for r + P");
            // Best effort for s: any byte value cannot make s + r + 1 = P with r >= P.
            for fill in [0u8, 0xff] {
                row.s = [fill; 32];
                for d0 in [0u8, 1, 255] {
                    row.d = [d0; BYTES - 1];
                    assert!(!row.is_satisfied(&p), "non-canonical r accepted");
                }
            }
        }
    }

    #[test]
    fn mulmod_bytes_pass_logup_and_out_of_range_fails() {
        let p = Modulus256::secp256k1();
        let mut seed = 3u64;
        let rows: Vec<MulModRow> = (0..16).map(|_| MulModRow::generate(&(rng(&mut seed) % &p.value), &(rng(&mut seed) % &p.value), &p)).collect();
        let limbs: Vec<u32> = rows.iter().flat_map(|r| r.limbs()).collect();
        let proof = logup::prove(&limbs, &mut Transcript::new(b"mulmod"));
        assert!(logup::verify(&limbs, &proof, &mut Transcript::new(b"mulmod")));

        let mut bad = limbs.clone();
        bad[0] += 256;
        let proof = logup::prove(&bad, &mut Transcript::new(b"mulmod"));
        assert!(!logup::verify(&bad, &proof, &mut Transcript::new(b"mulmod")));
    }
}
