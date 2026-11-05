//! EVM `uint256` MULMOD on the PDF architecture: 64-bit limbs x 5 RNS channels (PDF f.3, §2.2).
//!
//! The PDF proves `P(A, B) = R (mod p)` "for Goldilocks or 64-bit limbs of EVM 256-bit" with the
//! 5-channel modulus M ~ 2^154.3. A full 256-bit identity a*b = q*P + r does not fit below M,
//! so it is split into 64-bit limb columns. Each column identity is an integer of magnitude
//! < 2^137 < M/2, so checking it modulo the 5 channel primes proves it over Z (CRT), exactly as
//! the PDF's soundness argument does for one 64-bit product.
//!
//! "Don't compute, verify": the prover supplies q, r, s and the column carries as witnesses; the
//! constraints never divide, never reconstruct with CRT and are all independent of each other
//! (degree <= 2), so all 11 x 5 constraint evaluations of a row can run in parallel.
//!
//! Witness per row (all as bytes, every byte range-checked with LogUp):
//!   a, b, q, r, s           5 x 32 bytes   (4 limbs of 64 bits each)
//!   c_0..c_5               6 x 9 bytes    product-column carries, stored as c_k + 2^67
//!   d_0..d_2               3 x 1 byte     carries of the canonical check s + r + 1 = P
//!
//! Constraints per channel j (all must be 0 mod m_j):
//!   product column k = 0..6:
//!     sum_{i+l=k} a_i*b_l - sum_{i+l=k} q_i*P_l - [k<4] r_k + c_{k-1} - c_k * 2^64
//!   canonical column k = 0..3   (forces r < P):
//!     s_k + r_k + [k=0] + d_{k-1} - P_k - d_k * 2^64
//!   with c_{-1} = d_{-1} = 0 and no carry out of the top column (c_6 = d_3 = 0).
//! Summing column_k * 2^(64k) telescopes the carries away, giving a*b = q*P + r and
//! s + r + 1 = P over Z, hence r = a*b mod P with r < P.

use crate::{add_mod, fast_reduce_channel, mul_mod_channel, sub_mod, DEFAULT_RNS_CHANNELS, POW256, RNS_MODULI};

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Zero};

pub const LIMBS64: usize = 4;
pub const PRODUCT_COLUMNS: usize = 2 * LIMBS64 - 1; // 7
pub const CARRY_BYTES: usize = 9;
/// Carries are stored with this offset so that they are non-negative: |c_k| < 2^67.
pub const CARRY_OFFSET_BITS: u32 = 67;
pub const CONSTRAINTS_PER_CHANNEL: usize = PRODUCT_COLUMNS + LIMBS64; // 11

pub const SECP256K1_P_HEX: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
pub const BN254_P_HEX: &str = "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47";

pub type U256Bytes = [u8; 32];

fn to_bytes32(x: &BigUint) -> U256Bytes {
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
    pub d: [u8; LIMBS64 - 1],
}

fn limb64(bytes: &U256Bytes, i: usize) -> u64 {
    u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap())
}

/// Residue mod m_ch of 64-bit limb i of a 256-bit value, from its bytes (linear, fixed coefficients).
#[inline(always)]
fn limb_res(bytes: &U256Bytes, i: usize, ch: usize) -> u32 {
    let pw = &POW256[ch];
    let mut acc = 0u64;
    for k in 0..8 {
        acc += (bytes[8 * i + k] as u64) * (pw[k] as u64); // < 2^39 each
    }
    fast_reduce_channel(acc, ch)
}

impl MulModRow {
    /// Honest witness generation (this is the only place that "computes"; the circuit verifies).
    pub fn generate(a: &BigUint, b: &BigUint, p: &Modulus256) -> Self {
        assert!(a.bits() <= 256 && b.bits() <= 256, "operands must be uint256");
        let (q, r) = (a * b).div_rem(&p.value);
        assert!(q.bits() <= 256, "a*b/P must fit in 256 bits");
        let s = &p.value - &r - BigUint::one();
        let (a_b, b_b, q_b, r_b, s_b) = (to_bytes32(a), to_bytes32(b), to_bytes32(&q), to_bytes32(&r), to_bytes32(&s));

        // Product-column carries over Z.
        let two64 = BigInt::one() << 64;
        let offset = BigInt::one() << CARRY_OFFSET_BITS;
        let mut c = [[0u8; CARRY_BYTES]; PRODUCT_COLUMNS - 1];
        let mut carry = BigInt::zero();
        for k in 0..PRODUCT_COLUMNS {
            let mut col = carry.clone();
            for i in 0..LIMBS64 {
                if k >= i && k - i < LIMBS64 {
                    col += BigInt::from(limb64(&a_b, i)) * BigInt::from(limb64(&b_b, k - i));
                    col -= BigInt::from(limb64(&q_b, i)) * BigInt::from(limb64(&p.bytes, k - i));
                }
            }
            if k < LIMBS64 {
                col -= BigInt::from(limb64(&r_b, k));
            }
            let (next, rem) = col.div_rem(&two64);
            assert!(rem.is_zero(), "column {k} not divisible by 2^64");
            if k < PRODUCT_COLUMNS - 1 {
                let stored = (&next + &offset).to_biguint().expect("carry below offset");
                let v = stored.to_bytes_le();
                assert!(v.len() <= CARRY_BYTES);
                c[k][..v.len()].copy_from_slice(&v);
            } else {
                assert!(next.is_zero(), "top column must not carry");
            }
            carry = next;
        }

        // Canonical-check carries: s + r + 1 = P, column-wise.
        let mut d = [0u8; LIMBS64 - 1];
        let mut dc: u128 = 0;
        for k in 0..LIMBS64 {
            let col = limb64(&s_b, k) as u128 + limb64(&r_b, k) as u128 + (k == 0) as u128 + dc;
            let pk = limb64(&p.bytes, k) as u128;
            assert!(col >= pk && (col - pk) % (1u128 << 64) == 0);
            dc = (col - pk) >> 64;
            if k < LIMBS64 - 1 {
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

    /// Evaluates all 11 constraints in channel `ch`. Honest rows give all zeros.
    pub fn evaluate(&self, p: &Modulus256, ch: usize) -> [u32; CONSTRAINTS_PER_CHANNEL] {
        let cols = self.limbs();
        let pc = p_columns(p, ch);
        eval_columns(&cols, &pc, ch)
    }

    pub fn is_satisfied(&self, p: &Modulus256) -> bool {
        (0..DEFAULT_RNS_CHANNELS).all(|ch| self.evaluate(p, ch).iter().all(|&x| x == 0))
    }

    /// Every byte of the row, for the LogUp range check.
    pub fn limbs(&self) -> Vec<u32> {
        let mut v: Vec<u32> = Vec::with_capacity(5 * 32 + 6 * CARRY_BYTES + 3);
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

pub const NUM_COLUMNS: usize = 5 * 32 + (PRODUCT_COLUMNS - 1) * CARRY_BYTES + (LIMBS64 - 1); // 217
const COL_A: usize = 0;
const COL_B: usize = 32;
const COL_Q: usize = 64;
const COL_R: usize = 96;
const COL_S: usize = 128;
const COL_C: usize = 160;
const COL_D: usize = COL_C + (PRODUCT_COLUMNS - 1) * CARRY_BYTES;

/// Residues of the 4 limbs of P in channel `ch` (public constants of the AIR).
pub fn p_columns(p: &Modulus256, ch: usize) -> [u32; LIMBS64] {
    std::array::from_fn(|i| limb_res(&p.bytes, i, ch))
}

/// The MULMOD AIR as polynomial constraints over column values in F_{m_ch}. `cols` holds the
/// 217 byte columns in the order of `MulModRow::limbs()`. On byte values this is exactly
/// `MulModRow::evaluate`; the STARK evaluates it on low-degree extensions of the columns.
pub fn eval_columns(cols: &[u32], pl: &[u32; LIMBS64], ch: usize) -> [u32; CONSTRAINTS_PER_CHANNEL] {
    let m = RNS_MODULI[ch];
    let pw = &POW256[ch];
    let lin = |start: usize, len: usize| -> u32 {
        let mut acc = 0u32;
        for k in 0..len {
            acc = add_mod(acc, mul_mod_channel(cols[start + k], pw[k], ch), m);
        }
        acc
    };
    let limb = |base: usize, i: usize| lin(base + 8 * i, 8);
    let two64 = pw[8];
    let offset = mul_mod_channel(two64, 8, ch);
    let carry = |k: usize| sub_mod(lin(COL_C + CARRY_BYTES * k, CARRY_BYTES), offset, m);
    let a: [u32; LIMBS64] = std::array::from_fn(|i| limb(COL_A, i));
    let b: [u32; LIMBS64] = std::array::from_fn(|i| limb(COL_B, i));
    let q: [u32; LIMBS64] = std::array::from_fn(|i| limb(COL_Q, i));
    let r: [u32; LIMBS64] = std::array::from_fn(|i| limb(COL_R, i));
    let s: [u32; LIMBS64] = std::array::from_fn(|i| limb(COL_S, i));

    let mut out = [0u32; CONSTRAINTS_PER_CHANNEL];
    for k in 0..PRODUCT_COLUMNS {
        let mut v = if k > 0 { carry(k - 1) } else { 0 };
        for i in 0..LIMBS64 {
            if k >= i && k - i < LIMBS64 {
                v = add_mod(v, mul_mod_channel(a[i], b[k - i], ch), m);
                v = sub_mod(v, mul_mod_channel(q[i], pl[k - i], ch), m);
            }
        }
        if k < LIMBS64 {
            v = sub_mod(v, r[k], m);
        }
        if k < PRODUCT_COLUMNS - 1 {
            v = sub_mod(v, mul_mod_channel(carry(k), two64, ch), m);
        }
        out[k] = v;
    }
    for k in 0..LIMBS64 {
        let mut v = add_mod(s[k], r[k], m);
        v = add_mod(v, if k == 0 { 1 } else { cols[COL_D + k - 1] }, m);
        v = sub_mod(v, pl[k], m);
        if k < LIMBS64 - 1 {
            v = sub_mod(v, mul_mod_channel(cols[COL_D + k], two64, ch), m);
        }
        out[PRODUCT_COLUMNS + k] = v;
    }
    out
}

/// Re-derives every product-column carry for a (possibly forged) a, b, q, r so that the product
/// columns are as satisfiable as they can be. Used by the attack tests.
#[cfg(test)]
fn carries_for(a: &U256Bytes, b: &U256Bytes, q: &U256Bytes, r: &U256Bytes, p: &Modulus256) -> Option<[[u8; CARRY_BYTES]; PRODUCT_COLUMNS - 1]> {
    let two64 = BigInt::one() << 64;
    let offset = BigInt::one() << CARRY_OFFSET_BITS;
    let mut c = [[0u8; CARRY_BYTES]; PRODUCT_COLUMNS - 1];
    let mut carry = BigInt::zero();
    for k in 0..PRODUCT_COLUMNS - 1 {
        let mut col = carry.clone();
        for i in 0..LIMBS64 {
            if k >= i && k - i < LIMBS64 {
                col += BigInt::from(limb64(a, i)) * BigInt::from(limb64(b, k - i));
                col -= BigInt::from(limb64(q, i)) * BigInt::from(limb64(&p.bytes, k - i));
            }
        }
        if k < LIMBS64 {
            col -= BigInt::from(limb64(r, k));
        }
        let next = col.div_floor(&two64);
        let stored = &next + &offset;
        let v = stored.to_biguint()?.to_bytes_le();
        if v.len() > CARRY_BYTES {
            return None;
        }
        c[k][..v.len()].copy_from_slice(&v);
        carry = next;
    }
    Some(c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logup;
    use crate::transcript::Transcript;

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
            row.d = [0u8; 3];
            let ok_products = (0..DEFAULT_RNS_CHANNELS).all(|ch| row.evaluate(&p, ch)[..PRODUCT_COLUMNS].iter().all(|&x| x == 0));
            assert!(ok_products, "product columns should pass for r + P");
            // Best effort for s: any byte value cannot make s + r + 1 = P with r >= P.
            for fill in [0u8, 0xff] {
                row.s = [fill; 32];
                for d0 in [0u8, 1, 255] {
                    row.d = [d0; 3];
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
