//! RNS-256: carry-free 256-bit modular multiplication for EVM-native fields.
//!
//! Ethereum's expensive operations inside a zkEVM are 256-bit: `MULMOD`/`ADDMOD`, and the
//! `ecrecover` (secp256k1) and `ecAdd`/`ecMul`/`ecPairing` (BN254) precompiles. Small-field
//! STARK provers (31-bit BabyBear/KoalaBear) normally emulate a 256-bit multiply with ~64 limb
//! products plus carry propagation and carry range checks.
//!
//! Here a 256-bit value is represented by its residues modulo N independent 31-bit NTT-friendly
//! primes whose product M exceeds 2^514. A multiply `a*b = q*P + r` then becomes N independent
//! 31-bit multiply-reduce operations: no carries, no cross-lane communication, one GPU thread
//! (or SIMD lane) per channel. Soundness comes from tying every residue vector to the same
//! range-checked byte decomposition (32 limbs of 8 bits), which pins each one to a single
//! integer below 2^256; the identity then holds over Z because its magnitude is below M.
//!
//! Constraint set per row and per channel j (all must equal 0 mod m_j):
//!   tie(a), tie(b), tie(q), tie(r), tie(s)                        -- residues match byte limbs
//!   a*b - q*P - r                                                  -- product identity
//!   s + r + 1 - P                                                  -- canonical remainder: r < P
//! Byte limbs are range-checked with a LogUp lookup into [0, 255] (see `lib.rs`).

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};
use rayon::prelude::*;

pub const LIMBS: usize = 32;
/// log2(M) must exceed this: |a*b - q*P - r| < 2^513 and |s + r + 1 - P| < 2^257.
pub const REQUIRED_MODULUS_BITS: f64 = 514.0;
/// Minimum two-adicity of every channel prime (NTT domains up to 2^20 per channel).
pub const MIN_TWO_ADICITY: u32 = 20;

/// secp256k1 base field prime (ecrecover / ECDSA).
pub const SECP256K1_P_HEX: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
/// BN254 (alt_bn128) base field prime (EIP-196/197 precompiles).
pub const BN254_P_HEX: &str = "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47";

fn is_prime_u32(n: u32) -> bool {
    if n < 2 {
        return false;
    }
    for p in [2u32, 3, 5, 7] {
        if n % p == 0 {
            return n == p;
        }
    }
    let n64 = n as u64;
    let mut d = n64 - 1;
    let mut s = 0;
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    let pow = |mut b: u64, mut e: u64| {
        let mut r = 1u64;
        b %= n64;
        while e > 0 {
            if e & 1 == 1 {
                r = r * b % n64;
            }
            b = b * b % n64;
            e >>= 1;
        }
        r
    };
    // Bases {2,3,5,7} are deterministic for n < 3,215,031,751 (> 2^31).
    'outer: for a in [2u64, 3, 5, 7] {
        let mut x = pow(a, d);
        if x == 1 || x == n64 - 1 {
            continue;
        }
        for _ in 1..s {
            x = x * x % n64;
            if x == n64 - 1 {
                continue 'outer;
            }
        }
        return false;
    }
    true
}

/// One RNS channel: prime modulus with precomputed Barrett constant floor(2^64 / m).
#[derive(Clone, Copy, Debug)]
pub struct Channel {
    pub m: u32,
    pub mu: u64,
    /// 256^k mod m for k = 0..32, used by the limb-tie constraint.
    pub pow256: [u32; LIMBS],
}

impl Channel {
    fn new(m: u32) -> Self {
        let mu = (u128::from(u64::MAX) + 1) / m as u128;
        let mut pow256 = [0u32; LIMBS];
        let mut acc = 1u64;
        for p in pow256.iter_mut() {
            *p = acc as u32;
            acc = acc * 256 % m as u64;
        }
        Self { m, mu: mu as u64, pow256 }
    }

    // All helpers are branchless: `min(x, x - m)` with wrapping arithmetic compiles to a
    // conditional move, so random data causes no branch mispredictions.

    #[inline(always)]
    pub fn reduce(&self, val: u64) -> u32 {
        let m = self.m as u64;
        let q = ((val as u128 * self.mu as u128) >> 64) as u64;
        let r = val.wrapping_sub(q.wrapping_mul(m)); // r < 3m
        let r = r.min(r.wrapping_sub(m));
        r.min(r.wrapping_sub(m)) as u32
    }

    #[inline(always)]
    pub fn mul(&self, a: u32, b: u32) -> u32 {
        self.reduce(a as u64 * b as u64)
    }

    #[inline(always)]
    pub fn add(&self, a: u32, b: u32) -> u32 {
        let s = a + b; // a, b < m < 2^31, so no u32 overflow
        s.min(s.wrapping_sub(self.m))
    }

    #[inline(always)]
    pub fn sub(&self, a: u32, b: u32) -> u32 {
        let d = a.wrapping_sub(b);
        d.min(d.wrapping_add(self.m))
    }

    /// sum_k limbs[k] * 256^k  (mod m)
    #[inline(always)]
    pub fn from_limbs(&self, limbs: &[u8; LIMBS]) -> u32 {
        let mut acc = 0u64;
        // 32 terms each < 2^8 * 2^31 = 2^39 -> sum < 2^44, one reduction at the end.
        for k in 0..LIMBS {
            acc += limbs[k] as u64 * self.pow256[k] as u64;
        }
        self.reduce(acc)
    }
}

/// An RNS basis large enough for sound 256 x 256-bit modular multiplication.
#[derive(Clone, Debug)]
pub struct Rns256Basis {
    pub channels: Vec<Channel>,
    pub modulus_bits: f64,
}

impl Rns256Basis {
    /// Starts from the five v2.0 primes (so the 64-bit pipeline's channels are a strict subset),
    /// then adds the largest primes m = k * 2^20 + 1 < 2^31 until log2(M) > 514. Deterministic.
    pub fn canonical() -> Self {
        let step = 1u64 << MIN_TWO_ADICITY;
        let mut channels: Vec<Channel> = crate::RNS_MODULI.iter().map(|&m| Channel::new(m)).collect();
        let mut bits: f64 = crate::RNS_MODULI.iter().map(|&m| (m as f64).log2()).sum();
        let mut k = ((1u64 << 31) - 2) / step;
        while bits <= REQUIRED_MODULUS_BITS {
            let cand = k * step + 1;
            if is_prime_u32(cand as u32) && !crate::RNS_MODULI.contains(&(cand as u32)) {
                channels.push(Channel::new(cand as u32));
                bits += (cand as f64).log2();
            }
            k -= 1;
        }
        Self { channels, modulus_bits: bits }
    }

    pub fn len(&self) -> usize {
        self.channels.len()
    }

    pub fn is_empty(&self) -> bool {
        self.channels.is_empty()
    }

    pub fn modulus(&self) -> BigUint {
        self.channels.iter().fold(BigUint::one(), |acc, c| acc * c.m)
    }

    pub fn residues(&self, x: &BigUint) -> Vec<u32> {
        self.channels
            .iter()
            .map(|c| (x % c.m).iter_u32_digits().next().unwrap_or(0))
            .collect()
    }

    /// CRT reconstruction (verifier/debug side only; never needed on the prover hot path).
    pub fn reconstruct(&self, res: &[u32]) -> BigUint {
        let m = self.modulus();
        let mut acc = BigUint::zero();
        for (c, &r) in self.channels.iter().zip(res) {
            let mi = &m / c.m;
            let mi_mod = (&mi % c.m).iter_u32_digits().next().unwrap_or(0);
            let inv = crate::mod_inv_single(mi_mod, c.m);
            acc += mi * ((r as u64 * inv as u64) % c.m as u64);
        }
        acc % m
    }
}

/// Target modulus P prepared for a given basis.
#[derive(Clone, Debug)]
pub struct TargetField {
    pub p: BigUint,
    pub p_res: Vec<u32>,
    pub p_limbs: [u8; LIMBS],
}

impl TargetField {
    pub fn from_hex(hex: &str, basis: &Rns256Basis) -> Self {
        let p = BigUint::parse_bytes(hex.as_bytes(), 16).expect("bad hex");
        assert!(p.bits() <= 256);
        let p_res = basis.residues(&p);
        Self { p_limbs: to_limbs(&p), p, p_res }
    }
}

pub fn to_limbs(x: &BigUint) -> [u8; LIMBS] {
    let bytes = x.to_bytes_le();
    assert!(bytes.len() <= LIMBS, "value exceeds 256 bits");
    let mut out = [0u8; LIMBS];
    out[..bytes.len()].copy_from_slice(&bytes);
    out
}

pub fn from_limbs(l: &[u8; LIMBS]) -> BigUint {
    BigUint::from_bytes_le(l)
}

/// Witness row for r = a * b mod P. `s = P - 1 - r` proves r is canonical (r < P).
#[derive(Clone, Debug)]
pub struct MulModRow {
    pub a: [u8; LIMBS],
    pub b: [u8; LIMBS],
    pub q: [u8; LIMBS],
    pub r: [u8; LIMBS],
    pub s: [u8; LIMBS],
    /// Residues, channel-major per operand: [a, b, q, r, s][channel].
    pub res: [Vec<u32>; 5],
}

pub const NUM_CONSTRAINTS: usize = 7;

impl MulModRow {
    pub fn generate(a: &BigUint, b: &BigUint, f: &TargetField, basis: &Rns256Basis) -> Self {
        let a = a % &f.p;
        let b = b % &f.p;
        let (q, r) = (&a * &b).div_rem(&f.p);
        let s = &f.p - 1u32 - &r;
        let limbs = [to_limbs(&a), to_limbs(&b), to_limbs(&q), to_limbs(&r), to_limbs(&s)];
        // Residues straight from byte limbs: 32 multiply-adds + 1 Barrett per channel, no bigint `%`.
        let res = std::array::from_fn(|op| basis.channels.iter().map(|c| c.from_limbs(&limbs[op])).collect());
        let [a, b, q, r, s] = limbs;
        Self { a, b, q, r, s, res }
    }

    pub fn remainder(&self) -> BigUint {
        from_limbs(&self.r)
    }

    /// All constraints for channel `j`. Pure 31-bit arithmetic, no carries, no `%`.
    #[inline]
    pub fn constraints(&self, j: usize, f: &TargetField, basis: &Rns256Basis) -> [u32; NUM_CONSTRAINTS] {
        let c = &basis.channels[j];
        let [ra, rb, rq, rr, rs] = [self.res[0][j], self.res[1][j], self.res[2][j], self.res[3][j], self.res[4][j]];
        let p = f.p_res[j];
        let prod = c.sub(c.sub(c.mul(ra, rb), c.mul(rq, p)), rr);
        let canon = c.sub(c.add(c.add(rs, rr), 1 % c.m), p);
        [
            c.sub(ra, c.from_limbs(&self.a)),
            c.sub(rb, c.from_limbs(&self.b)),
            c.sub(rq, c.from_limbs(&self.q)),
            c.sub(rr, c.from_limbs(&self.r)),
            c.sub(rs, c.from_limbs(&self.s)),
            prod,
            canon,
        ]
    }

    pub fn is_satisfied(&self, f: &TargetField, basis: &Rns256Basis) -> bool {
        (0..basis.len()).all(|j| self.constraints(j, f, basis).iter().all(|&x| x == 0))
    }
}

/// Struct-of-arrays batch: `lanes[op][channel][row]`. This is the layout a GPU kernel consumes:
/// one contiguous u32 column per (operand, channel), fully coalesced, no cross-channel traffic.
pub struct MulModBatch {
    pub rows: usize,
    pub lanes: [Vec<Vec<u32>>; 5],
}

impl MulModBatch {
    pub fn from_rows(rows: &[MulModRow], basis: &Rns256Basis) -> Self {
        let n = basis.len();
        let lanes = std::array::from_fn(|op| {
            (0..n).map(|j| rows.iter().map(|r| r.res[op][j]).collect()).collect()
        });
        Self { rows: rows.len(), lanes }
    }

    /// Evaluates the product identity for every (channel, row) in parallel.
    /// Returns the number of violated cells (0 for a valid batch).
    pub fn eval_product_identity(&self, f: &TargetField, basis: &Rns256Basis) -> usize {
        (0..basis.len())
            .into_par_iter()
            .map(|j| {
                let c = &basis.channels[j];
                let p = f.p_res[j];
                let (a, b, q, r) = (&self.lanes[0][j], &self.lanes[1][j], &self.lanes[2][j], &self.lanes[3][j]);
                a.par_chunks(4096)
                    .zip(b.par_chunks(4096))
                    .zip(q.par_chunks(4096))
                    .zip(r.par_chunks(4096))
                    .map(|(((a, b), q), r)| {
                        a.iter()
                            .zip(b)
                            .zip(q)
                            .zip(r)
                            .filter(|&(((&a, &b), &q), &r)| c.sub(c.sub(c.mul(a, b), c.mul(q, p)), r) != 0)
                            .count()
                    })
                    .sum::<usize>()
            })
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup() -> (Rns256Basis, TargetField, TargetField) {
        let basis = Rns256Basis::canonical();
        let secp = TargetField::from_hex(SECP256K1_P_HEX, &basis);
        let bn = TargetField::from_hex(BN254_P_HEX, &basis);
        (basis, secp, bn)
    }

    fn big(hex: &str) -> BigUint {
        BigUint::parse_bytes(hex.as_bytes(), 16).unwrap()
    }

    #[test]
    fn basis_is_large_enough_and_ntt_friendly() {
        let (basis, _, _) = setup();
        assert!(basis.modulus().bits() as f64 > REQUIRED_MODULUS_BITS);
        for c in &basis.channels {
            assert!(is_prime_u32(c.m));
            assert_eq!((c.m - 1) % (1 << MIN_TWO_ADICITY), 0);
        }
        // Includes the v2.0 primes.
        for p in crate::RNS_MODULI {
            assert!(basis.channels.iter().any(|c| c.m == p), "missing v2.0 prime {p}");
        }
        let mut ms: Vec<u32> = basis.channels.iter().map(|c| c.m).collect();
        ms.sort_unstable();
        ms.dedup();
        assert_eq!(ms.len(), basis.len());
    }

    #[test]
    fn barrett_matches_reference() {
        let (basis, _, _) = setup();
        for c in &basis.channels {
            for v in [0u64, 1, c.m as u64, u64::MAX, 0xdead_beef_cafe_babe, (c.m as u64 - 1).pow(2)] {
                assert_eq!(c.reduce(v) as u64, v % c.m as u64);
            }
        }
    }

    #[test]
    fn crt_roundtrip() {
        let (basis, secp, _) = setup();
        let x = &secp.p - 12345u32;
        assert_eq!(basis.reconstruct(&basis.residues(&x)), x);
    }

    #[test]
    fn honest_rows_satisfy_on_secp256k1_and_bn254() {
        let (basis, secp, bn) = setup();
        let cases = [
            (big("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"),
             big("483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8")),
            (big("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e"),
             big("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e")),
            (BigUint::zero(), big("1234")),
            (BigUint::one(), BigUint::one()),
        ];
        for f in [&secp, &bn] {
            for (a, b) in &cases {
                let row = MulModRow::generate(a, b, f, &basis);
                assert_eq!(row.remainder(), (a % &f.p) * (b % &f.p) % &f.p);
                assert!(row.is_satisfied(f, &basis));
            }
        }
    }

    /// Attack 1: claim a wrong remainder and solve for a matching quotient *residue* per channel.
    #[test]
    fn forged_remainder_rejected() {
        let (basis, f, _) = setup();
        let mut row = MulModRow::generate(&big("abcdef0123456789"), &big("fedcba9876543210ffff"), &f, &basis);
        let fake_r = BigUint::from(7u32);
        row.r = to_limbs(&fake_r);
        row.res[3] = basis.residues(&fake_r);
        let s = &f.p - 1u32 - &fake_r;
        row.s = to_limbs(&s);
        row.res[4] = basis.residues(&s);
        for (j, c) in basis.channels.iter().enumerate() {
            let lhs = c.sub(c.mul(row.res[0][j], row.res[1][j]), row.res[3][j]);
            row.res[2][j] = c.mul(lhs, crate::mod_inv_single(f.p_res[j], c.m));
        }
        assert!(!row.is_satisfied(&f, &basis));
    }

    /// Attack 2: non-canonical remainder r' = r + P (still < 2^256 for small r) with q' = q - 1.
    #[test]
    fn non_canonical_remainder_rejected() {
        let (basis, f, _) = setup();
        // a*b slightly above P so r is tiny and r + P < 2^256.
        let a = &f.p - 1u32;
        let b = &f.p - 1u32; // (P-1)^2 = q*P + 1
        let honest = MulModRow::generate(&a, &b, &f, &basis);
        assert_eq!(honest.remainder(), BigUint::one());
        let q = from_limbs(&honest.q);
        let r2 = BigUint::one() + &f.p;
        assert!(r2.bits() <= 256);
        let q2 = q - 1u32;
        let mut row = honest.clone();
        row.r = to_limbs(&r2);
        row.res[3] = basis.residues(&r2);
        row.q = to_limbs(&q2);
        row.res[2] = basis.residues(&q2);
        // Product identity alone would accept this:
        assert!((0..basis.len()).all(|j| row.constraints(j, &f, &basis)[5] == 0));
        // ... but no s in [0, 2^256) satisfies s + r2 + 1 = P.
        assert!(!row.is_satisfied(&f, &basis));
    }

    #[test]
    fn soa_batch_matches_rows() {
        let (basis, f, _) = setup();
        let rows: Vec<MulModRow> = (1..64u32)
            .map(|i| MulModRow::generate(&(BigUint::from(i).pow(40)), &(BigUint::from(i + 7).pow(33)), &f, &basis))
            .collect();
        let mut batch = MulModBatch::from_rows(&rows, &basis);
        assert_eq!(batch.eval_product_identity(&f, &basis), 0);
        batch.lanes[3][0][5] ^= 1;
        assert_eq!(batch.eval_product_identity(&f, &basis), 1);
    }
}
