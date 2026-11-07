//! Audit H-01, part 2: the EIP-4844 blob polynomial evaluated inside the STARK.
//!
//! One instance of `BlobEvalAir` per blob, 4096 rows (one per field element). For a point `z`
//! (public values), the AIR proves
//!
//! ```text
//! S = sum_i e_i * w_i / (z - w_i)        (mod r_bls, BLS12-381 scalar field)
//! ```
//!
//! for the blob elements `e_i` in its trace and the roots of unity `w_i` in EIP-4844's
//! bit-reversed order (preprocessed), with `S` the second public value. The blob's value is then
//! `p(z) = S * (z^4096 - 1) / 4096`, a constant amount of work done outside (in the Groth16
//! circuit), and the contract checks that value for the blob it carries with the 0x0a
//! point-evaluation precompile.
//!
//! Every value is 32 little-endian bytes, every byte on the global "byte" bus, and every integer
//! identity is checked column by column with carries, as in `ss_rap_v2::uint256` (each column is
//! far below p_BabyBear / 2 in absolute value, so "= 0 mod p" means "= 0 over Z"). Per row:
//!
//! ```text
//! u * d = q1 * P + R         (product, carries C1)
//! e * w = q2 * P + R         (product, carries C2)   => u = e*w/d (mod P)
//! sd + d + 1 = P             (d < P, carries DD)
//! d + w = z + kd * P         (d = z - w mod P, carries AD, kd boolean)
//! acc' = acc + u' - ka' * P  (running sum to the next row, carries AA, ka = ka0 + 2 ka1)
//! e_31 = 0                   (the blob encoding: elements are < 2^248)
//! ```
//!
//! with `acc = u` on the first row and `acc = S` on the last. R, u and acc need not be
//! canonical: only their values mod P matter, and the bounds keep every quotient in 32 bytes.
//!
//! The elements are also committed: a Poseidon2-BabyBear (width 24) sponge absorbs row i's
//! element (31 bytes as 11 values of 3 bytes) in one permutation per row, and the digest D of
//! the last row is the third public value. The point z must be derived from D (and the blob's
//! versioned hash) outside the STARK, so the prover fixes the elements before it learns z.

use num_bigint::BigUint;
use p3_air::{Air, AirBuilder, BaseAir, PermutationAirBuilder, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_lookup::InteractionBuilder;
use p3_matrix::dense::RowMajorMatrix;
use std::sync::OnceLock;

use crate::poseidon2_24;

/// Field elements (rows) per blob.
pub const LOG_ROWS: usize = 12;
pub const ROWS: usize = 1 << LOG_ROWS;
const B: usize = 32;
const PROD_CARRIES: usize = 2 * B - 2; // 62 carries of 2 bytes
const CARRY_OFFSET: i64 = 1 << 14;
const ADD_OFFSET: i64 = 128;

// main columns
const E: usize = 0;
const D: usize = E + B;
const SD: usize = D + B;
const U: usize = SD + B;
const R: usize = U + B;
const Q1: usize = R + B;
const Q2: usize = Q1 + B;
const ACC: usize = Q2 + B;
const C1: usize = ACC + B;
const C2: usize = C1 + 2 * PROD_CARRIES;
const DD: usize = C2 + 2 * PROD_CARRIES;
const AD: usize = DD + B - 1;
const AA: usize = AD + B - 1;
const KD: usize = AA + B - 1;
const KA0: usize = KD + 1;
const KA1: usize = KA0 + 1;
/// Columns that hold bytes (all on the "byte" bus).
const BYTE_COLS: usize = KA1 + 1;
// the commitment: the capacity this row's permutation starts from, then the permutation
const CAP: usize = BYTE_COLS;
const P2: usize = CAP + CAPACITY;
pub const WIDTH: usize = P2 + poseidon2_24::COLS;
/// Poseidon2-24 sponge over the elements: rate 16 (11 used, 3 bytes per BabyBear element),
/// capacity 8, one permutation per row, overwrite mode.
const RATE: usize = 16;
const CAPACITY: usize = poseidon2_24::T - RATE;
/// Felts of the digest of the blob's elements.
pub const DIGEST: usize = 8;
/// Domain tag in the first capacity element ("BLOB").
const TAG: u32 = 0x424c_4f42;
/// Public values: z (32 bytes), S (32 bytes), then the digest D of the elements (8 BabyBear).
pub const PUBLIC_VALUES: usize = 2 * B + DIGEST;

/// BLS12-381 scalar field modulus.
pub fn modulus() -> &'static BigUint {
    static P: OnceLock<BigUint> = OnceLock::new();
    P.get_or_init(|| BigUint::parse_bytes(b"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001", 16).unwrap())
}

fn modulus_bytes() -> &'static [u8; B] {
    static P: OnceLock<[u8; B]> = OnceLock::new();
    P.get_or_init(|| le32(modulus()))
}

/// The 4096 roots of unity in EIP-4844's bit-reversed order.
pub fn roots_brp() -> &'static [BigUint] {
    static W: OnceLock<Vec<BigUint>> = OnceLock::new();
    W.get_or_init(|| {
        let p = modulus();
        let g = BigUint::from(7u32).modpow(&((p - 1u32) / ROWS as u32), p);
        let mut natural = Vec::with_capacity(ROWS);
        let mut x = BigUint::from(1u32);
        for _ in 0..ROWS {
            natural.push(x.clone());
            x = x * &g % p;
        }
        (0..ROWS).map(|i| natural[(i as u32).reverse_bits() as usize >> (32 - LOG_ROWS)].clone()).collect()
    })
}

pub fn le32(x: &BigUint) -> [u8; B] {
    let v = x.to_bytes_le();
    assert!(v.len() <= B, "value above 2^256");
    let mut out = [0u8; B];
    out[..v.len()].copy_from_slice(&v);
    out
}

fn inv(x: &BigUint) -> BigUint {
    let p = modulus();
    x.modpow(&(p - 2u32), p)
}

/// The blob's field elements: 4096 big-endian 32-byte words, each below r_bls.
pub fn elements(blob: &[u8]) -> Option<Vec<BigUint>> {
    if blob.len() != ROWS * B {
        return None;
    }
    blob.chunks(B).map(|c| Some(BigUint::from_bytes_be(c)).filter(|e| e < modulus())).collect()
}

/// Native S for elements `e` at `z` (z not a root of unity).
pub fn barycentric_sum(e: &[BigUint], z: &BigUint) -> BigUint {
    let p = modulus();
    let w = roots_brp();
    let mut s = BigUint::from(0u32);
    for i in 0..ROWS {
        s = (s + &e[i] * &w[i] % p * inv(&((z + p - &w[i]) % p))) % p;
    }
    s
}

/// p(z) from S: S * (z^4096 - 1) / 4096 (the step done outside the STARK).
pub fn value_from_sum(s: &BigUint, z: &BigUint) -> BigUint {
    let p = modulus();
    let zn = (z.modpow(&BigUint::from(ROWS), p) + p - 1u32) % p;
    s * zn % p * inv(&BigUint::from(ROWS)) % p
}

/// Carries of a*b - q*P - r, column by column, stored as 2-byte values with CARRY_OFFSET.
fn product_carries(a: &[u8; B], b: &[u8; B], q: &[u8; B], r: &[u8; B], p: &[u8; B]) -> [[u8; 2]; PROD_CARRIES] {
    let mut out = [[0u8; 2]; PROD_CARRIES];
    let mut carry = 0i64;
    for k in 0..2 * B - 1 {
        let mut col = carry;
        for i in k.saturating_sub(B - 1)..=k.min(B - 1) {
            col += a[i] as i64 * b[k - i] as i64 - q[i] as i64 * p[k - i] as i64;
        }
        if k < B {
            col -= r[k] as i64;
        }
        assert_eq!(col.rem_euclid(256), 0, "product column {k} does not divide");
        carry = col.div_euclid(256);
        if k < PROD_CARRIES {
            let stored = carry + CARRY_OFFSET;
            assert!((0..1 << 16).contains(&stored));
            out[k] = (stored as u16).to_le_bytes();
        } else {
            assert_eq!(carry, 0, "product overflows");
        }
    }
    out
}

/// Carries of sum_j sign_j * x_j (byte vectors) column by column, stored with ADD_OFFSET.
fn add_carries(terms: &[(i64, [u8; B])]) -> [u8; B - 1] {
    let mut out = [0u8; B - 1];
    let mut carry = 0i64;
    for k in 0..B {
        let col: i64 = carry + terms.iter().map(|(s, x)| s * x[k] as i64).sum::<i64>();
        assert_eq!(col.rem_euclid(256), 0, "sum column {k} does not divide");
        carry = col.div_euclid(256);
        if k < B - 1 {
            let stored = carry + ADD_OFFSET;
            assert!((0..256).contains(&stored));
            out[k] = stored as u8;
        } else {
            assert_eq!(carry, 0, "sum overflows");
        }
    }
    out
}

/// Native digest of a blob's elements (the same sponge as the AIR).
pub fn digest<F: PrimeField32>(e: &[BigUint]) -> [F; DIGEST] {
    let mut cols = vec![F::ZERO; poseidon2_24::COLS];
    let mut cap: Vec<F> = (0..CAPACITY).map(|k| F::from_u32(if k == 0 { TAG } else { 0 })).collect();
    let mut out = [F::ZERO; poseidon2_24::T];
    for x in e {
        let eb: Vec<F> = le32(x).iter().map(|&b| F::from_u32(b as u32)).collect();
        out = poseidon2_24::generate(absorb(&eb, &cap), &mut cols);
        cap = out[RATE..].to_vec();
    }
    core::array::from_fn(|k| out[k])
}

/// The trace of one blob at `z`, the sum S it proves and the digest D of its elements.
pub fn trace<F: PrimeField32>(e: &[BigUint], z: &BigUint) -> (RowMajorMatrix<F>, BigUint, [F; DIGEST]) {
    assert_eq!(e.len(), ROWS);
    let p = modulus();
    let pb = modulus_bytes();
    let w = roots_brp();
    let zb = le32(z);
    let mut v = F::zero_vec(ROWS * WIDTH);
    let mut acc = BigUint::from(0u32);
    let mut cap: Vec<F> = (0..CAPACITY).map(|k| F::from_u32(if k == 0 { TAG } else { 0 })).collect();
    let mut sponge = [F::ZERO; poseidon2_24::T];
    for i in 0..ROWS {
        let row = &mut v[i * WIDTH..(i + 1) * WIDTH];
        let put = |row: &mut [F], at: usize, bytes: &[u8]| {
            for (j, &b) in bytes.iter().enumerate() {
                row[at + j] = F::from_u32(b as u32);
            }
        };
        assert!(e[i] < (BigUint::from(1u32) << 248), "blob element above 2^248");
        let d = (z + p - &w[i]) % p;
        assert!(d != BigUint::from(0u32), "z is a root of unity");
        let kd = ((&d + &w[i]) >= (z + p)) as u8; // d + w = z + kd * P
        assert_eq!(&d + &w[i], z + p * kd as u32);
        let ew = &e[i] * &w[i];
        let (q2, rr) = (&ew / p, &ew % p);
        let u = &rr * inv(&d) % p;
        let ud = &u * &d;
        let q1 = &ud / p;
        assert_eq!(&ud % p, rr);
        let sd = p - &d - 1u32;
        let (eb, db, sdb, ub, rb, q1b, q2b, wb) = (le32(&e[i]), le32(&d), le32(&sd), le32(&u), le32(&rr), le32(&q1), le32(&q2), le32(&w[i]));
        put(row, E, &eb);
        put(row, D, &db);
        put(row, SD, &sdb);
        put(row, U, &ub);
        put(row, R, &rb);
        put(row, Q1, &q1b);
        put(row, Q2, &q2b);
        let c1 = product_carries(&ub, &db, &q1b, &rb, pb);
        let c2 = product_carries(&eb, &wb, &q2b, &rb, pb);
        put(row, C1, c1.as_flattened());
        put(row, C2, c2.as_flattened());
        // sd + d + 1 - P = 0
        let mut one = [0u8; B];
        one[0] = 1;
        put(row, DD, &add_carries(&[(1, sdb), (1, db), (1, one), (-1, *pb)]));
        // d + w - z - kd * P = 0
        let kdp = if kd == 1 { *pb } else { [0u8; B] };
        put(row, AD, &add_carries(&[(1, db), (1, wb), (-1, zb), (-1, kdp)]));
        row[KD] = F::from_u32(kd as u32);
        // running sum
        let (next, ka) = if i == 0 { (u.clone(), 0u32) } else {
            let s = &acc + &u;
            let n = &s % p;
            let ka = ((&s - &n) / p).to_u32_digits().first().copied().unwrap_or(0);
            (n, ka)
        };
        let nb = le32(&next);
        put(row, ACC, &nb);
        if i == 0 {
            put(row, AA, &[ADD_OFFSET as u8; B - 1]);
        } else {
            // acc + u - acc' - ka * P = 0, with ka * P = ka0 * P + ka1 * 2P
            let ab = le32(&acc);
            let mut terms = vec![(1, ab), (1, ub), (-1, nb)];
            for _ in 0..ka {
                terms.push((-1, *pb));
            }
            put(row, AA, &add_carries(&terms));
        }
        row[KA0] = F::from_u32(ka & 1);
        row[KA1] = F::from_u32(ka >> 1);
        acc = next;
        // the commitment
        row[CAP..CAP + CAPACITY].copy_from_slice(&cap);
        let input = absorb(&row[E..E + B], &cap);
        sponge = poseidon2_24::generate(input, &mut row[P2..P2 + poseidon2_24::COLS]);
        cap = sponge[RATE..].to_vec();
    }
    (RowMajorMatrix::new(v, WIDTH), acc, core::array::from_fn(|k| sponge[k]))
}

/// Public values of the instance: z then S, one byte each.
pub fn public_values<F: Field>(z: &BigUint, s: &BigUint, d: &[F; DIGEST]) -> Vec<F> {
    le32(z).iter().chain(le32(s).iter()).map(|&b| F::from_u32(b as u32)).chain(d.iter().copied()).collect()
}

/// Byte counts of a trace (for the shared `ByteTableAir`).
pub fn byte_counts<F: Field + p3_field::PrimeField32>(t: &RowMajorMatrix<F>, m: &mut [u64; 256]) {
    for row in t.values.chunks(WIDTH) {
        for x in &row[..BYTE_COLS] {
            m[x.as_canonical_u32() as usize] += 1;
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct BlobEvalAir;

impl<F: Field> BaseAir<F> for BlobEvalAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let w = roots_brp();
        Some(RowMajorMatrix::new(w.iter().flat_map(|x| le32(x).map(|b| F::from_u32(b as u32))).collect(), B))
    }
    fn preprocessed_width(&self) -> usize {
        B
    }
    fn num_public_values(&self) -> usize {
        PUBLIC_VALUES
    }
}

/// The permutation input of a row: the element's bytes, 3 per value, then the capacity.
fn absorb<R: PrimeCharacteristicRing>(e: &[R], cap: &[R]) -> [R; poseidon2_24::T] {
    core::array::from_fn(|k| {
        if k < 11 {
            (0..3).filter(|j| 3 * k + j < B).fold(R::ZERO, |acc, j| acc + e[3 * k + j].clone() * R::from_u32(1 << (8 * j)))
        } else if k < RATE {
            R::ZERO
        } else {
            cap[k - RATE].clone()
        }
    })
}

fn product<AB: AirBuilder>(builder: &mut AB, a: &[AB::Expr], b: &[AB::Expr], q: &[AB::Expr], r: &[AB::Expr], c: &[AB::Expr], p: &[u8; B]) {
    let k256 = AB::Expr::from_u32(256);
    let carry = |k: usize| c[2 * k].clone() + c[2 * k + 1].clone() * k256.clone() - AB::Expr::from_u32(CARRY_OFFSET as u32);
    for k in 0..2 * B - 1 {
        let mut e = AB::Expr::ZERO;
        for i in k.saturating_sub(B - 1)..=k.min(B - 1) {
            e += a[i].clone() * b[k - i].clone() - q[i].clone() * AB::Expr::from_u32(p[k - i] as u32);
        }
        if k > 0 {
            e += carry(k - 1);
        }
        if k < B {
            e -= r[k].clone();
        }
        if k < PROD_CARRIES {
            e -= carry(k) * k256.clone();
        }
        builder.assert_zero(e);
    }
}

/// sum of the byte-vector terms (already signed and scaled), column by column with carries.
fn sum_zero<AB: AirBuilder>(builder: &mut AB, cols: &[AB::Expr], carries: &[AB::Expr]) {
    let k256 = AB::Expr::from_u32(256);
    let off = AB::Expr::from_u32(ADD_OFFSET as u32);
    for k in 0..B {
        let mut e = cols[k].clone();
        if k > 0 {
            e += carries[k - 1].clone() - off.clone();
        }
        if k < B - 1 {
            e -= (carries[k].clone() - off.clone()) * k256.clone();
        }
        builder.assert_zero(e);
    }
}

impl<AB> Air<AB> for BlobEvalAir
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let c: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let n: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pre = builder.preprocessed();
        let w: Vec<AB::Expr> = pre.current_slice().iter().map(|&x| x.into()).collect();
        let pv: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let (z, s) = (&pv[..B], &pv[B..2 * B]);
        let p = modulus_bytes();
        let pk = |k: usize| AB::Expr::from_u32(p[k] as u32);
        let col = |v: &[AB::Expr], at: usize| v[at..at + B].to_vec();

        product(builder, &col(&c, U), &col(&c, D), &col(&c, Q1), &col(&c, R), &c[C1..C1 + 2 * PROD_CARRIES], p);
        product(builder, &col(&c, E), &w, &col(&c, Q2), &col(&c, R), &c[C2..C2 + 2 * PROD_CARRIES], p);
        // sd + d + 1 - P
        let cols: Vec<AB::Expr> = (0..B).map(|k| c[SD + k].clone() + c[D + k].clone() + if k == 0 { AB::Expr::ONE } else { AB::Expr::ZERO } - pk(k)).collect();
        sum_zero(builder, &cols, &c[DD..DD + B - 1]);
        // d + w - z - kd * P
        let kd = c[KD].clone();
        builder.assert_bool(kd.clone());
        let cols: Vec<AB::Expr> = (0..B).map(|k| c[D + k].clone() + w[k].clone() - z[k].clone() - kd.clone() * pk(k)).collect();
        sum_zero(builder, &cols, &c[AD..AD + B - 1]);
        // the blob encoding keeps every element below 2^248
        builder.assert_zero(c[E + B - 1].clone());
        // running sum
        builder.assert_bool(c[KA0].clone());
        builder.assert_bool(c[KA1].clone());
        for k in 0..B {
            builder.when_first_row().assert_eq(c[ACC + k].clone(), c[U + k].clone());
            builder.when_last_row().assert_eq(c[ACC + k].clone(), s[k].clone());
        }
        let ka = n[KA0].clone() + n[KA1].clone() * AB::Expr::from_u32(2);
        let cols: Vec<AB::Expr> = (0..B).map(|k| c[ACC + k].clone() + n[U + k].clone() - n[ACC + k].clone() - ka.clone() * pk(k)).collect();
        {
            let mut t = builder.when_transition();
            sum_zero(&mut t, &cols, &n[AA..AA + B - 1]);
        }
        // the commitment
        let input = absorb(&c[E..E + B], &c[CAP..CAP + CAPACITY]);
        let out = poseidon2_24::eval(builder, input, &c[P2..P2 + poseidon2_24::COLS]);
        for k in 0..CAPACITY {
            builder.when_first_row().assert_eq(c[CAP + k].clone(), AB::Expr::from_u32(if k == 0 { TAG } else { 0 }));
            builder.when_transition().assert_eq(n[CAP + k].clone(), out[RATE + k].clone());
        }
        for k in 0..DIGEST {
            builder.when_last_row().assert_eq(out[k].clone(), pv[2 * B + k].clone());
        }
        for j in 0..BYTE_COLS {
            builder.push_interaction("byte", [c[j].clone()], 1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{config, BabyBear, Config};
    use crate::mulmod::ByteTableAir;
    use p3_air::{Air, BaseAir};
    use p3_batch_stark::{prove_batch, verify_batch, ProverData, StarkInstance};
    use p3_lookup::InteractionBuilder;

    #[derive(Clone, Debug)]
    enum Airs {
        Blob(BlobEvalAir),
        Table(ByteTableAir),
    }
    impl<F: Field> BaseAir<F> for Airs {
        fn width(&self) -> usize {
            match self {
                Self::Blob(a) => <BlobEvalAir as BaseAir<F>>::width(a),
                Self::Table(a) => <ByteTableAir as BaseAir<F>>::width(a),
            }
        }
        fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
            match self {
                Self::Blob(a) => a.preprocessed_trace(),
                Self::Table(a) => a.preprocessed_trace(),
            }
        }
        fn preprocessed_width(&self) -> usize {
            match self {
                Self::Blob(a) => <BlobEvalAir as BaseAir<F>>::preprocessed_width(a),
                Self::Table(a) => <ByteTableAir as BaseAir<F>>::preprocessed_width(a),
            }
        }
        fn num_public_values(&self) -> usize {
            match self {
                Self::Blob(a) => <BlobEvalAir as BaseAir<F>>::num_public_values(a),
                Self::Table(_) => 0,
            }
        }
    }
    impl<AB: AirBuilder + PermutationAirBuilder + InteractionBuilder> Air<AB> for Airs {
        fn eval(&self, builder: &mut AB) {
            match self {
                Self::Blob(a) => a.eval(builder),
                Self::Table(a) => a.eval(builder),
            }
        }
    }

    fn blob_elements(seed: u64) -> Vec<BigUint> {
        let mut s = seed;
        (0..ROWS)
            .map(|_| {
                let mut b = [0u8; 31];
                for x in b.iter_mut() {
                    s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    *x = (s >> 56) as u8;
                }
                BigUint::from_bytes_be(&b)
            })
            .collect()
    }

    fn prove_and_verify(e: &[BigUint], z: &BigUint, claimed: Option<&BigUint>) -> bool {
        prove_and_verify_with(e, z, claimed, None, None, |_| {})
    }

    /// Proves the trace of `e` at `z` (after `tamper`), verifies it against `claimed` (default:
    /// the honest S) at `z_verify` (default: z). A prover panic counts as rejection.
    fn prove_and_verify_with(e: &[BigUint], z: &BigUint, claimed: Option<&BigUint>, z_verify: Option<&BigUint>, digest_verify: Option<usize>, tamper: impl Fn(&mut RowMajorMatrix<BabyBear>)) -> bool {
        let (mut t, s, d) = trace::<BabyBear>(e, z);
        tamper(&mut t);
        let mut m = [0u64; 256];
        byte_counts(&t, &mut m);
        let table = ByteTableAir::from_counts::<BabyBear>(&m);
        let cfg = config::<BabyBear>(1, 8);
        let airs = vec![Airs::Blob(BlobEvalAir), Airs::Table(ByteTableAir)];
        let pd = ProverData::<Config<BabyBear>>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &[LOG_ROWS, 8], &[3, 3], 1).unwrap();
        let pv_prove = vec![public_values::<BabyBear>(z, &s, &d), vec![]];
        let traces = [&t, &table];
        let inst = StarkInstance::new_multiple(&airs, &traces, &pv_prove);
        let Ok(Ok(proof)) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove_batch(&cfg, &inst, &pd))) else {
            return false;
        };
        let mut dv = d;
        if let Some(i) = digest_verify {
            dv[i] += BabyBear::ONE;
        }
        let pv = vec![public_values::<BabyBear>(z_verify.unwrap_or(z), claimed.unwrap_or(&s), &dv), vec![]];
        verify_batch(&cfg, &airs, &proof, &pv, &pd.common).is_ok()
    }

    #[test]
    fn witness_sum_matches_the_barycentric_formula() {
        let e = blob_elements(3);
        let z = BigUint::from(0x1234_5678_9abc_def0u64) * BigUint::from(0xfedc_ba98u64);
        let (_, s, d) = trace::<BabyBear>(&e, &z);
        assert_eq!(s, barycentric_sum(&e, &z));
        assert_eq!(d, digest::<BabyBear>(&e));
        let mut e2 = e.clone();
        e2[4095] += 1u32;
        assert_ne!(d, digest::<BabyBear>(&e2), "the digest covers the last element");
        // and p(z) from S is the polynomial through the elements: at z = w_j the limit is e_j,
        // so check against a direct Lagrange evaluation instead (independent formula)
        let p = modulus();
        let w = roots_brp();
        let y = value_from_sum(&s, &z);
        let mut direct = BigUint::from(0u32);
        // p(z) = sum_i e_i * L_i(z), L_i(z) = (z^n - 1) * w_i / (n * (z - w_i))
        let zn = (z.modpow(&BigUint::from(ROWS), p) + p - 1u32) % p;
        let ninv = inv(&BigUint::from(ROWS));
        for i in 0..ROWS {
            direct = (direct + &e[i] * &zn % p * &w[i] % p * &ninv % p * inv(&((&z + p - &w[i]) % p))) % p;
        }
        assert_eq!(y, direct);
    }

    #[test]
    fn blob_evaluation_proves_and_a_wrong_sum_does_not_verify() {
        let e = blob_elements(7);
        let z = BigUint::parse_bytes(b"5ab1e0f00dcafe0123456789abcdef0123456789abcdef0123456789abcdef", 16).unwrap() % modulus();
        assert!(prove_and_verify(&e, &z, None), "honest");
        let s = barycentric_sum(&e, &z);
        let wrong = (s + 1u32) % modulus();
        assert!(!prove_and_verify(&e, &z, Some(&wrong)), "a sum the trace does not have");
        // the same proof at another point
        let z2 = (&z + 1u32) % modulus();
        assert!(!prove_and_verify_with(&e, &z, None, Some(&z2), None, |_| {}), "another z");
        // a trace whose element 5 was changed after the witness was made
        let tamper_e = |t: &mut RowMajorMatrix<BabyBear>| t.values[5 * WIDTH + E + 3] += BabyBear::ONE;
        assert!(!prove_and_verify_with(&e, &z, None, None, None, tamper_e), "element changed");
        // a running sum that skips row 100's term
        let tamper_acc = |t: &mut RowMajorMatrix<BabyBear>| t.values[100 * WIDTH + U] += BabyBear::ONE;
        assert!(!prove_and_verify_with(&e, &z, None, None, None, tamper_acc), "term changed");
        // another digest for the same elements
        assert!(!prove_and_verify_with(&e, &z, None, None, Some(3), |_| {}), "another digest");
        // an element changed with its whole row recomputed (sum and permutation), but the
        // capacity chain left as it was: the next row's permutation no longer starts from it
        let (t2, _, _) = trace::<BabyBear>(&{ let mut x = e.clone(); x[9] += 1u32; x }, &z);
        let swap = |t: &mut RowMajorMatrix<BabyBear>| t.values[9 * WIDTH..10 * WIDTH].copy_from_slice(&t2.values[9 * WIDTH..10 * WIDTH]);
        assert!(!prove_and_verify_with(&e, &z, None, None, None, swap), "element swapped in");
    }
}
