//! Audit H-01, part 2: the EIP-4844 blob polynomial evaluated inside the STARK.
//!
//! One instance of `BlobEvalAir` holds `slots` blobs (a power of two), 4096 rows each (one per
//! field element), so the verifier's work does not grow with the number of blobs. For one point
//! `z` (public values, the same for every blob), the AIR proves for each blob j
//!
//! ```text
//! S = sum_i e_i * w_i / (z - w_i)        (mod r_bls, BLS12-381 scalar field)
//! ```
//!
//! for the blob elements `e_i` in its rows and the roots of unity `w_i` in EIP-4844's
//! bit-reversed order (preprocessed), with `S_j` a public value. Preprocessed selectors mark the
//! first row of every blob (where the running sum and the sponge restart) and the last row of
//! blob j (where they are read out). A slot without a blob holds zero elements, so its S_j is 0. The blob's value is then
//! `p(z) = S * (z^4096 - 1) / 4096`, a constant amount of work done outside (in the Groth16
//! circuit), and the contract checks that value for the blob it carries with the 0x0a
//! point-evaluation precompile.
//!
//! Every value is 32 little-endian bytes, every byte range-checked (two at a time, on the global
//! "byte2" bus to `BytePairTableAir`), and every integer identity is checked column by column
//! with carries, as in `ss_rap_v2::uint256` (each column is far below p_BabyBear / 2 in absolute
//! value, so "= 0 mod p" means "= 0 over Z"). Per row:
//!
//! ```text
//! u * d + q2 * P = e * w + q1 * P   (one convolution, carries C)   => u = e*w/d (mod P)
//! d + w = z + kd * P                (d = z - w mod P, carries AD, kd boolean)
//! acc' = acc + u' - ka' * P         (running sum to the next row, carries AA, ka = ka0 + 2 ka1)
//! e_31 = 0                          (the blob encoding: elements are < 2^248)
//! ```
//!
//! with `acc = u` on the first row of a blob and `acc = S_j` on its last. d, u and acc need not
//! be canonical: only their values mod P matter (d = z - w_i mod P is never 0 for z outside the
//! roots of unity), the bounds keep every quotient in 32 bytes, and the settlement circuit takes
//! S_j as canonical bytes.
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
const CARRY_OFFSET: i64 = 1 << 15;
const ADD_OFFSET: i64 = 128;

// main columns: bytes first (an even number of them, range-checked in pairs)
const E: usize = 0;
const D: usize = E + B;
const U: usize = D + B;
const Q1: usize = U + B;
const Q2: usize = Q1 + B;
const ACC: usize = Q2 + B;
const C: usize = ACC + B;
const AD: usize = C + 2 * PROD_CARRIES;
const AA: usize = AD + B - 1;
/// Columns that hold bytes.
const BYTE_COLS: usize = AA + B - 1;
const KD: usize = BYTE_COLS;
const KA0: usize = KD + 1;
const KA1: usize = KA0 + 1;
// the commitment: the capacity this row's permutation starts from, then the permutation
const CAP: usize = KA1 + 1;
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
/// Public values: z (32 bytes), then per slot S_j (32 bytes) and the digest D_j (8 BabyBear).
pub const PER_SLOT: usize = B + DIGEST;
// preprocessed columns: the root w_i, "first row of a blob", then "last row of blob j"
const PRE_W: usize = 0;
const PRE_FIRST: usize = B;
const PRE_LAST: usize = B + 1;

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

/// Carries of sum_t sign_t * a_t * b_t (byte vectors), column by column, stored as 2-byte
/// values with CARRY_OFFSET.
fn product_carries(terms: &[(i64, &[u8; B], &[u8; B])]) -> [[u8; 2]; PROD_CARRIES] {
    let mut out = [[0u8; 2]; PROD_CARRIES];
    let mut carry = 0i64;
    for k in 0..2 * B - 1 {
        let mut col = carry;
        for i in k.saturating_sub(B - 1)..=k.min(B - 1) {
            for (sg, a, b) in terms {
                col += sg * a[i] as i64 * b[k - i] as i64;
            }
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

/// The trace of `slots` blobs (the given ones, then empty slots) at `z`, with the sums S_j and
/// digests D_j it proves.
pub fn trace<F: PrimeField32>(blobs: &[Vec<BigUint>], slots: usize, z: &BigUint) -> (RowMajorMatrix<F>, Vec<BigUint>, Vec<[F; DIGEST]>) {
    assert!(slots.is_power_of_two() && blobs.len() <= slots, "{} blobs for {slots} slots", blobs.len());
    let zero = vec![BigUint::from(0u32); ROWS];
    let mut v = F::zero_vec(slots * ROWS * WIDTH);
    let (mut ss, mut ds) = (vec![], vec![]);
    for (j, rows) in v.chunks_mut(ROWS * WIDTH).enumerate() {
        let (s, d) = blob_rows(blobs.get(j).unwrap_or(&zero), z, rows);
        ss.push(s);
        ds.push(d);
    }
    (RowMajorMatrix::new(v, WIDTH), ss, ds)
}

/// One blob's 4096 rows (written to `v`), its sum S and digest D.
fn blob_rows<F: PrimeField32>(e: &[BigUint], z: &BigUint, v: &mut [F]) -> (BigUint, [F; DIGEST]) {
    assert_eq!(e.len(), ROWS);
    let p = modulus();
    let pb = modulus_bytes();
    let w = roots_brp();
    let zb = le32(z);
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
        // u = e w / d, with u d = q1 P + r and e w = q2 P + r
        let ew = &e[i] * &w[i];
        let (q2, rr) = (&ew / p, &ew % p);
        let u = &rr * inv(&d) % p;
        let ud = &u * &d;
        let q1 = &ud / p;
        assert_eq!(&ud % p, rr);
        let (eb, db, ub, q1b, q2b, wb) = (le32(&e[i]), le32(&d), le32(&u), le32(&q1), le32(&q2), le32(&w[i]));
        put(row, E, &eb);
        put(row, D, &db);
        put(row, U, &ub);
        put(row, Q1, &q1b);
        put(row, Q2, &q2b);
        // u d + q2 P - e w - q1 P = 0
        let c = product_carries(&[(1, &ub, &db), (1, &q2b, pb), (-1, &eb, &wb), (-1, &q1b, pb)]);
        put(row, C, c.as_flattened());
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
    (acc, core::array::from_fn(|k| sponge[k]))
}

/// Public values of the instance: z (bytes), then per slot S_j (bytes) and D_j.
pub fn public_values<F: Field>(z: &BigUint, s: &[BigUint], d: &[[F; DIGEST]]) -> Vec<F> {
    assert_eq!(s.len(), d.len());
    let mut v: Vec<F> = le32(z).iter().map(|&b| F::from_u32(b as u32)).collect();
    for (sj, dj) in s.iter().zip(d) {
        v.extend(le32(sj).iter().map(|&b| F::from_u32(b as u32)));
        v.extend(dj.iter().copied());
    }
    v
}

/// Byte-pair counts of a trace (for `BytePairTableAir`), indexed by a + 256 b.
pub fn pair_counts<F: Field + p3_field::PrimeField32>(t: &RowMajorMatrix<F>) -> Vec<u64> {
    let mut m = vec![0u64; 1 << 16];
    for row in t.values.chunks(WIDTH) {
        for pair in row[..BYTE_COLS].chunks(2) {
            m[(pair[0].as_canonical_u32() + 256 * pair[1].as_canonical_u32()) as usize] += 1;
        }
    }
    m
}

/// The table of all byte pairs (a, b) (preprocessed, 2^16 rows) with the multiplicity of each
/// in the trace: the receiving side of the "byte2" bus.
#[derive(Clone, Debug, Default)]
pub struct BytePairTableAir;

pub const PAIR_LOG_ROWS: usize = 16;

impl BytePairTableAir {
    pub fn from_counts<F: Field>(m: &[u64]) -> RowMajorMatrix<F> {
        assert_eq!(m.len(), 1 << PAIR_LOG_ROWS);
        RowMajorMatrix::new(m.iter().map(|&x| F::from_u64(x)).collect(), 1)
    }
}

impl<F: Field> BaseAir<F> for BytePairTableAir {
    fn width(&self) -> usize {
        1
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(RowMajorMatrix::new((0..1u32 << PAIR_LOG_ROWS).flat_map(|i| [F::from_u32(i & 255), F::from_u32(i >> 8)]).collect(), 2))
    }
    fn preprocessed_width(&self) -> usize {
        2
    }
}

impl<AB> Air<AB> for BytePairTableAir
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let m: AB::Expr = builder.main().current_slice()[0].into();
        let pre = builder.preprocessed();
        let (a, b): (AB::Expr, AB::Expr) = (pre.current(0).unwrap().into(), pre.current(1).unwrap().into());
        builder.push_interaction("byte2", [a, b], p3_lookup::Count::provided(-m));
    }
}

/// The blob side of a batch proof, for the prover: the blobs' elements (at most `slots`) and
/// the point z (derived from their digests and versioned hashes by the caller).
#[derive(Clone, Debug)]
pub struct BlobInput {
    pub slots: usize,
    pub blobs: Vec<Vec<BigUint>>,
    pub z: BigUint,
}

/// The blob side of a batch proof, for the verifier: z, and per slot S_j and D_j (canonical).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlobClaim {
    pub z: BigUint,
    pub s: Vec<BigUint>,
    pub d: Vec<[u32; DIGEST]>,
}

impl BlobInput {
    /// The claim an honest proof of these blobs makes (computed natively).
    pub fn claim(&self) -> BlobClaim {
        assert!(self.slots.is_power_of_two() && self.blobs.len() <= self.slots);
        let zero = vec![BigUint::from(0u32); ROWS];
        let get = |j: usize| self.blobs.get(j).unwrap_or(&zero);
        BlobClaim {
            z: self.z.clone(),
            s: (0..self.slots).map(|j| barycentric_sum(get(j), &self.z)).collect(),
            d: (0..self.slots).map(|j| digests_u32(get(j))).collect(),
        }
    }
}

/// `digest` as canonical u32 values.
pub fn digests_u32(e: &[BigUint]) -> [u32; DIGEST] {
    digest::<p3_baby_bear::BabyBear>(e).map(|x| x.as_canonical_u32())
}

impl BlobClaim {
    pub fn slots(&self) -> usize {
        self.s.len()
    }
    pub fn public_values<F: Field>(&self) -> Vec<F> {
        let d: Vec<[F; DIGEST]> = self.d.iter().map(|d| d.map(F::from_u32)).collect();
        public_values(&self.z, &self.s, &d)
    }
}

/// The blob AIR with `slots` blobs (a power of two).
#[derive(Clone, Debug)]
pub struct BlobEvalAir {
    pub slots: usize,
    /// every element also goes on the "elem" bus to `tx_bind::TxAir` (audit H-01 (b))
    pub bind: bool,
}

impl BlobEvalAir {
    /// The blob AIR alone (the claim about S and D only).
    pub fn new(slots: usize) -> Self {
        assert!(slots.is_power_of_two(), "blob slots must be a power of two");
        Self { slots, bind: false }
    }
    /// The blob AIR whose elements are bound to the executed transactions.
    pub fn bound(slots: usize) -> Self {
        Self { bind: true, ..Self::new(slots) }
    }
    /// log2 of the trace height.
    pub fn log_rows(&self) -> usize {
        LOG_ROWS + self.slots.trailing_zeros() as usize
    }
    fn pre_width(&self) -> usize {
        PRE_LAST + self.slots + 1
    }
    /// the global element index (blob j, element i) -> 4096 j + i
    fn pre_g(&self) -> usize {
        PRE_LAST + self.slots
    }
}

impl<F: Field> BaseAir<F> for BlobEvalAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let w = roots_brp();
        let pw = self.pre_width();
        let mut v = F::zero_vec(self.slots * ROWS * pw);
        for j in 0..self.slots {
            for i in 0..ROWS {
                let row = &mut v[(j * ROWS + i) * pw..(j * ROWS + i + 1) * pw];
                for (k, b) in le32(&w[i]).iter().enumerate() {
                    row[PRE_W + k] = F::from_u32(*b as u32);
                }
                row[PRE_FIRST] = F::from_bool(i == 0);
                row[PRE_LAST + j] = F::from_bool(i == ROWS - 1);
                row[PRE_LAST + self.slots] = F::from_usize(j * ROWS + i);
            }
        }
        Some(RowMajorMatrix::new(v, pw))
    }
    fn preprocessed_width(&self) -> usize {
        self.pre_width()
    }
    fn num_public_values(&self) -> usize {
        B + self.slots * PER_SLOT
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

/// u d + q2 P - e w - q1 P = 0 over the integers, column by column with the carries `c`.
#[allow(clippy::too_many_arguments)]
fn product<AB: AirBuilder>(builder: &mut AB, u: &[AB::Expr], d: &[AB::Expr], e: &[AB::Expr], w: &[AB::Expr], q1: &[AB::Expr], q2: &[AB::Expr], c: &[AB::Expr], p: &[u8; B]) {
    let k256 = AB::Expr::from_u32(256);
    let carry = |k: usize| c[2 * k].clone() + c[2 * k + 1].clone() * k256.clone() - AB::Expr::from_u32(CARRY_OFFSET as u32);
    for k in 0..2 * B - 1 {
        let mut e_k = AB::Expr::ZERO;
        let mut qp = AB::Expr::ZERO;
        for i in k.saturating_sub(B - 1)..=k.min(B - 1) {
            e_k += u[i].clone() * d[k - i].clone() - e[i].clone() * w[k - i].clone();
            qp += (q2[i].clone() - q1[i].clone()) * AB::Expr::from_u32(p[k - i] as u32);
        }
        let mut e = e_k + qp;
        if k > 0 {
            e += carry(k - 1);
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
        let pc: Vec<AB::Expr> = pre.current_slice().iter().map(|&x| x.into()).collect();
        let first_next: AB::Expr = pre.next_slice()[PRE_FIRST].into();
        let w = &pc[PRE_W..PRE_W + B];
        let first = pc[PRE_FIRST].clone();
        let pv: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let z = &pv[..B];
        let slot = |j: usize| &pv[B + j * PER_SLOT..B + (j + 1) * PER_SLOT];
        // within a blob: the next row is not the first of a blob (this also covers the wrap)
        let within = AB::Expr::ONE - first_next;
        let p = modulus_bytes();
        let pk = |k: usize| AB::Expr::from_u32(p[k] as u32);
        let col = |v: &[AB::Expr], at: usize| v[at..at + B].to_vec();

        product(builder, &col(&c, U), &col(&c, D), &col(&c, E), w, &col(&c, Q1), &col(&c, Q2), &c[C..C + 2 * PROD_CARRIES], p);
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
            builder.when(first.clone()).assert_eq(c[ACC + k].clone(), c[U + k].clone());
            for j in 0..self.slots {
                builder.when(pc[PRE_LAST + j].clone()).assert_eq(c[ACC + k].clone(), slot(j)[k].clone());
            }
        }
        let ka = n[KA0].clone() + n[KA1].clone() * AB::Expr::from_u32(2);
        let cols: Vec<AB::Expr> = (0..B).map(|k| c[ACC + k].clone() + n[U + k].clone() - n[ACC + k].clone() - ka.clone() * pk(k)).collect();
        {
            let mut t = builder.when(within.clone());
            sum_zero(&mut t, &cols, &n[AA..AA + B - 1]);
        }
        // the commitment
        let input = absorb(&c[E..E + B], &c[CAP..CAP + CAPACITY]);
        let out = poseidon2_24::eval(builder, input, &c[P2..P2 + poseidon2_24::COLS]);
        for k in 0..CAPACITY {
            builder.when(first.clone()).assert_eq(c[CAP + k].clone(), AB::Expr::from_u32(if k == 0 { TAG } else { 0 }));
            builder.when(within.clone()).assert_eq(n[CAP + k].clone(), out[RATE + k].clone());
        }
        for j in 0..self.slots {
            for k in 0..DIGEST {
                builder.when(pc[PRE_LAST + j].clone()).assert_eq(out[k].clone(), slot(j)[B + k].clone());
            }
        }
        for j in (0..BYTE_COLS).step_by(2) {
            builder.push_interaction("byte2", [c[j].clone(), c[j + 1].clone()], 1);
        }
        if self.bind {
            // (g, the element's 31 data bytes in blob order: big-endian, e_30 first)
            let mut t = vec![pc[self.pre_g()].clone()];
            t.extend((0..B - 1).rev().map(|k| c[E + k].clone()));
            builder.push_interaction("elem", t, 1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{config, BabyBear, Config};
    use p3_air::{Air, BaseAir};
    use p3_batch_stark::{prove_batch, verify_batch, ProverData, StarkInstance};
    use p3_lookup::InteractionBuilder;

    #[derive(Clone, Debug)]
    enum Airs {
        Blob(BlobEvalAir),
        Table(BytePairTableAir),
    }
    impl<F: Field> BaseAir<F> for Airs {
        fn width(&self) -> usize {
            match self {
                Self::Blob(a) => <BlobEvalAir as BaseAir<F>>::width(a),
                Self::Table(a) => <BytePairTableAir as BaseAir<F>>::width(a),
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
                Self::Table(a) => <BytePairTableAir as BaseAir<F>>::preprocessed_width(a),
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

    fn z0() -> BigUint {
        BigUint::parse_bytes(b"5ab1e0f00dcafe0123456789abcdef0123456789abcdef0123456789abcdef", 16).unwrap() % modulus()
    }

    /// What the verifier is given, relative to the honest values.
    #[derive(Default)]
    struct Claim {
        z: Option<BigUint>,
        /// (slot, S)
        s: Option<(usize, BigUint)>,
        /// (slot, digest element bumped)
        d: Option<(usize, usize)>,
    }

    /// Proves the trace of `blobs` in `slots` at `z` (after `tamper`) and verifies it against
    /// the claim. A prover panic counts as rejection.
    fn prove_and_verify(blobs: &[Vec<BigUint>], slots: usize, z: &BigUint, claim: Claim, tamper: impl Fn(&mut RowMajorMatrix<BabyBear>)) -> bool {
        let air = BlobEvalAir::new(slots);
        let (mut t, s, d) = trace::<BabyBear>(blobs, slots, z);
        tamper(&mut t);
        let table = BytePairTableAir::from_counts::<BabyBear>(&pair_counts(&t));
        let cfg = config::<BabyBear>(1, 8);
        let airs = vec![Airs::Blob(air.clone()), Airs::Table(BytePairTableAir)];
        let pd = ProverData::<Config<BabyBear>>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &[air.log_rows(), PAIR_LOG_ROWS], &[3, 3], 1).unwrap();
        let pv_prove = vec![public_values::<BabyBear>(z, &s, &d), vec![]];
        let traces = [&t, &table];
        let inst = StarkInstance::new_multiple(&airs, &traces, &pv_prove);
        let Ok(Ok(proof)) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove_batch(&cfg, &inst, &pd))) else {
            return false;
        };
        let (mut sv, mut dv) = (s, d);
        if let Some((j, x)) = claim.s {
            sv[j] = x;
        }
        if let Some((j, k)) = claim.d {
            dv[j][k] += BabyBear::ONE;
        }
        let pv = vec![public_values::<BabyBear>(claim.z.as_ref().unwrap_or(z), &sv, &dv), vec![]];
        verify_batch(&cfg, &airs, &proof, &pv, &pd.common).is_ok()
    }

    #[test]
    fn witness_sum_matches_the_barycentric_formula() {
        let e = blob_elements(3);
        let z = BigUint::from(0x1234_5678_9abc_def0u64) * BigUint::from(0xfedc_ba98u64);
        let (_, s, d) = trace::<BabyBear>(std::slice::from_ref(&e), 2, &z);
        assert_eq!(s[0], barycentric_sum(&e, &z));
        assert_eq!(s[1], BigUint::from(0u32), "an empty slot sums to 0");
        assert_eq!(d[0], digest::<BabyBear>(&e));
        let mut e2 = e.clone();
        e2[4095] += 1u32;
        assert_ne!(d[0], digest::<BabyBear>(&e2), "the digest covers the last element");
        // p(z) from S against a direct Lagrange evaluation (independent formula)
        let p = modulus();
        let w = roots_brp();
        let y = value_from_sum(&s[0], &z);
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
        let e = vec![blob_elements(7)];
        let z = z0();
        let ok = |claim: Claim| prove_and_verify(&e, 1, &z, claim, |_| {});
        assert!(ok(Claim::default()), "honest");
        let wrong = (barycentric_sum(&e[0], &z) + 1u32) % modulus();
        assert!(!ok(Claim { s: Some((0, wrong)), ..Default::default() }), "a sum the trace does not have");
        assert!(!ok(Claim { z: Some((&z + 1u32) % modulus()), ..Default::default() }), "another z");
        assert!(!ok(Claim { d: Some((0, 3)), ..Default::default() }), "another digest");
        let bad = |tamper: &dyn Fn(&mut RowMajorMatrix<BabyBear>)| prove_and_verify(&e, 1, &z, Claim::default(), tamper);
        // element 5 changed after the witness was made
        assert!(!bad(&|t| t.values[5 * WIDTH + E + 3] += BabyBear::ONE), "element changed");
        // a running sum that skips row 100's term
        assert!(!bad(&|t| t.values[100 * WIDTH + U] += BabyBear::ONE), "term changed");
        // row 9 taken from the trace of other elements (its sum and permutation consistent
        // with themselves, not with the rows around it)
        let mut e2 = e[0].clone();
        e2[9] += 1u32;
        let (t2, _, _) = trace::<BabyBear>(&[e2], 1, &z);
        assert!(!bad(&|t| t.values[9 * WIDTH..10 * WIDTH].copy_from_slice(&t2.values[9 * WIDTH..10 * WIDTH])), "element swapped in");
    }

    #[test]
    fn several_blobs_in_one_instance() {
        let blobs = vec![blob_elements(11), blob_elements(12), blob_elements(13)];
        let z = z0();
        let ok = |claim: Claim| prove_and_verify(&blobs, 4, &z, claim, |_| {});
        assert!(ok(Claim::default()), "honest, 3 blobs in 4 slots");
        // every blob's own sum and digest
        let (_, s, d) = trace::<BabyBear>(&blobs, 4, &z);
        for j in 0..3 {
            assert_eq!(s[j], barycentric_sum(&blobs[j], &z));
            assert_eq!(d[j], digest::<BabyBear>(&blobs[j]));
        }
        assert_eq!(s[3], BigUint::from(0u32));
        // the sums of two blobs swapped
        assert!(!ok(Claim { s: Some((1, s[2].clone())), ..Default::default() }), "blob 2's sum claimed for blob 1");
        assert!(!ok(Claim { s: Some((3, BigUint::from(1u32))), ..Default::default() }), "the empty slot");
        assert!(!ok(Claim { d: Some((2, 0)), ..Default::default() }), "blob 2's digest");
    }
}
