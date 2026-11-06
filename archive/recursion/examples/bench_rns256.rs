//! cargo run --release --example bench_rns256 [rows]
//!
//! Fair, single-threaded comparison of the *full* constraint work needed to check one
//! 256-bit modular multiplication r = a*b mod P (secp256k1 field) inside a 31-bit-field prover:
//!
//!  A) RNS-256 (this crate): per channel, 5 limb-tie constraints + product identity + canonical-r
//!     check, over all 17 channels.
//!  B) Classic limb arithmetic: 16-bit limbs, schoolbook convolution of a*b and q*P, signed
//!     carry chain, all evaluated in BabyBear.
//!
//! Byte/16-bit range checks (LogUp) are excluded from both; they are comparable in size.
//! Also printed: honest operation counts for both approaches.

use num_bigint::BigUint;
use num_integer::Integer;
use ss_rap_v2::rns256::*;
use std::time::Instant;

fn lcg(state: &mut u64) -> u64 {
    *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *state
}

fn rand256(state: &mut u64) -> BigUint {
    BigUint::new((0..8).map(|_| (lcg(state) >> 32) as u32).collect())
}

const L16: usize = 16;

fn limbs16(x: &BigUint) -> [u32; L16] {
    let mut out = [0u32; L16];
    for (i, d) in x.iter_u32_digits().enumerate() {
        out[2 * i] = d & 0xffff;
        out[2 * i + 1] = d >> 16;
    }
    out
}

/// Classic witness: 16-bit limbs of a, b, q, r and the signed carry chain c_0..c_31.
struct LimbRow {
    a: [u32; L16],
    b: [u32; L16],
    q: [u32; L16],
    r: [u32; L16],
    carries: [u32; 2 * L16], // field encoding of signed carries
}

fn limb_row(a: &BigUint, b: &BigUint, p: &BigUint, p16: &[u32; L16], m: u32) -> LimbRow {
    let a = a % p;
    let b = b % p;
    let (q, r) = (&a * &b).div_rem(p);
    let (a, b, q, r) = (limbs16(&a), limbs16(&b), limbs16(&q), limbs16(&r));
    let mut carries = [0u32; 2 * L16];
    let mut c: i64 = 0;
    for k in 0..2 * L16 {
        let mut d: i64 = c;
        for i in 0..L16 {
            if k >= i && k - i < L16 {
                d += a[i] as i64 * b[k - i] as i64 - q[i] as i64 * p16[k - i] as i64;
            }
        }
        if k < L16 {
            d -= r[k] as i64;
        }
        assert_eq!(d & 0xffff, 0, "carry chain must be exact");
        c = d >> 16;
        carries[k] = c.rem_euclid(m as i64) as u32;
    }
    assert_eq!(c, 0, "final carry must vanish");
    LimbRow { a, b, q, r, carries }
}

/// Number of violated constraints in a classic limb row (field = channel `ch`).
fn eval_limb_row(row: &LimbRow, p16: &[u32; L16], ch: &Channel) -> usize {
    let two16 = 1u32 << 16;
    let mut bad = 0;
    let mut prev = 0u32;
    for k in 0..2 * L16 {
        let mut d = prev;
        let lo = k.saturating_sub(L16 - 1);
        let hi = k.min(L16 - 1);
        for i in lo..=hi {
            d = ch.add(d, ch.mul(row.a[i], row.b[k - i]));
            d = ch.sub(d, ch.mul(row.q[i], p16[k - i]));
        }
        if k < L16 {
            d = ch.sub(d, row.r[k]);
        }
        d = ch.sub(d, ch.mul(row.carries[k], two16));
        bad += (d != 0) as usize;
        prev = row.carries[k];
    }
    bad
}

fn main() {
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(1 << 14);
    let basis = Rns256Basis::canonical();
    let f = TargetField::from_hex(SECP256K1_P_HEX, &basis);
    let baby_bear = basis.channels[0];
    assert_eq!(baby_bear.m, ss_rap_v2::BABY_BEAR);
    let p16 = limbs16(&f.p);

    println!("RNS basis: {} channels x 31-bit, log2(M) = {:.1} bits", basis.len(), basis.modulus_bits);
    println!("rows: {n} random secp256k1 mulmods, single thread\n");

    let mut st = 0x5eed_u64;
    let inputs: Vec<(BigUint, BigUint)> = (0..n).map(|_| (rand256(&mut st), rand256(&mut st))).collect();

    let rns_rows: Vec<MulModRow> = inputs.iter().map(|(a, b)| MulModRow::generate(a, b, &f, &basis)).collect();
    let limb_rows: Vec<LimbRow> = inputs.iter().map(|(a, b)| limb_row(a, b, &f.p, &p16, baby_bear.m)).collect();

    let time = |name: &str, f: &dyn Fn() -> usize| {
        assert_eq!(f(), 0); // warm-up + correctness
        let reps = 5;
        let t = Instant::now();
        for _ in 0..reps {
            assert_eq!(std::hint::black_box(f()), 0);
        }
        let ns = t.elapsed().as_nanos() as f64 / (reps * n) as f64;
        println!("{name:<46} {ns:>9.1} ns/row");
        ns
    };

    let rns_full = time("A) RNS-256 full constraints (17 channels)", &|| {
        rns_rows
            .iter()
            .map(|r| (0..basis.len()).map(|j| r.constraints(j, &f, &basis).iter().filter(|&&x| x != 0).count()).sum::<usize>())
            .sum()
    });
    let rns_one = time("A1) RNS-256, one channel only (per-GPU share)", &|| {
        rns_rows.iter().map(|r| r.constraints(0, &f, &basis).iter().filter(|&&x| x != 0).count()).sum()
    });
    let limb = time("B) classic 16-bit limbs + carries (BabyBear)", &|| {
        limb_rows.iter().map(|r| eval_limb_row(r, &p16, &baby_bear)).sum()
    });

    let k = basis.len();
    println!("\nField operations per 256-bit mulmod check (mul / mul-by-constant):");
    println!("  A) RNS-256:  {:>4} (5 ties x 32 limbs + 2 products, x {k} channels)", (5 * 32 + 2) * k);
    println!("  B) classic:  {:>4} (2 x 16x16 convolution + 32 carry terms)", 2 * L16 * L16 + 2 * L16);
    println!("\nMeasured: RNS total / classic = {:.2}x   |   one RNS channel / classic = {:.2}x",
        rns_full / limb, rns_one / limb);
}
