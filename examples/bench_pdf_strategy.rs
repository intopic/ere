//! cargo run --release --example bench_pdf_strategy [n]
//!
//! Measures the strategy described in the SS-RAP v2.0 PDF ("mos llogarit, verifiko"):
//! the expensive operations AROUND a big multiplication are replaced by cheaper ones.
//! Each section isolates one replacement and compares it to the naive path, single-threaded.
//!
//!  S1  Verify instead of compute:  check a*b == q*p + r (witness given)  vs  compute r = a*b % p
//!  S2  Carry-free constraints:     5 independent RNS channel identities  vs  16-bit limbs + carry chain
//!  S3  Barrett instead of `%`:     fast_reduce_channel                    vs  u64 % m (div)
//!  S4  Montgomery batch inversion: 1 inverse + 3(N-1) mul                 vs  N extended-Euclid inverses
//!  S5  V-UMT:                      1 Merkle tree over 5 channels          vs  5 separate trees
//!  S6  Full unified FRI (Phase A): prove + verify time and proof size for 5 channels at once
//!
//! Numbers are wall-clock on whatever machine runs this (CI runners are noisy); ratios matter,
//! absolute values do not. Nothing here measures a full prover or a GPU.

use blake3::Hasher;
use ss_rap_v2::*;
use std::hint::black_box;
use std::time::Instant;

fn lcg(s: &mut u64) -> u64 {
    *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *s
}

fn time<F: FnMut() -> u64>(mut f: F) -> (f64, u64) {
    let t = Instant::now();
    let acc = f();
    (t.elapsed().as_secs_f64(), acc)
}

fn ratio(slow: f64, fast: f64) -> String {
    format!("{:.2}x", slow / fast)
}

// ---------------------------------------------------------------------------------------------
// S2 helpers: classic 16-bit-limb carry-chain check of a*b = q*p + r over BabyBear (64-bit operands)
// ---------------------------------------------------------------------------------------------
const BB: u64 = BABY_BEAR as u64;

struct ClassicRow {
    a: [u64; 4],
    b: [u64; 4],
    q: [u64; 4],
    r: [u64; 4],
    carries: [i64; 8],
}

fn limbs16(x: u64) -> [u64; 4] {
    [x & 0xffff, (x >> 16) & 0xffff, (x >> 32) & 0xffff, x >> 48]
}

fn classic_row(a: u64, b: u64) -> ClassicRow {
    let p = GOLDILOCKS_P;
    let (a, b) = (a % p, b % p);
    let prod = (a as u128) * (b as u128);
    let q = (prod / p as u128) as u64;
    let r = (prod % p as u128) as u64;
    let (al, bl, ql, rl, pl) = (limbs16(a), limbs16(b), limbs16(q), limbs16(r), limbs16(p));
    // column k: sum a_i b_j - sum q_i p_j - r_k + c_{k-1} = c_k * 2^16
    let mut carries = [0i64; 8];
    let mut c: i128 = 0;
    for k in 0..8 {
        let mut s: i128 = c;
        for i in 0..4 {
            if k >= i && k - i < 4 {
                s += (al[i] * bl[k - i]) as i128 - (ql[i] * pl[k - i]) as i128;
            }
        }
        if k < 4 {
            s -= rl[k] as i128;
        }
        c = s >> 16;
        carries[k] = c as i64;
    }
    ClassicRow { a: al, b: bl, q: ql, r: rl, carries }
}

fn to_bb(x: i64) -> u64 {
    (x.rem_euclid(BB as i64)) as u64
}

/// Evaluates the 8 carry constraints in BabyBear. They form a sequential chain: constraint k
/// uses c_{k-1}, so a prover/verifier cannot settle column k before column k-1.
fn classic_eval(row: &ClassicRow, p: &[u64; 4]) -> u64 {
    let mut acc = 0u64;
    for k in 0..8 {
        let mut s: u64 = 0;
        for i in 0..4 {
            if k >= i && k - i < 4 {
                s = (s + row.a[i] * row.b[k - i] % BB) % BB;
                s = (s + BB - row.q[i] * p[k - i] % BB) % BB;
            }
        }
        if k < 4 {
            s = (s + BB - row.r[k]) % BB;
        }
        if k > 0 {
            s = (s + to_bb(row.carries[k - 1])) % BB;
        }
        s = (s + BB - to_bb(row.carries[k]) * 65536 % BB) % BB;
        acc |= s;
    }
    acc
}

// ---------------------------------------------------------------------------------------------
// S5 helper: plain binary Blake3 Merkle tree, single-threaded, returns (root, hash calls)
// ---------------------------------------------------------------------------------------------
fn merkle(leaves: Vec<[u8; 32]>) -> ([u8; 32], u64) {
    let mut layer = leaves;
    let mut hashes = 0u64;
    while layer.len() > 1 {
        layer = layer
            .chunks(2)
            .map(|c| {
                hashes += 1;
                let mut h = Hasher::new();
                h.update(&c[0]);
                h.update(&c[1]);
                *h.finalize().as_bytes()
            })
            .collect();
    }
    (layer[0], hashes)
}

fn main() {
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(1 << 16);
    assert!(n.is_power_of_two(), "n must be a power of two");
    let mut seed = 0x5eed_u64;
    println!("SS-RAP v2 PDF strategy benchmark, n = {n}, single-threaded\n");

    // ------------------------------------------------------------------------------- S1
    let p = GOLDILOCKS_P;
    let pairs: Vec<(u64, u64)> = (0..n).map(|_| (lcg(&mut seed) % p, lcg(&mut seed) % p)).collect();
    let witnesses: Vec<(u64, u64)> = pairs
        .iter()
        .map(|&(a, b)| {
            let prod = a as u128 * b as u128;
            ((prod / p as u128) as u64, (prod % p as u128) as u64)
        })
        .collect();
    let reps = 20;
    let (t_compute, c1) = time(|| {
        let mut acc = 0u64;
        for _ in 0..reps {
            for &(a, b) in black_box(&pairs) {
                acc ^= ((a as u128 * b as u128) % p as u128) as u64;
            }
        }
        acc
    });
    let (t_verify, c2) = time(|| {
        let mut ok = 0u64;
        for _ in 0..reps {
            for (&(a, b), &(q, r)) in black_box(&pairs).iter().zip(black_box(&witnesses)) {
                ok += (a as u128 * b as u128 == q as u128 * p as u128 + r as u128) as u64;
            }
        }
        ok
    });
    black_box((c1, c2));
    assert_eq!(c2, (n * reps) as u64);
    println!("S1  Verify instead of compute (64-bit mod Goldilocks, native CPU)");
    println!("    compute r = a*b % p (128-bit division) : {:>8.2} ns/op", t_compute * 1e9 / (n * reps) as f64);
    println!("    verify a*b == q*p + r (no division)    : {:>8.2} ns/op", t_verify * 1e9 / (n * reps) as f64);
    println!("    speed-up                               : {}\n", ratio(t_compute, t_verify));

    // ------------------------------------------------------------------------------- S2
    let rns_rows: Vec<CarryFreeMulWitnessRow> =
        pairs.iter().map(|&(a, b)| CarryFreeMulWitnessRow::generate(a, b)).collect();
    let classic_rows: Vec<ClassicRow> = pairs.iter().map(|&(a, b)| classic_row(a, b)).collect();
    let pl = limbs16(p);
    assert!(classic_rows.iter().all(|r| classic_eval(r, &pl) == 0), "classic rows must satisfy");
    let (t_classic, _) = time(|| classic_rows.iter().map(|r| classic_eval(black_box(r), &pl)).fold(0, |a, x| a | x));
    let (t_rns_all, _) = time(|| {
        let mut acc = 0u64;
        for r in &rns_rows {
            for ch in 0..DEFAULT_RNS_CHANNELS {
                acc |= black_box(r).evaluate_air_constraints(ch).iter().fold(0u64, |a, &x| a | x as u64);
            }
        }
        acc
    });
    let (t_rns_one, _) = time(|| {
        let mut acc = 0u64;
        for r in &rns_rows {
            acc |= black_box(r).evaluate_air_constraints(0).iter().fold(0u64, |a, &x| a | x as u64);
        }
        acc
    });
    println!("S2  Carry-free RNS constraints vs 16-bit-limb carry chain (a*b = q*p + r, 64-bit)");
    println!("    structure                              classic          RNS (PDF)");
    println!("    sequential dependency depth            8 (carry chain)  1 per channel, 5 independent");
    println!("    carry columns                          8                0");
    println!("    constraints                            8 (chained)      5 x 5 (independent)");
    println!("    CPU time, all constraints              {:>7.1} ns/row   {:>7.1} ns/row",
        t_classic * 1e9 / n as f64, t_rns_all * 1e9 / n as f64);
    println!("    CPU time, one RNS channel (1 worker)                    {:>7.1} ns/row",
        t_rns_one * 1e9 / n as f64);
    println!("    latency with 5 parallel channels vs classic : {}",
        ratio(t_classic, t_rns_one));
    println!("    total work RNS vs classic                   : {:.2}x of classic\n",
        t_rns_all / t_classic);

    // ------------------------------------------------------------------------------- S3
    let vals: Vec<u64> = (0..n).map(|_| lcg(&mut seed) >> 2).collect(); // < 2^62 (product range)
    let reps = 20;
    let (t_div, a1) = time(|| {
        let mut acc = 0u64;
        for _ in 0..reps {
            for ch in 0..DEFAULT_RNS_CHANNELS {
                let m = black_box(RNS_MODULI[ch] as u64);
                for &v in black_box(&vals) {
                    acc = acc.wrapping_add(v % m);
                }
            }
        }
        acc
    });
    let (t_bar, a2) = time(|| {
        let mut acc = 0u64;
        for _ in 0..reps {
            for ch in 0..DEFAULT_RNS_CHANNELS {
                for &v in black_box(&vals) {
                    acc = acc.wrapping_add(fast_reduce_channel(v, black_box(ch)) as u64);
                }
            }
        }
        acc
    });
    assert_eq!(a1, a2, "Barrett must equal %");
    let ops = (n * reps * DEFAULT_RNS_CHANNELS) as f64;
    println!("S3  Barrett reduction vs `%` (64-bit -> 31-bit, 5 channels)");
    println!("    u64 % m (hardware division)            : {:>8.2} ns/op", t_div * 1e9 / ops);
    println!("    Barrett (mul + shift, no division)     : {:>8.2} ns/op", t_bar * 1e9 / ops);
    println!("    speed-up                               : {}\n", ratio(t_div, t_bar));

    // ------------------------------------------------------------------------------- S4
    let ch = 0;
    let m = RNS_MODULI[ch];
    let xs: Vec<u32> = (0..n).map(|_| (lcg(&mut seed) % (m as u64 - 1)) as u32 + 1).collect();
    let (t_naive, _) = time(|| xs.iter().map(|&x| mod_inv_single(black_box(x), m) as u64).sum());
    let (t_batch, _) = time(|| batch_inverse_channel(black_box(&xs), ch).iter().map(|&x| x as u64).sum());
    let batch = batch_inverse_channel(&xs, ch);
    assert!(xs.iter().zip(&batch).all(|(&x, &y)| mul_mod_channel(x, y, ch) == 1));
    println!("S4  Montgomery batch inversion vs N single inverses (N = {n})");
    println!("    N x extended Euclid                    : {:>8.2} ns/elem", t_naive * 1e9 / n as f64);
    println!("    batch: 1 inverse + 3(N-1) Barrett muls : {:>8.2} ns/elem", t_batch * 1e9 / n as f64);
    println!("    speed-up                               : {}\n", ratio(t_naive, t_batch));

    // ------------------------------------------------------------------------------- S5
    let evals: [Vec<Extension4>; DEFAULT_RNS_CHANNELS] = std::array::from_fn(|c| {
        (0..n)
            .map(|_| {
                let m = RNS_MODULI[c] as u64;
                Extension4::new(
                    (lcg(&mut seed) % m) as u32,
                    (lcg(&mut seed) % m) as u32,
                    (lcg(&mut seed) % m) as u32,
                    (lcg(&mut seed) % m) as u32,
                )
            })
            .collect()
    });
    let (t_sep, h_sep) = time(|| {
        let mut hashes = 0;
        for c in 0..DEFAULT_RNS_CHANNELS {
            let leaves: Vec<[u8; 32]> = evals[c].iter().map(|e| *blake3::hash(&e.to_bytes()).as_bytes()).collect();
            hashes += n as u64;
            let (root, h) = merkle(leaves);
            black_box(root);
            hashes += h;
        }
        hashes
    });
    let (t_umt, h_umt) = time(|| {
        let leaves: Vec<[u8; 32]> = (0..n)
            .map(|i| {
                let mut h = Hasher::new();
                for c in 0..DEFAULT_RNS_CHANNELS {
                    h.update(&evals[c][i].to_bytes());
                }
                *h.finalize().as_bytes()
            })
            .collect();
        let (root, h) = merkle(leaves);
        black_box(root);
        n as u64 + h
    });
    let log_n = n.trailing_zeros() as u64;
    println!("S5  V-UMT (1 tree, 80-byte leaves) vs 5 separate Merkle trees (N = {n})");
    println!("    hash calls                             : {h_sep} vs {h_umt}  ({:.2}x fewer)", h_sep as f64 / h_umt as f64);
    println!("    roots to commit / auth paths per query : 5 vs 1  ({} vs {} sibling hashes)", 5 * log_n, log_n);
    println!("    time 5 trees / V-UMT                   : {:.2} ms / {:.2} ms  ({})",
        t_sep * 1e3, t_umt * 1e3, ratio(t_sep, t_umt));

    // ------------------------------------------------------------------------------- S6
    use ss_rap_v2::fri::{self, FriParams};
    use ss_rap_v2::transcript::Transcript;
    let params = FriParams { log_degree: n.trailing_zeros() - 2, log_blowup: 2, num_queries: 40 };
    let coeffs: [Vec<u32>; DEFAULT_RNS_CHANNELS] = std::array::from_fn(|c| {
        (0..1usize << params.log_degree).map(|_| (lcg(&mut seed) % RNS_MODULI[c] as u64) as u32).collect()
    });
    let t0 = Instant::now();
    let proof = fri::prove(&coeffs, &params, &mut Transcript::new(b"bench"));
    let t_prove = t0.elapsed().as_secs_f64();
    let t0 = Instant::now();
    let ok = fri::verify(&proof, &params, &mut Transcript::new(b"bench"));
    let t_verify = t0.elapsed().as_secs_f64();
    assert!(ok);
    println!("S6  Unified FRI, 5 channels together (degree < 2^{}, blowup 4, 40 queries, ~{} bits conjectured)",
        params.log_degree, params.conjectured_security_bits());
    println!("    prove (LDE + {} folds + V-UMT per layer) : {:.2} ms", params.log_degree, t_prove * 1e3);
    println!("    verify                                 : {:.3} ms", t_verify * 1e3);
    println!("    proof size                             : {:.1} KiB", proof.size_bytes() as f64 / 1024.0);
    println!("\nAll correctness asserts passed.");
}
