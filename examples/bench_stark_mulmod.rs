//! cargo run --release --example bench_stark_mulmod [log_rows]
//!
//! End-to-end STARK (Phase A, CPU, single machine) for a batch of EVM uint256 MULMOD operations
//! on secp256k1: trace -> LogUp -> quotient -> unified FRI over 5 RNS channels -> verify.
//! 50 FRI queries with blowup 4 (~100 bits, conjectured FRI soundness).

use num_bigint::BigUint;
use ss_rap_v2::stark::{self, StarkParams};
use ss_rap_v2::transcript::Transcript;
use ss_rap_v2::uint256::{Modulus256, MulModRow};
use std::time::Instant;

fn main() {
    let log_rows: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(10);
    let params = StarkParams { log_rows, log_blowup: 2, num_queries: 50 };
    let p = Modulus256::secp256k1();
    let mut s = 1u64;
    let mut next = || {
        let w: Vec<u32> = (0..8)
            .map(|_| {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                (s >> 32) as u32
            })
            .collect();
        BigUint::new(w) % &p.value
    };
    let n = 1usize << log_rows;
    let rows: Vec<MulModRow> = (0..n).map(|_| MulModRow::generate(&next(), &next(), &p)).collect();

    let t0 = Instant::now();
    let proof = stark::prove(&rows, &p, &params, &mut Transcript::new(b"bench"));
    let t_prove = t0.elapsed().as_secs_f64();
    let t0 = Instant::now();
    let ok = stark::verify(&proof, &p, &params, &mut Transcript::new(b"bench"));
    let t_verify = t0.elapsed().as_secs_f64();
    assert!(ok, "proof must verify");

    println!("STARK uint256 MULMOD (secp256k1), {n} operations, 5 RNS channels, blowup 4, 50 queries");
    println!("  prove        : {:>9.1} ms  ({:.1} us per MULMOD)", t_prove * 1e3, t_prove * 1e6 / n as f64);
    println!("  verify       : {:>9.2} ms", t_verify * 1e3);
    println!("  proof size   : {:>9.1} KiB", proof.size_bytes() as f64 / 1024.0);
    println!("  (CPU, one machine. GPU and channel-per-GPU are Phase B.)");
}
