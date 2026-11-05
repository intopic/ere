//! B2: engine comparison. Proves N Poseidon2-KoalaBear (width 16) permutations, one per row,
//! with this repository's STARK prover. `bench/plonky3` proves the same permutations with
//! Plonky3 (p3-uni-stark + p3-poseidon2-air) on the same machine and FRI parameters.
//! cargo run --release --example bench_vs_plonky3 [log_rows] [log_blowup] [queries]
use ss_rap_v2::hash::HashMode;
use ss_rap_v2::poseidon2::{permute, WIDTH};
use ss_rap_v2::poseidon2_air::{Poseidon2Air, LANE};
use ss_rap_v2::stark::{prove_air, verify_air, StarkParams};
use ss_rap_v2::transcript::Transcript;
use std::time::Instant;

fn main() {
    let a: Vec<u32> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (log_rows, log_blowup, queries) = (*a.first().unwrap_or(&13), *a.get(1).unwrap_or(&1), *a.get(2).unwrap_or(&100) as usize);
    let n = 1usize << log_rows;
    let params = StarkParams { log_rows, log_blowup, num_queries: queries };
    let pairs: Vec<([u32; WIDTH], [u32; WIDTH])> = (0..n as u32)
        .map(|k| {
            let i: [u32; WIDTH] = std::array::from_fn(|j| (k * 31 + j as u32 * 7 + 1) % 0x7f000001);
            let mut o = i;
            permute(&mut o);
            (i, o)
        })
        .collect();
    let air = Poseidon2Air { public: pairs };
    let t0 = Instant::now();
    let traces = air.traces(log_rows);
    let trace_t = t0.elapsed();
    println!("ours: {n} Poseidon2-KoalaBear-16 permutations, blowup {}, {queries} queries, {} threads", 1 << log_blowup, rayon_threads());
    for (name, mode) in [("blake3, 5 lanes (4 idle)", HashMode::Blake3), ("poseidon2, KoalaBear lane only", HashMode::Lane(LANE as u8))] {
        let t0 = Instant::now();
        let proof = prove_air(&air, &traces, n, &params, &mut Transcript::with_mode(b"b2", mode));
        let pt = t0.elapsed();
        let t0 = Instant::now();
        let ok = verify_air(&air, &proof, n, &params, &mut Transcript::with_mode(b"b2", mode));
        println!("  {name:32} trace {:>7.1?}  prove {:>8.2?}  verify {:>7.2?}  ok {ok}  proof {:.0} KiB", trace_t, pt, t0.elapsed(), proof.size_bytes() as f64 / 1024.0);
    }
}

fn rayon_threads() -> usize {
    std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1)
}
