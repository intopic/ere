//! cargo run --release --example bench_poseidon2: permutations per second in every lane.
use ss_rap_v2::poseidon2::{permute_ch, WIDTH};
use std::time::Instant;

fn main() {
    let n = 1_000_000;
    for ch in 0..5 {
        let mut s = [7u32; WIDTH];
        let t = Instant::now();
        for _ in 0..n {
            permute_ch(&mut s, ch);
        }
        println!("lane {ch}: {:.0} ns / permutation ({})", t.elapsed().as_nanos() as f64 / n as f64, s[0]);
    }
}
