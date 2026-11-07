//! State AIR (1000 transfers by default) on Plonky3 vs the in-house engine (Blake3 and Poseidon-BN254).
//! cargo run --release -p ss_rap_p3 --example bench_p3_state [txs] [log_blowup] [queries]
use ss_rap_p3::state::{keccak, poseidon2_bn254, prove, verify, Params};
use ss_rap_v2::hash::HashMode;
use ss_rap_v2::stark::StarkParams;
use ss_rap_v2::state::{self, build, AccountState, Transfer};
use ss_rap_v2::transcript::Transcript;
use std::time::Instant;

fn main() {
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (n, log_blowup, queries) = (*a.first().unwrap_or(&1000), *a.get(1).unwrap_or(&1), *a.get(2).unwrap_or(&100));
    let k = 100usize;
    let addrs: Vec<[u8; 20]> = (0..k).map(|i| [i as u8; 20]).collect();
    let old: Vec<AccountState> = (0..k).map(|_| AccountState { balance: 1_000_000_000, nonce: 0 }).collect();
    let mut nonces = vec![0u32; k];
    let txs: Vec<Transfer> = (0..n as u32)
        .map(|j| {
            let from = j % k as u32;
            let tx = Transfer { from, to: (j * 7 + 3) % k as u32, amount: 1 + (j as u64 * 7919) % 10_000, nonce: nonces[from as usize] };
            nonces[from as usize] += 1;
            tx
        })
        .collect();
    let sp = state::params(n, 2, 50);
    let (st, traces) = build(&addrs, &old, &txs, sp.log_rows, true).unwrap();
    let p = Params { log_rows: sp.log_rows as usize, log_blowup, queries, budget: 3, query_pow: 0 };
    let t0 = Instant::now();
    let proof = prove(&st, &traces, &p);
    let pt = t0.elapsed();
    let t0 = Instant::now();
    let ok = verify(&st, &st.old_root(), &st.new_root(), &proof, &p);
    println!("{n} transfers, {k} accounts, 2^{} rows/lane", sp.log_rows);
    println!("  plonky3 (keccak), blowup {} x {queries} queries : prove {pt:>8.2?}  verify {:>8.2?}  ok {ok}", 1 << log_blowup, t0.elapsed());
    let t0 = Instant::now();
    let proof = poseidon2_bn254::prove(&st, &traces, &p);
    let pt = t0.elapsed();
    let t0 = Instant::now();
    let ok = poseidon2_bn254::verify(&st, &st.old_root(), &st.new_root(), &proof, &p);
    println!("  plonky3 (poseidon2-bn254), blowup {} x {queries}: prove {pt:>8.2?}  verify {:>8.2?}  ok {ok}", 1 << log_blowup, t0.elapsed());
    // all 5 lanes in ONE proof (what the Groth16 circuit verifies), incl. the circuit-friendly 16 x 25
    for (lb, q) in [(log_blowup, queries), (2, 50), (3, 34), (4, 25)] {
        let p1 = Params { log_blowup: lb, queries: q, ..p };
        let blobs = ss_rap_p3::state::tests_blobs(&st);
        let claim = blobs.claim();
        let t0 = Instant::now();
        let pr = keccak::prove_one(&st, &traces, &blobs, &p1);
        let pt = t0.elapsed();
        let ok = keccak::verify_one(&st, &st.old_root(), &st.new_root(), &pr, &claim, &p1);
        println!("  plonky3 ONE proof (keccak), blowup {} x {q}: prove {pt:>8.2?}  ok {ok}", 1 << lb);
        let t0 = Instant::now();
        let pr = poseidon2_bn254::prove_one(&st, &traces, &blobs, &p1);
        let pt = t0.elapsed();
        let t0 = Instant::now();
        let ok = poseidon2_bn254::verify_one(&st, &st.old_root(), &st.new_root(), &pr, &claim, &p1);
        println!("  plonky3 ONE proof (poseidon2-bn254), blowup {} x {q}: prove {pt:>8.2?}  verify {:>8.2?}  ok {ok}", 1 << lb, t0.elapsed());
    }
    for (name, mode) in [("ours, blake3", HashMode::Blake3), ("ours, poseidon-bn254", HashMode::Poseidon)] {
        let params = StarkParams { log_rows: sp.log_rows, log_blowup: 2, num_queries: 50 };
        let t0 = Instant::now();
        let pr = state::prove(&st, &traces, &params, &mut Transcript::with_mode(b"b", mode));
        let pt = t0.elapsed();
        let t0 = Instant::now();
        let ok = state::verify(&st, &st.old_root(), &st.new_root(), &pr, &params, &mut Transcript::with_mode(b"b", mode));
        println!("  {name:22}, blowup 4 x 50 queries : prove {pt:>8.2?}  verify {:>8.2?}  ok {ok}", t0.elapsed());
    }
}
