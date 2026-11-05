//! cargo run --release --example bench_recursion [num_queries] [log_blowup] [lane]
//!
//! Recursion cost at the real batch size: a state proof of 1000 transfers (per-lane mode, one
//! lane), then the outer STARK that proves "the verifier of that lane accepted" (R7 stack).
//! Prints the rows each verifier table needs, the stack shape and the time of every step.

use ss_rap_v2::hash::HashMode;
use ss_rap_v2::recursion::LaneAlgebra;
use ss_rap_v2::stark::{prove_air, verify_air, Air, StarkParams};
use ss_rap_v2::state::{self, AccountState, StateAir, Transfer};
use ss_rap_v2::transcript::Transcript;
use std::time::Instant;

fn main() {
    let arg = |i: usize, d: usize| std::env::args().nth(i).and_then(|s| s.parse().ok()).unwrap_or(d);
    let (queries, log_blowup, j) = (arg(1, 50), arg(2, 2) as u32, arg(3, 0));
    let n_tx = 1000usize;
    let accounts = 200usize;
    let addrs: Vec<[u8; 20]> = (0..accounts).map(|i| { let mut a = [0u8; 20]; a[..8].copy_from_slice(&(i as u64 + 1).to_le_bytes()); a }).collect();
    let old: Vec<AccountState> = (0..accounts).map(|i| AccountState { balance: 10_000_000 + i as u64, nonce: 0 }).collect();
    let mut nonces = vec![0u32; accounts];
    let txs: Vec<Transfer> = (0..n_tx as u32)
        .map(|k| {
            let from = (k * 37 + 11) % accounts as u32;
            let tx = Transfer { from, to: (k * 53 + 7) % accounts as u32, amount: 100 + k as u64, nonce: nonces[from as usize] };
            nonces[from as usize] += 1;
            tx
        })
        .collect();
    let inner_p = state::params(n_tx, log_blowup, queries);
    let (st, traces) = state::build(&addrs, &old, &txs, inner_p.log_rows, true).unwrap();
    let inner = StateAir { st: &st };
    println!("inner: {n_tx} tx, 2^{} rows per lane, blowup {}, {} queries, lane {j}", inner_p.log_rows, 1 << log_blowup, queries);

    let t0 = Instant::now();
    let proof = prove_air(&inner, &traces, st.num_txs(), &inner_p, &mut Transcript::with_mode(b"inner", HashMode::Lane(j as u8)));
    println!("inner prove (one lane, Poseidon2): {:?}, proof {} KiB", t0.elapsed(), proof.size_bytes() / 1024);

    let t0 = Instant::now();
    let alg = LaneAlgebra::new(&inner, &proof, inner_p, b"inner");
    println!("replay + witness: {:?}", t0.elapsed());

    let log_rows = alg.log_rows();
    let merkle_rows: usize = alg.merkle.claims.iter().map(|c| c.depth as usize).sum();
    let tables: [(&str, usize, usize); 10] = [
        ("composition", alg.opened.len(), alg.composition.width()),
        ("fri fold", alg.pairs.len() * alg.fold.alphas.len(), alg.fold.width()),
        ("leaf hash", alg.leaves.rows_needed(), alg.leaves.width()),
        ("merkle", merkle_rows, alg.merkle.width()),
        ("transcript", alg.transcript.perms, alg.transcript.width()),
        ("pid roots", alg.merkle.claims.len(), alg.pid_roots.width()),
        ("tree roots", alg.tree_roots.trees.len(), alg.tree_roots.width()),
        ("final", 1, alg.final_air.width()),
        ("index", alg.index_words.len(), alg.index.width()),
        ("public sum", alg.public_sum.tuples.len(), alg.public_sum.width()),
    ];
    let (mut cells_used, mut cells_padded) = (0usize, 0usize);
    println!("{:<12} {:>7} {:>6} {:>12}", "table", "rows", "width", "rows*width");
    for (name, rows, width) in tables {
        println!("{:<12} {:>7} {:>6} {:>12}", name, rows, width, rows * width);
        cells_used += rows * width;
        cells_padded += (1usize << log_rows) * width;
    }
    let width = alg.stack().width();
    println!("stack: 2^{log_rows} rows x {width} columns; cells used {cells_used}, padded {cells_padded} ({:.1}x)", cells_padded as f64 / cells_used as f64);

    let p = StarkParams { log_rows, log_blowup: 2, num_queries: 16 };
    let t0 = Instant::now();
    let tr = alg.traces(p.log_rows);
    println!("outer traces: {:?}", t0.elapsed());
    let stack = alg.stack();
    let t0 = Instant::now();
    let outer = prove_air(&stack, &tr, alg.composition.claims.len(), &p, &mut Transcript::with_mode(b"recursion", HashMode::Lane(j as u8)));
    println!("outer prove: {:?}, proof {} KiB", t0.elapsed(), outer.size_bytes() / 1024);
    let t0 = Instant::now();
    assert!(verify_air(&stack, &outer, 1 << p.log_rows, &p, &mut Transcript::with_mode(b"recursion", HashMode::Lane(j as u8))));
    println!("outer verify: {:?}", t0.elapsed());
}
