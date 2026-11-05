//! cargo run --release --example bench_state_bn254 [log_blowup] [queries]
//!
//! The 1000-tx state proof with the BN254-friendly hash (Poseidon over BN254 for the trees and
//! the transcript): the proof the Groth16 circuit verifies directly (R8).

use ss_rap_v2::hash::HashMode;
use ss_rap_v2::state::{self, AccountState, Transfer};
use ss_rap_v2::transcript::Transcript;
use std::time::Instant;

fn main() {
    let arg = |i: usize, d: usize| std::env::args().nth(i).and_then(|s| s.parse().ok()).unwrap_or(d);
    let (log_blowup, queries) = (arg(1, 6) as u32, arg(2, 16));
    let accounts = 200usize;
    let addrs: Vec<[u8; 20]> = (0..accounts).map(|i| { let mut a = [0u8; 20]; a[..8].copy_from_slice(&(i as u64 + 1).to_le_bytes()); a }).collect();
    let old: Vec<AccountState> = (0..accounts).map(|i| AccountState { balance: 10_000_000 + i as u64, nonce: 0 }).collect();
    let mut nonces = vec![0u32; accounts];
    let txs: Vec<Transfer> = (0..1000u32)
        .map(|k| {
            let from = (k * 37 + 11) % accounts as u32;
            let tx = Transfer { from, to: (k * 53 + 7) % accounts as u32, amount: 100 + k as u64, nonce: nonces[from as usize] };
            nonces[from as usize] += 1;
            tx
        })
        .collect();
    let p = state::params(txs.len(), log_blowup, queries);
    let (st, traces) = state::build(&addrs, &old, &txs, p.log_rows, true).unwrap();
    for (mode, name) in [(HashMode::Blake3, "blake3"), (HashMode::Poseidon, "poseidon-bn254")] {
        let t = || Transcript::with_mode(b"bench", mode);
        let t0 = Instant::now();
        let proof = state::prove(&st, &traces, &p, &mut t());
        let dt = t0.elapsed();
        let t0 = Instant::now();
        let ok = state::verify(&st, &st.old_root(), &st.new_root(), &proof, &p, &mut t());
        println!("{name}: blowup {}, {queries} queries: prove {dt:?}, verify {:?} ({ok}), proof {} KiB", 1 << log_blowup, t0.elapsed(), proof.size_bytes() / 1024);
    }
}
