//! cargo run --release -p ss_rap_settlement --example stark_circuit_size [queries] [log_blowup] [txs]
//!
//! Builds the BN254 circuit that verifies a real state proof (R8.3) and prints its size and
//! whether the honest witness satisfies it.

use ark_bn254::Fr;
use ark_relations::r1cs::ConstraintSystem;
use ss_rap_settlement::wrapper::stark_var::{verify_stark, StarkProofVar, StateCircuit};
use ss_rap_settlement::wrapper::statement_var::{StatementShape, StatementVar};
use ss_rap_v2::hash::HashMode;
use ss_rap_v2::state::{self, AccountState, Transfer};
use ss_rap_v2::transcript::Transcript;
use std::time::Instant;

fn main() {
    let arg = |i: usize, d: usize| std::env::args().nth(i).and_then(|s| s.parse().ok()).unwrap_or(d);
    let (queries, log_blowup, n_tx) = (arg(1, 16), arg(2, 6) as u32, arg(3, 1000));
    let accounts = 200usize;
    let addrs: Vec<[u8; 20]> = (0..accounts).map(|i| { let mut a = [0u8; 20]; a[..8].copy_from_slice(&(i as u64 + 1).to_be_bytes()); a }).collect();
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
    let p = state::params(n_tx, log_blowup, queries);
    let (st, traces) = state::build(&addrs, &old, &txs, p.log_rows, true).unwrap();
    let t = || Transcript::with_mode(b"settle", HashMode::Poseidon);
    let t0 = Instant::now();
    let proof = state::prove(&st, &traces, &p, &mut t());
    println!("state proof ({n_tx} tx, blowup {}, {queries} queries): {:?}", 1 << log_blowup, t0.elapsed());
    let cs = ConstraintSystem::<Fr>::new_ref();
    let t0 = Instant::now();
    let air = StateCircuit { stmt: StatementVar::witness(&cs, Some(&st), StatementShape::of(&st, p.log_rows)).unwrap() };
    let after_statement = cs.num_constraints();
    let pv = StarkProofVar::witness(&cs, &air, Some(&proof), &p).unwrap();
    let after_witness = cs.num_constraints() - after_statement;
    verify_stark(&cs, &air, &pv, &p, st.num_txs(), b"settle").unwrap();
    println!("circuit: {} constraints (statement {after_statement}, proof witness {after_witness}), built in {:?}", cs.num_constraints(), t0.elapsed());
    println!("satisfied: {}", cs.is_satisfied().unwrap());
}
