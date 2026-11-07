//! R8.4c: real Groth16 over the settlement circuit (the state STARK verified inside), small shape.
//! cargo run --release --example settle_groth16 [queries] [log_blowup] [txs]
use ark_bn254::Bn254;
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_snark::SNARK;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;
use ss_rap_settlement::public_input::BatchHeader;
use ss_rap_settlement::wrapper::settle_circuit::{v_umt_root, SettleCircuit, SettleShape, LABEL};
use ss_rap_settlement::wrapper::statement_var::StatementShape;
use ss_rap_v2::hash::HashMode;
use ss_rap_v2::stark::StarkParams;
use ss_rap_v2::state::{self, AccountState, Transfer};
use ss_rap_v2::transcript::Transcript;
use std::time::Instant;

fn main() {
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (queries, log_blowup, ntx) = (*a.first().unwrap_or(&1), *a.get(1).unwrap_or(&2) as u32, *a.get(2).unwrap_or(&10));
    let accounts = 6usize;
    let log_rows = (ntx.max(2) as f64).log2().ceil() as u32 + 4;
    let params = StarkParams { log_rows: log_rows.max(8), log_blowup, num_queries: queries };
    let addrs: Vec<[u8; 20]> = (0..accounts).map(|i| [i as u8 * 9 + 2; 20]).collect();
    let old: Vec<AccountState> = (0..accounts).map(|i| AccountState { balance: 1_000_000 + i as u64, nonce: 0 }).collect();
    let mut nonces = vec![0u32; accounts];
    let txs: Vec<Transfer> = (0..ntx as u32)
        .map(|k| {
            let from = k % accounts as u32;
            let tx = Transfer { from, to: (from + 1 + k % 3) % accounts as u32, amount: 7 + k as u64, nonce: nonces[from as usize] };
            nonces[from as usize] += 1;
            tx
        })
        .collect();
    let (st, traces) = state::build(&addrs, &old, &txs, params.log_rows, true).unwrap();
    let t0 = Instant::now();
    let proof = state::prove(&st, &traces, &params, &mut Transcript::with_mode(LABEL, HashMode::Poseidon));
    println!("STARK prove (Poseidon-BN254): {:.2?}", t0.elapsed());
    let shape = SettleShape { statement: StatementShape::of(&st, params.log_rows), params };
    let h = BatchHeader { old_state_root: st.old_root(), new_state_root: st.new_root(), v_umt_root: v_umt_root(&st, &proof), blob_versioned_hash: [1; 32], batch_number: 1, chain_id: 31337, settlement: ss_rap_settlement::public_input::FORGE_SETTLEMENT };
    let circ = SettleCircuit { shape, st: Some(&st), proof: Some(&proof), header: Some(&h) };

    let cs = ConstraintSystem::new_ref();
    circ.clone().generate_constraints(cs.clone()).unwrap();
    println!("constraints: {}  satisfied: {}", cs.num_constraints(), cs.is_satisfied().unwrap());

    let mut rng = ChaCha20Rng::from_seed([7; 32]);
    let t0 = Instant::now();
    let (pk, vk) = Groth16::<Bn254>::circuit_specific_setup(SettleCircuit { shape, st: None, proof: None, header: None }, &mut rng).unwrap();
    println!("setup: {:.2?}", t0.elapsed());
    let t0 = Instant::now();
    let g = Groth16::<Bn254>::prove(&pk, circ, &mut rng).unwrap();
    println!("Groth16 prove: {:.2?}", t0.elapsed());
    let x = h.public_input();
    println!("verify honest: {}", Groth16::<Bn254>::verify(&vk, &[x], &g).unwrap());
    println!("verify other x: {}", Groth16::<Bn254>::verify(&vk, &[x + ark_bn254::Fr::from(1u64)], &g).unwrap());
}
