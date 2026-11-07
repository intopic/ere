//! cargo run --release -p ss_rap_settlement --example export_p3_fixture [n_tx log_rows log_blowup queries query_pow]
//!
//! P4b: one small batch settled with the Plonky3 settlement circuit (`wrapper::p3settle`): the
//! 5-lane Plonky3 batch-STARK (Poseidon2-BN254) is verified inside the Groth16 circuit. Writes
//!   contracts/P3WrapperVerifier.sol  -- verifier generated from that circuit's (dev) key
//!   test/P3SettlementFixture.sol     -- header, public input and Groth16 proof
//! Deterministic: CI re-runs it and fails if the files are out of date. Small shape and few FRI
//! queries so it runs in CI; NOT the production parameters. `P3_COUNT_ONLY=1` stops after
//! counting constraints on one thread (any shape); `P3_SYNTH_ONLY=1` stops after the shape's
//! matrices, the batch's witness and the satisfiability check.

use ark_bn254::{Bn254, Fr};
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_snark::SNARK;
use ss_rap_p3::state::Params;
use ss_rap_settlement::groth16::{self, fr_hex, g1_hex, g2_calldata};
use ss_rap_settlement::public_input::Domain;
use ss_rap_settlement::wrapper::par::Merged;
use ss_rap_settlement::wrapper::p3settle::{self, P3SettleCircuit, P3SettleShape};
use std::path::Path;
use std::time::Instant;

use ss_rap_settlement::public_input::checksum;

fn hex(b: &[u8; 32]) -> String {
    format!("0x{}", b.iter().map(|x| format!("{x:02x}")).collect::<String>())
}

fn main() {
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (n_tx, log_rows, log_blowup, queries, query_pow) = (*a.first().unwrap_or(&40), *a.get(1).unwrap_or(&5), *a.get(2).unwrap_or(&1), *a.get(3).unwrap_or(&4), *a.get(4).unwrap_or(&8));
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    // log_rows 0: the smallest trace that holds the batch
    let log_rows = if log_rows == 0 { ss_rap_v2::state::params(n_tx, 2, 50).log_rows as usize } else { log_rows };
    let (st, traces) = ss_rap_p3::state::tests_case(n_tx as u32, log_rows as u32);
    let p = Params { log_rows, log_blowup, queries, budget: 3, query_pow };

    // the batch's blob: its transfers, one per slot (made-up signatures: audit C-02 is open)
    let blob = p3settle::tests_blob_bytes(&st).remove(0);
    let (blobs, blobs_hash) = p3settle::blob_input(std::slice::from_ref(&blob), 1).unwrap();

    let t0 = Instant::now();
    let (proof, ops, claim) = p3settle::prove(&st, &traces, &blobs, &p);
    let t_stark = t0.elapsed();
    let shape = P3SettleShape::new(&st, &p, &proof, &ops);
    let w = p3settle::witness(&shape, &proof, &ops);
    let h = p3settle::header(&st, &w, &claim, blobs_hash, 1, &Domain::DEV);
    let kzg = ss_rap_settlement::blob_eval::point_evaluation_input(&blob, &h.blob_point).unwrap()[96..].to_vec();

    let print_head = || {
        println!("SS-RAP v2 P4b Plonky3 settlement circuit: {n_tx} transfers, 5 lanes x 2^{log_rows} rows, blowup {} x {queries} queries + {query_pow} bits grinding", 1 << log_blowup);
        println!("  Plonky3 prove (Poseidon2-BN254) : {:.0} ms", t_stark.as_secs_f64() * 1e3);
    };
    if std::env::var("P3_COUNT_ONLY").is_ok() {
        // one thread, without storing the matrices (any shape)
        let cs = ConstraintSystem::<Fr>::new_ref();
        cs.set_mode(ark_relations::r1cs::SynthesisMode::Prove { construct_matrices: false });
        let t0 = Instant::now();
        P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&w), blobs: Some(&claim), header: Some(&h) }.generate_constraints(cs.clone()).unwrap();
        print_head();
        println!("  constraints                     : {} (satisfied: not checked)", cs.num_constraints());
        println!("  witness generation (1 thread)   : {:.1} s", t0.elapsed().as_secs_f64());
        return;
    }
    if std::env::var("P3_INLINE").is_ok() {
        // one thread, with the matrices Groth16 needs (the comparison point for the parallel path)
        let cs = ConstraintSystem::<Fr>::new_ref();
        cs.set_optimization_goal(ark_relations::r1cs::OptimizationGoal::Constraints);
        let t0 = Instant::now();
        P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&w), blobs: Some(&claim), header: Some(&h) }.generate_constraints(cs.clone()).unwrap();
        let t_gen = t0.elapsed();
        cs.finalize();
        let mx = cs.to_matrices().unwrap();
        print_head();
        println!("  constraints                     : {}", mx.num_constraints);
        println!("  witness generation (1 thread)   : {:.1} s ({:.1} s synthesis + {:.1} s matrices)", t0.elapsed().as_secs_f64(), t_gen.as_secs_f64(), (t0.elapsed() - t_gen).as_secs_f64());
        return;
    }
    // once per shape: the matrices (and, below, the Groth16 keys)
    let t0 = Instant::now();
    let (keys, mx) = if std::env::var("P3_SYNTH_ONLY").is_ok() {
        (None, p3settle::synthesize_parallel(&shape, None, None, None, None, true).unwrap().matrices)
    } else {
        let (k, mx) = groth16::p3_dev_setup_with_matrices(&shape);
        (Some(k), mx)
    };
    let t_setup = t0.elapsed();
    // per batch: only the witness, on several threads (statement, instances at zeta, FRI query
    // groups), in the column order of those matrices
    let t0 = Instant::now();
    let z = p3settle::witness_parallel(&shape, &st, &w, &claim, &h).unwrap();
    let t_synth = t0.elapsed();
    let m = Merged { matrices: mx, assignment: z };
    let t0 = Instant::now();
    let ok = m.is_satisfied();
    let t_check = t0.elapsed();
    print_head();
    println!("  constraints                     : {} (satisfied: {ok})", m.matrices.num_constraints);
    println!("  matrices (once per shape)       : {:.1} s{}", t_setup.as_secs_f64(), if keys.is_some() { " incl. Groth16 setup (dev)" } else { "" });
    println!("  witness generation (per batch)  : {:.1} s ({} threads; satisfiability check {:.1} s)", t_synth.as_secs_f64(), rayon::current_num_threads(), t_check.as_secs_f64());
    assert!(ok, "first unsatisfied constraint: {:?}", m.first_unsatisfied());
    let Some((pk, vk)) = keys else { return };

    let t0 = Instant::now();
    // seeded proof randomness: reproducible fixture (production uses an OS-seeded CSPRNG)
    let mut rng: rand_chacha::ChaCha20Rng = rand_chacha::rand_core::SeedableRng::seed_from_u64(1);
    let g = groth16::p3_prove_with(&pk, &m.matrices, &m.assignment, &mut rng);
    let t_prove = t0.elapsed();
    let x = h.public_input();
    let t0 = Instant::now();
    assert!(Groth16::<Bn254>::verify(&vk, &[x], &g).unwrap(), "Groth16 proof must verify");
    let t_verify = t0.elapsed();
    assert!(!Groth16::<Bn254>::verify(&vk, &[x + Fr::from(1u64)], &g).unwrap(), "other public input must fail");

    std::fs::write(
        root.join("contracts/P3WrapperVerifier.sol"),
        groth16::solidity_verifier_named(
            &vk,
            "P3WrapperVerifier",
            "// GENERATED by `cargo run -p ss_rap_settlement --example export_p3_fixture`. DO NOT EDIT.\n\
             // Verifying key of the Plonky3 settlement circuit (5-lane Plonky3 batch-STARK verified inside the\n\
             // SNARK) for ONE small batch shape, from `groth16::p3_dev_setup`: PUBLIC SEED, NOT SECURE. Development\n\
             // and CI only.",
        ),
    )
    .unwrap();
    let (a, b, c) = (g1_hex(&g.a), g2_calldata(&g.b), g1_hex(&g.c));
    let fixture = format!(
        r#"// SPDX-License-Identifier: MIT
// GENERATED by `cargo run -p ss_rap_settlement --example export_p3_fixture`. DO NOT EDIT.
// Batch {batch} of {n_tx} transfers. The Groth16 proof comes from the Plonky3 settlement circuit, which
// verifies the 5-lane Plonky3 batch-STARK inside the SNARK (small shape, {queries} FRI queries: CI only).
pragma solidity ^0.8.26;

library P3SettlementFixture {{
    bytes32 internal constant OLD_ROOT = {old};
    bytes32 internal constant NEW_ROOT = {new};
    bytes32 internal constant VUMT_ROOT = {vumt};
    bytes32 internal constant BLOB_HASH = {blob};
    uint256 internal constant BATCH = {batch};
    uint256 internal constant CHAIN_ID = {chain};
    address internal constant SETTLEMENT = {settlement};
    uint256 internal constant PUBLIC_INPUT = {x};
{blob_eval}
    function a() internal pure returns (uint256[2] memory p) {{
        p = [uint256({a0}), uint256({a1})];
    }}

    function b() internal pure returns (uint256[2][2] memory p) {{
        p = [[uint256({b00}), uint256({b01})], [uint256({b10}), uint256({b11})]];
    }}

    function c() internal pure returns (uint256[2] memory p) {{
        p = [uint256({c0}), uint256({c1})];
    }}
}}
"#,
        batch = h.batch_number,
        chain = h.chain_id,
        settlement = checksum(&h.settlement),
        old = hex(&h.old_state_root),
        new = hex(&h.new_state_root),
        vumt = hex(&h.v_umt_root),
        blob = hex(&h.blob_versioned_hash),
        x = fr_hex(&x),
        blob_eval = ss_rap_settlement::blob_eval::solidity_fixture(&h, &kzg),
        a0 = a[0], a1 = a[1],
        b00 = b[0][0], b01 = b[0][1], b10 = b[1][0], b11 = b[1][1],
        c0 = c[0], c1 = c[1],
    );
    std::fs::write(root.join("test/P3SettlementFixture.sol"), fixture).unwrap();
    println!("  Groth16 prove (Plonky3 inside)  : {:.1} s, verify {:.1} ms", t_prove.as_secs_f64(), t_verify.as_secs_f64() * 1e3);
    println!("wrote contracts/P3WrapperVerifier.sol and test/P3SettlementFixture.sol");
}
