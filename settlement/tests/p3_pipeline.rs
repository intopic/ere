//! The pipeline through the Plonky3 settlement circuit. Its own test binary: the dev setup of
//! the circuit takes ~8 GB, so it must not run next to the library's other heavy tests (cargo
//! runs test binaries one after another).

use ss_rap_settlement::fees::{CostModel, FeeSchedule, TxKind};
use ss_rap_settlement::groth16;
use ss_rap_settlement::pipeline::{settle_with, P3Params, P3Prover, PipelineConfig, PipelineError, Profile, Wrapper};
use ss_rap_settlement::sequencer::{address_of, dev_key, Sequencer, Tx};

fn addr(i: u64) -> [u8; 20] {
    address_of(dev_key(i).verifying_key())
}

/// Audit finding: the pipeline settled through the first STARK, not the Plonky3 circuit.
#[test]
fn small_batch_through_the_plonky3_circuit() {
    let genesis: Vec<([u8; 20], u64)> = (0..8u64).map(|i| (addr(i), 1_000_000)).collect();
    let mut seq = Sequencer::new(&genesis, 64, FeeSchedule::default());
    for k in 0..10u64 {
        let from = k % 8;
        seq.submit(Tx::signed(&dev_key(from), addr((from + 3) % 8), 10 + k, (k / 8) as u32, TxKind::Transfer, &seq.domain)).unwrap();
    }
    let batch = seq.seal();
    let p = P3Params { log_rows: 4, log_blowup: 1, queries: 1, budget: 3, query_pow: 4 };
    // a production prover refuses these CI parameters (5 conjectured bits)
    assert!(matches!(P3Prover::new(&batch, p, 1, Profile::Production), Err(PipelineError::InsecureParams { bits: 5 })));
    let prover = P3Prover::new(&batch, p, 1, Profile::Development).unwrap();
    let (pk, vk) = prover.dev_keys();
    let mut rng: rand_chacha::ChaCha20Rng = rand_chacha::rand_core::SeedableRng::seed_from_u64(1);
    let cfg = PipelineConfig::default();
    let pkg = settle_with(&batch, &pk, &vk, Wrapper::P3(&prover), &cfg, &FeeSchedule::default(), &CostModel::default(), &mut rng).unwrap();
    assert_eq!(pkg.header.new_state_root, batch.new_state_root);
    assert!(groth16::verify(&vk, pkg.public_input, &pkg.proof));
    // a proof of this batch does not settle a header with another root
    let mut other = pkg.header.clone();
    other.new_state_root[0] ^= 1;
    assert!(!groth16::verify(&vk, other.public_input(), &pkg.proof));
    // nor the same batch on another settlement contract (audit SET-06)
    let mut other = pkg.header.clone();
    other.settlement[19] ^= 1;
    assert!(!groth16::verify(&vk, other.public_input(), &pkg.proof));
    // a batch of another shape is refused, not proven against the wrong key
    let mut seq2 = Sequencer::new(&genesis, 64, FeeSchedule::default());
    seq2.submit(Tx::signed(&dev_key(0), addr(1), 1, 0, TxKind::Transfer, &seq2.domain)).unwrap();
    seq2.submit(Tx::signed(&dev_key(1), addr(9), 1, 0, TxKind::Transfer, &seq2.domain)).unwrap();
    let b2 = seq2.seal();
    let r = settle_with(&b2, &pk, &vk, Wrapper::P3(&prover), &cfg, &FeeSchedule::default(), &CostModel::default(), &mut rng);
    assert!(matches!(r, Err(PipelineError::ShapeMismatch)), "got {:?}", r.err());
}
