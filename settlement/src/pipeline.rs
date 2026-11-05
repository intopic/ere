//! End-to-end settlement pipeline for one sealed batch:
//!
//! ```text
//! SealedBatch -> state AIR witness (old table, transfers) -> STARK prove + native verify
//!             (5 RNS lanes; proves old_state_root -> new_state_root)
//!             -> v_umt_root (binds the statement and the STARK commitments) + blob hash
//!             -> BatchHeader -> public input (keccak mod r, same as the contract)
//!             -> Groth16 proof -> calldata for verifyAndSettleBatchV2
//! ```
//!
//! MVP scope, stated plainly:
//! - The STARK proves the state transition of the batch (`ss_rap_v2::state`): balances, nonces,
//!   no overspending, every blob transaction executed once and in order, and that the old and
//!   new state roots in the header are the roots of the proven tables. Signatures are checked
//!   by the sequencer; proving them in-circuit (secp256k1, using the MULMOD AIR) comes later.
//! - The Groth16 circuit is the DEV wrapper (see groth16.rs): it binds the public input; the
//!   STARK is verified natively here before anything is sent to L1.
//! - The blob versioned hash is 0x01 || blake3(blob)[1..]. On a real network it is
//!   0x01 || sha256(KZG commitment)[1..], computed by the node when the blob tx is built.

use crate::fees::{batch_economics, BatchEconomics, CostModel, FeeSchedule};
use crate::groth16;
use crate::public_input::{keccak256, BatchHeader};
use crate::sequencer::SealedBatch;
use ark_bn254::{Bn254, Fr};
use ark_groth16::{Proof, ProvingKey, VerifyingKey};
use ss_rap_v2::stark::StarkProof;
use ss_rap_v2::state::{self, StateError, StateStatement};
use ss_rap_v2::transcript::Transcript;
use std::time::{Duration, Instant};

#[derive(Clone, Copy, Debug)]
pub struct PipelineConfig {
    pub chain_id: u64,
    pub num_queries: usize,
    pub log_blowup: u32,
}

impl Default for PipelineConfig {
    fn default() -> Self {
        Self { chain_id: 31337, num_queries: 50, log_blowup: 2 }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Timings {
    pub stark_prove: Duration,
    pub stark_verify: Duration,
    pub groth16_prove: Duration,
    pub groth16_verify: Duration,
}

pub struct SettlementPackage {
    pub header: BatchHeader,
    pub public_input: Fr,
    pub proof: Proof<Bn254>,
    pub stark_proof_bytes: usize,
    pub stark_rows: usize,
    pub timings: Timings,
    pub economics: BatchEconomics,
}

pub fn blob_versioned_hash(blob: &[u8]) -> [u8; 32] {
    let mut h = *blake3::hash(blob).as_bytes();
    h[0] = 0x01;
    h
}

/// Binds the public statement and every STARK commitment (trace, aux, quotient, all FRI
/// layers) into one root.
pub fn v_umt_root(st: &StateStatement, p: &StarkProof) -> [u8; 32] {
    let mut v = st.digest().to_vec();
    v.extend_from_slice(&p.main_root);
    v.extend_from_slice(&p.aux_root);
    v.extend_from_slice(&p.q_root);
    for r in &p.fri.layer_roots {
        v.extend_from_slice(r);
    }
    keccak256(&v)
}

#[derive(Debug)]
pub enum PipelineError {
    InvalidBatch(StateError),
    /// The sequencer's roots differ from the roots of the proven tables.
    RootMismatch,
    StarkRejected,
    Groth16Rejected,
}

pub fn settle(
    batch: &SealedBatch,
    pk: &ProvingKey<Bn254>,
    vk: &VerifyingKey<Bn254>,
    cfg: &PipelineConfig,
    schedule: &FeeSchedule,
    cost: &CostModel,
) -> Result<SettlementPackage, PipelineError> {
    let params = state::params(batch.txs.len(), cfg.log_blowup, cfg.num_queries);
    let label = format!("SS-RAP/v2/batch/{}/{}", cfg.chain_id, batch.batch_number);
    let mut timings = Timings::default();

    let t0 = Instant::now();
    let (st, traces) = state::build(&batch.addrs, &batch.old_states, &batch.transfers(), params.log_rows, true).map_err(PipelineError::InvalidBatch)?;
    if st.old_root() != batch.old_state_root || st.new_root() != batch.new_state_root {
        return Err(PipelineError::RootMismatch);
    }
    let stark_proof = state::prove(&st, &traces, &params, &mut Transcript::new(label.as_bytes()));
    timings.stark_prove = t0.elapsed();
    let t0 = Instant::now();
    let ok = state::verify(&st, &batch.old_state_root, &batch.new_state_root, &stark_proof, &params, &mut Transcript::new(label.as_bytes()));
    timings.stark_verify = t0.elapsed();
    if !ok {
        return Err(PipelineError::StarkRejected);
    }

    let header = BatchHeader {
        old_state_root: batch.old_state_root,
        new_state_root: batch.new_state_root,
        v_umt_root: v_umt_root(&st, &stark_proof),
        blob_versioned_hash: blob_versioned_hash(&batch.blob_data()),
        batch_number: batch.batch_number,
        chain_id: cfg.chain_id,
    };
    let x = header.public_input();
    let t0 = Instant::now();
    let proof = groth16::prove(pk, x, batch.batch_number);
    timings.groth16_prove = t0.elapsed();
    let t0 = Instant::now();
    if !groth16::verify(vk, x, &proof) {
        return Err(PipelineError::Groth16Rejected);
    }
    timings.groth16_verify = t0.elapsed();

    let measured = CostModel { prover_seconds: timings.stark_prove.as_secs_f64() + timings.groth16_prove.as_secs_f64(), ..*cost };
    Ok(SettlementPackage {
        header,
        public_input: x,
        proof,
        stark_proof_bytes: stark_proof.size_bytes(),
        stark_rows: 1 << params.log_rows,
        timings,
        economics: batch_economics(&batch.kinds(), schedule, &measured),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fees::TxKind;
    use crate::sequencer::{Sequencer, Tx};

    #[test]
    fn small_batch_end_to_end() {
        let genesis: Vec<([u8; 20], u64)> = (0..8u8).map(|i| ([i; 20], 1_000_000)).collect();
        let mut seq = Sequencer::new(&genesis, 64, FeeSchedule::default());
        for k in 0..40u64 {
            let from = (k % 8) as u8;
            let tx = Tx { from: [from; 20], to: [(from + 1) % 8; 20], amount: 10 + k, nonce: (k / 8) as u32, kind: if k % 2 == 0 { TxKind::Transfer } else { TxKind::Swap } };
            seq.submit(tx).unwrap();
        }
        let batch = seq.seal();
        let (pk, vk) = groth16::dev_setup();
        let cfg = PipelineConfig { num_queries: 8, ..PipelineConfig::default() };
        let pkg = settle(&batch, &pk, &vk, &cfg, &FeeSchedule::default(), &CostModel::default()).unwrap();
        assert_eq!(pkg.header.old_state_root, batch.old_state_root);
        assert_eq!(pkg.public_input, pkg.header.public_input());
        assert!(groth16::verify(&vk, pkg.public_input, &pkg.proof));
        assert_eq!(pkg.economics.txs, 40);
        assert_eq!(pkg.header.blob_versioned_hash[0], 1);
    }

    #[test]
    fn header_roots_must_be_the_proven_roots() {
        let genesis: Vec<([u8; 20], u64)> = (0..4u8).map(|i| ([i; 20], 1_000)).collect();
        let mut seq = Sequencer::new(&genesis, 16, FeeSchedule::default());
        seq.submit(Tx { from: [0; 20], to: [9; 20], amount: 5, nonce: 0, kind: TxKind::Transfer }).unwrap();
        let mut batch = seq.seal();
        batch.new_state_root[0] ^= 1;
        let (pk, vk) = groth16::dev_setup();
        let cfg = PipelineConfig { num_queries: 8, ..PipelineConfig::default() };
        let r = settle(&batch, &pk, &vk, &cfg, &FeeSchedule::default(), &CostModel::default());
        assert!(matches!(r, Err(PipelineError::RootMismatch)));
    }
}
