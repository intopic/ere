//! End-to-end settlement pipeline for one sealed batch:
//!
//! ```text
//! SealedBatch -> MULMOD workload -> STARK prove + native verify (5 RNS channels)
//!             -> v_umt_root (binds the STARK commitments) + blob hash
//!             -> BatchHeader -> public input (keccak mod r, same as the contract)
//!             -> Groth16 proof -> calldata for verifyAndSettleBatchV2
//! ```
//!
//! MVP scope, stated plainly:
//! - The STARK proves the batch's uint256 MULMOD workload (one secp256k1-field multiplication
//!   per transaction, derived from the tx hash and amount). Proving the full state transition
//!   needs the EVM/state AIR, which is the next step after this MVP.
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
use num_bigint::BigUint;
use ss_rap_v2::stark::{self, StarkParams, StarkProof};
use ss_rap_v2::transcript::Transcript;
use ss_rap_v2::uint256::{Modulus256, MulModRow};
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

/// One MULMOD per transaction over the secp256k1 field (the arithmetic of signature checks).
pub fn mulmod_workload(batch: &SealedBatch, p: &Modulus256) -> Vec<MulModRow> {
    batch
        .txs
        .iter()
        .map(|tx| {
            let a = BigUint::from_bytes_be(&tx.hash()) % &p.value;
            let b = BigUint::from(tx.amount) % &p.value;
            MulModRow::generate(&a, &b, p)
        })
        .collect()
}

pub fn blob_versioned_hash(blob: &[u8]) -> [u8; 32] {
    let mut h = *blake3::hash(blob).as_bytes();
    h[0] = 0x01;
    h
}

/// Binds every STARK commitment (trace, aux, quotient, all FRI layers) into one root.
pub fn v_umt_root(p: &StarkProof) -> [u8; 32] {
    let mut v = Vec::new();
    v.extend_from_slice(&p.main_root);
    v.extend_from_slice(&p.aux_root);
    v.extend_from_slice(&p.q_root);
    for r in &p.fri.layer_roots {
        v.extend_from_slice(r);
    }
    keccak256(&v)
}

fn stark_params(rows: usize, cfg: &PipelineConfig) -> StarkParams {
    let log_rows = stark::lane_rows(rows).max(256).next_power_of_two().trailing_zeros();
    StarkParams { log_rows, log_blowup: cfg.log_blowup, num_queries: cfg.num_queries }
}

#[derive(Debug)]
pub enum PipelineError {
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
    let p = Modulus256::secp256k1();
    let rows = mulmod_workload(batch, &p);
    let params = stark_params(rows.len(), cfg);
    let label = format!("SS-RAP/v2/batch/{}/{}", cfg.chain_id, batch.batch_number);
    let mut timings = Timings::default();

    let t0 = Instant::now();
    let stark_proof = stark::prove(&rows, &p, &params, &mut Transcript::new(label.as_bytes()));
    timings.stark_prove = t0.elapsed();
    let t0 = Instant::now();
    let ok = stark::verify(&stark_proof, &p, &params, &mut Transcript::new(label.as_bytes()));
    timings.stark_verify = t0.elapsed();
    if !ok {
        return Err(PipelineError::StarkRejected);
    }

    let header = BatchHeader {
        old_state_root: batch.old_state_root,
        new_state_root: batch.new_state_root,
        v_umt_root: v_umt_root(&stark_proof),
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
        let genesis: Vec<([u8; 20], u128)> = (0..8u8).map(|i| ([i; 20], 1_000_000)).collect();
        let mut seq = Sequencer::new(&genesis, 64, FeeSchedule::default());
        for k in 0..40u64 {
            let from = (k % 8) as u8;
            let tx = Tx { from: [from; 20], to: [(from + 1) % 8; 20], amount: 10 + k as u128, nonce: k / 8, kind: if k % 2 == 0 { TxKind::Transfer } else { TxKind::Swap } };
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
}
