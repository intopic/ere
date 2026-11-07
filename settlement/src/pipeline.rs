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
//! - Three Groth16 circuits: the DEV wrapper (groth16.rs) only binds the public input, and the
//!   STARK is verified natively here; `Wrapper::Stark` (wrapper/settle_circuit.rs) verifies the
//!   first state STARK inside the SNARK; `Wrapper::P3` (wrapper/p3settle.rs) verifies the
//!   5-lane Plonky3 batch-STARK inside the SNARK, the production path. Each key is for one
//!   fixed batch shape.
//! - The blob versioned hash is the real EIP-4844 one: 0x01 || sha256(KZG commitment)[1..] of
//!   the batch's blob (`blob.rs`), the value `blobhash(0)` returns to the contract.

use crate::fees::{batch_economics, BatchEconomics, CostModel, FeeSchedule};
use crate::groth16;
use crate::public_input::BatchHeader;
use crate::wrapper::settle_circuit::{SettleCircuit, SettleShape, LABEL};
use crate::wrapper::p3settle::{self, P3SettleShape};
use crate::wrapper::statement_var::StatementShape;
use ark_relations::r1cs::ConstraintMatrices;
pub use ss_rap_p3::state::Params as P3Params;
use ark_groth16::Groth16;
use ark_snark::SNARK;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;
use ss_rap_v2::hash::HashMode;
use crate::sequencer::SealedBatch;
use ark_bn254::{Bn254, Fr};
use ark_groth16::{Proof, ProvingKey, VerifyingKey};
use ss_rap_v2::state::{self, StateError};
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

/// The blob hash of `data` (the batch's `blob_data`): the versioned hash of its blob, or, when it
/// takes several blobs, keccak256 of their versioned hashes (`crate::blob::blobs_hash`).
pub fn blob_versioned_hash(data: &[u8]) -> Result<[u8; 32], PipelineError> {
    let blobs = crate::blob::to_blobs(data).ok_or(PipelineError::BlobTooLarge)?;
    let hashes: Vec<[u8; 32]> = blobs.iter().map(|b| crate::blob::versioned_hash(b)).collect();
    Ok(crate::blob::blobs_hash(&hashes))
}

/// Binds the public statement and every STARK commitment (trace, aux, quotient, all FRI
/// layers) into one root (Poseidon, so the settlement circuit recomputes it cheaply).
pub use crate::wrapper::settle_circuit::v_umt_root;

/// The Plonky3 settlement circuit of one batch shape, ready to prove: the shape and its R1CS
/// matrices are built once; per batch only the witness is computed (on several threads).
pub struct P3Prover {
    pub shape: P3SettleShape,
    pub matrices: ConstraintMatrices<Fr>,
    degree_bits: Vec<usize>,
}

impl P3Prover {
    /// The shape of `batch` proven with `params`, and the matrices of its circuit.
    pub fn new(batch: &SealedBatch, params: P3Params) -> Result<(Self, (ProvingKey<Bn254>, VerifyingKey<Bn254>)), PipelineError> {
        let (st, traces) = state::build(&batch.addrs, &batch.old_states, &batch.transfers(), params.log_rows as u32, true).map_err(PipelineError::InvalidBatch)?;
        let (proof, ops) = p3settle::prove(&st, &traces, &params);
        let shape = P3SettleShape::new(&st, &params, &proof, &ops);
        // DEV key (public seed). A real deployment loads the key of a setup ceremony instead.
        let (keys, matrices) = groth16::p3_dev_setup_with_matrices(&shape);
        Ok((Self { shape, matrices, degree_bits: proof.degree_bits.clone() }, keys))
    }
}

/// Which Groth16 circuit wraps the batch.
#[derive(Clone, Copy)]
pub enum Wrapper<'a> {
    /// DEV circuit: binds the public input only; the STARK is verified natively here.
    Dev,
    /// The settlement circuit: verifies the state STARK inside the SNARK. The proving key is for
    /// this one shape (accounts, transfers per lane, STARK parameters).
    Stark(SettleShape),
    /// The Plonky3 settlement circuit (production path).
    P3(&'a P3Prover),
}

#[derive(Debug)]
pub enum PipelineError {
    InvalidBatch(StateError),
    /// The sequencer's roots differ from the roots of the proven tables.
    RootMismatch,
    StarkRejected,
    Groth16Rejected,
    /// The batch does not have the shape the settlement circuit's key was made for.
    ShapeMismatch,
    /// The batch's transactions do not fit in one blob.
    BlobTooLarge,
}

pub fn settle(
    batch: &SealedBatch,
    pk: &ProvingKey<Bn254>,
    vk: &VerifyingKey<Bn254>,
    cfg: &PipelineConfig,
    schedule: &FeeSchedule,
    cost: &CostModel,
) -> Result<SettlementPackage, PipelineError> {
    settle_with(batch, pk, vk, Wrapper::Dev, cfg, schedule, cost)
}

/// The statement shape and STARK parameters of a batch (what a settlement circuit key fixes).
pub fn batch_shape(batch: &SealedBatch, cfg: &PipelineConfig) -> Result<SettleShape, PipelineError> {
    let params = state::params(batch.txs.len(), cfg.log_blowup, cfg.num_queries);
    let (st, _) = state::build(&batch.addrs, &batch.old_states, &batch.transfers(), params.log_rows, true).map_err(PipelineError::InvalidBatch)?;
    Ok(SettleShape { statement: StatementShape::of(&st, params.log_rows), params })
}

pub fn settle_with(
    batch: &SealedBatch,
    pk: &ProvingKey<Bn254>,
    vk: &VerifyingKey<Bn254>,
    wrapper: Wrapper,
    cfg: &PipelineConfig,
    schedule: &FeeSchedule,
    cost: &CostModel,
) -> Result<SettlementPackage, PipelineError> {
    if let Wrapper::P3(prover) = wrapper {
        return settle_p3(batch, pk, vk, prover, cfg, schedule, cost);
    }
    let params = state::params(batch.txs.len(), cfg.log_blowup, cfg.num_queries);
    // One constant label: chain id and batch number are bound through the public input.
    let transcript = || Transcript::with_mode(LABEL, HashMode::Poseidon);
    let mut timings = Timings::default();

    let t0 = Instant::now();
    let (st, traces) = state::build(&batch.addrs, &batch.old_states, &batch.transfers(), params.log_rows, true).map_err(PipelineError::InvalidBatch)?;
    if st.old_root() != batch.old_state_root || st.new_root() != batch.new_state_root {
        return Err(PipelineError::RootMismatch);
    }
    let stark_proof = state::prove(&st, &traces, &params, &mut transcript());
    timings.stark_prove = t0.elapsed();
    let t0 = Instant::now();
    let ok = state::verify(&st, &batch.old_state_root, &batch.new_state_root, &stark_proof, &params, &mut transcript());
    timings.stark_verify = t0.elapsed();
    if !ok {
        return Err(PipelineError::StarkRejected);
    }

    let header = BatchHeader {
        old_state_root: batch.old_state_root,
        new_state_root: batch.new_state_root,
        v_umt_root: v_umt_root(&st, &stark_proof),
        blob_versioned_hash: blob_versioned_hash(&batch.blob_data())?,
        batch_number: batch.batch_number,
        chain_id: cfg.chain_id,
    };
    let x = header.public_input();
    let t0 = Instant::now();
    let proof = match wrapper {
        Wrapper::Dev => groth16::prove(pk, x, batch.batch_number),
        Wrapper::P3(_) => unreachable!(),
        Wrapper::Stark(shape) => {
            let p = &shape.params;
            if StatementShape::of(&st, params.log_rows) != shape.statement || (p.log_rows, p.log_blowup, p.num_queries) != (params.log_rows, params.log_blowup, params.num_queries) {
                return Err(PipelineError::ShapeMismatch);
            }
            let mut rng = ChaCha20Rng::seed_from_u64(batch.batch_number);
            let c = SettleCircuit { shape, st: Some(&st), proof: Some(&stark_proof), header: Some(&header) };
            Groth16::<Bn254>::prove(pk, c, &mut rng).map_err(|_| PipelineError::Groth16Rejected)?
        }
    };
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

/// The batch through the Plonky3 batch-STARK and the Plonky3 settlement circuit.
fn settle_p3(
    batch: &SealedBatch,
    pk: &ProvingKey<Bn254>,
    vk: &VerifyingKey<Bn254>,
    prover: &P3Prover,
    cfg: &PipelineConfig,
    schedule: &FeeSchedule,
    cost: &CostModel,
) -> Result<SettlementPackage, PipelineError> {
    let p = prover.shape.params;
    let mut timings = Timings::default();
    let t0 = Instant::now();
    let (st, traces) = state::build(&batch.addrs, &batch.old_states, &batch.transfers(), p.log_rows as u32, true).map_err(PipelineError::InvalidBatch)?;
    if st.old_root() != batch.old_state_root || st.new_root() != batch.new_state_root {
        return Err(PipelineError::RootMismatch);
    }
    if StatementShape::of(&st.public_part(), p.log_rows as u32) != prover.shape.statement {
        return Err(PipelineError::ShapeMismatch);
    }
    // proves and verifies natively (panics if the native verifier rejects)
    let (proof, ops) = p3settle::prove(&st, &traces, &p);
    timings.stark_prove = t0.elapsed();
    if proof.degree_bits != prover.degree_bits {
        return Err(PipelineError::ShapeMismatch);
    }
    let w = p3settle::witness(&prover.shape, &proof, &ops);
    let header = BatchHeader {
        old_state_root: batch.old_state_root,
        new_state_root: batch.new_state_root,
        v_umt_root: p3settle::v_umt_root(&st, &w),
        blob_versioned_hash: blob_versioned_hash(&batch.blob_data())?,
        batch_number: batch.batch_number,
        chain_id: cfg.chain_id,
    };
    let x = header.public_input();
    let t0 = Instant::now();
    let z = p3settle::witness_parallel(&prover.shape, &st, &w, &header).map_err(|_| PipelineError::Groth16Rejected)?;
    let proof_g = groth16::p3_prove_with(pk, &prover.matrices, &z, batch.batch_number);
    timings.groth16_prove = t0.elapsed();
    let t0 = Instant::now();
    if !groth16::verify(vk, x, &proof_g) {
        return Err(PipelineError::Groth16Rejected);
    }
    timings.groth16_verify = t0.elapsed();
    let measured = CostModel { prover_seconds: timings.stark_prove.as_secs_f64() + timings.groth16_prove.as_secs_f64(), ..*cost };
    Ok(SettlementPackage {
        header,
        public_input: x,
        proof: proof_g,
        // not measured for the Plonky3 proof (it never leaves the prover: L1 sees only Groth16)
        stark_proof_bytes: 0,
        stark_rows: 5 << p.log_rows,
        timings,
        economics: batch_economics(&batch.kinds(), schedule, &measured),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fees::TxKind;
    use crate::sequencer::{address_of, dev_key, Sequencer, Tx};

    fn addr(i: u64) -> [u8; 20] {
        address_of(dev_key(i).verifying_key())
    }

    #[test]
    fn small_batch_end_to_end() {
        let genesis: Vec<([u8; 20], u64)> = (0..8u64).map(|i| (addr(i), 1_000_000)).collect();
        let mut seq = Sequencer::new(&genesis, 64, FeeSchedule::default());
        for k in 0..40u64 {
            let from = k % 8;
            let kind = if k % 2 == 0 { TxKind::Transfer } else { TxKind::Swap };
            let tx = Tx::signed(&dev_key(from), addr((from + 1) % 8), 10 + k, (k / 8) as u32, kind, seq.chain_id);
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
        let genesis: Vec<([u8; 20], u64)> = (0..4u64).map(|i| (addr(i), 1_000)).collect();
        let mut seq = Sequencer::new(&genesis, 16, FeeSchedule::default());
        seq.submit(Tx::signed(&dev_key(0), addr(9), 5, 0, TxKind::Transfer, seq.chain_id)).unwrap();
        let mut batch = seq.seal();
        batch.new_state_root[0] ^= 1;
        let (pk, vk) = groth16::dev_setup();
        let cfg = PipelineConfig { num_queries: 8, ..PipelineConfig::default() };
        let r = settle(&batch, &pk, &vk, &cfg, &FeeSchedule::default(), &CostModel::default());
        assert!(matches!(r, Err(PipelineError::RootMismatch)));
    }
}
