//! SS-RAP v2, Phase C: settlement on Ethereum L1 and the payment model.
//!
//! - `public_input`: the exact public input the L1 contract computes (keccak, mod r).
//! - `groth16`: Groth16 over BN254 (arkworks): setup, prove, verify, Solidity verifier codegen.
//! - `sequencer`: accepts transactions, gives soft confirmations, seals batches.
//! - `fees`: the PDF's "mid-price" fee schedule and real per-batch cost accounting.
//! - `pipeline`: transactions -> batch -> STARK -> public input -> Groth16 -> L1 calldata.

pub mod fees;
pub mod groth16;
pub mod pipeline;
pub mod public_input;
pub mod sequencer;
pub mod wrapper;

/// Tests that build a Plonky3 settlement circuit take several GB each: they hold this lock so
/// that `cargo test` never runs two of them at once (CI runners have 16 GB).
#[cfg(test)]
pub(crate) fn heavy_test_lock() -> std::sync::MutexGuard<'static, ()> {
    static HEAVY: std::sync::Mutex<()> = std::sync::Mutex::new(());
    HEAVY.lock().unwrap_or_else(|e| e.into_inner())
}
