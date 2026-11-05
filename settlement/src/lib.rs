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
