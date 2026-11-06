//! SS-RAP on Plonky3 (decision 5.11.2026, docs/BENCHMARK.md B2: the in-house engine was ~33x slower).
//! The AIRs and the PDF method stay the same; only the STARK engine underneath changes.

pub mod bn254;
pub mod config;
pub mod mulmod;
pub mod state;
pub mod record;
