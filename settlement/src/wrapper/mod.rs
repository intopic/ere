//! The real STARK -> Groth16 wrapper (work in progress).
//!
//! Goal: a BN254 R1CS circuit that runs the STARK verifier, so that the Groth16 proof posted to
//! L1 implies that the state-transition STARK verifies. This module holds the building blocks:
//! - `fp31`: arithmetic of the five 31-bit RNS fields and their quartic extension inside BN254,
//!   with lazy reduction (products are accumulated in the 254-bit native field and reduced
//!   only when a bound would overflow);
//! - `poseidon`: the SNARK-friendly hash the wrapped STARK must use for Merkle trees and
//!   Fiat-Shamir (Blake3 costs ~100x more constraints per byte inside R1CS);
//! - `cost`: constraint counts measured on these gadgets and the projection for a full proof.

pub mod cost;
pub mod fp31;
pub mod poseidon;
