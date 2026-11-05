//! The real STARK -> Groth16 wrapper (work in progress), built by recursion:
//!
//! ```text
//! state STARK (Blake3, 5 lanes, fast)  ->  recursion STARK proving "that STARK verifies"
//!   (Poseidon, small)  ->  BN254 circuit verifying the small STARK  ->  Groth16 to L1
//! ```
//!
//! A direct circuit for today's proof would need ~8M constraints (`cost`); the recursion
//! step shrinks what the final circuit has to check. This module holds the building blocks:
//! - `fp31`: arithmetic of the five 31-bit RNS fields and their quartic extension inside BN254,
//!   with lazy reduction (products are accumulated in the 254-bit native field and reduced
//!   only when a bound would overflow);
//! - Poseidon (`ss_rap_v2::hash`, `HashMode::Poseidon`): the SNARK-friendly hash the final STARK
//!   uses for Merkle trees and Fiat-Shamir (Blake3 costs ~100x more constraints in R1CS);
//! - `cost`: constraint counts measured on these gadgets and the projection for a full proof.

pub mod cost;
pub mod fp31;
pub mod fri_var;
pub mod keccak_var;
pub mod stark_var;
pub mod settle_circuit;
pub mod statement_var;
pub mod hash_var;

