//! R8.4: the settlement circuit. One public input, the same as the contract's:
//!
//! ```text
//! x = keccak256(oldStateRoot, newStateRoot, vUmtRoot, blobhash, batchNumber, chainId, settlement) mod r
//! ```
//!
//! and the circuit proves that x is the hash of a header whose
//! - old and new state roots are the roots of a well-formed state statement,
//! - v_umt_root binds that statement and every commitment of a STARK proof (Poseidon),
//! - STARK proof verifies for that statement (`stark_var::verify_stark`).
//!
//! The blob hash, batch number, chain id and settlement address are free header fields: the
//! contract supplies them (blobsHash(), its counter, block.chainid, address(this)), so the proof
//! is bound to them through x. Tying the
//! blob's content to the proven transfers (KZG point evaluation) is a later step.

use super::keccak_var::keccak256;
use super::stark_var::{verify_stark, StarkProofVar, StateCircuit};
use super::statement_var::{StatementShape, StatementVar};
use crate::public_input::BatchHeader;
use ark_bn254::Fr;
use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::prelude::ToBitsGadget;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ss_rap_v2::hash::{fr_to_hash, hash_to_fr, poseidon_config, poseidon_hash};
use ss_rap_v2::stark::{StarkParams, StarkProof};
use ss_rap_v2::state::StateStatement;

/// The STARK transcript label of settlement proofs.
pub const LABEL: &[u8] = b"SS-RAP/v2/settle";

/// v_umt_root: Poseidon over the statement digest and every STARK commitment.
pub fn v_umt_root(st: &StateStatement, p: &StarkProof) -> [u8; 32] {
    let mut v = vec![hash_to_fr(&st.digest()), hash_to_fr(&p.main_root), hash_to_fr(&p.aux_root), hash_to_fr(&p.q_root)];
    v.extend(p.fri.layer_roots.iter().map(hash_to_fr));
    fr_to_hash(&poseidon_hash(&v))
}

#[derive(Clone, Copy, Debug)]
pub struct SettleShape {
    pub statement: StatementShape,
    pub params: StarkParams,
}

/// The circuit (values are None during setup).
#[derive(Clone)]
pub struct SettleCircuit<'a> {
    pub shape: SettleShape,
    pub st: Option<&'a StateStatement>,
    pub proof: Option<&'a StarkProof>,
    pub header: Option<&'a BatchHeader>,
}

fn bits_of_bytes(cs: &ConstraintSystemRef<Fr>, bytes: Option<&[u8]>, n: usize) -> Result<Vec<Boolean<Fr>>, SynthesisError> {
    (0..8 * n).map(|i| Boolean::new_witness(cs.clone(), || bytes.map(|b| (b[i / 8] >> (i % 8)) & 1 == 1).ok_or(SynthesisError::AssignmentMissing))).collect()
}

/// A field element as its 32 LE bytes (`fr_to_hash`), as bits.
fn fr_bits(x: &FpVar<Fr>) -> Result<Vec<Boolean<Fr>>, SynthesisError> {
    let mut b = x.to_bits_le()?;
    b.resize(256, Boolean::FALSE);
    Ok(b)
}

/// A u64 as a 32-byte big-endian uint256, as bits (LSB first per byte).
fn u256_be_bits(cs: &ConstraintSystemRef<Fr>, x: Option<u64>) -> Result<Vec<Boolean<Fr>>, SynthesisError> {
    let v: Vec<Boolean<Fr>> = (0..64).map(|i| Boolean::new_witness(cs.clone(), || x.map(|x| (x >> i) & 1 == 1).ok_or(SynthesisError::AssignmentMissing))).collect::<Result<_, _>>()?;
    let mut out = vec![Boolean::FALSE; 24 * 8];
    for j in 0..8 {
        // byte 24 + j holds bits 8 (7 - j) .. 8 (7 - j) + 8
        for t in 0..8 {
            out.push(v[8 * (7 - j) + t].clone());
        }
    }
    Ok(out)
}

/// x = keccak256(oldRoot, newRoot, vUmtRoot, blobhash, batchNumber, chainId, settlement) mod r, with the
/// three roots given as circuit values and the other header fields as free witnesses.
pub fn bind_header(cs: &ConstraintSystemRef<Fr>, x: &FpVar<Fr>, old_root: &FpVar<Fr>, new_root: &FpVar<Fr>, v_umt: &FpVar<Fr>, header: Option<&BatchHeader>) -> Result<(), SynthesisError> {
    let cs = cs.clone();
    let mut msg = Vec::with_capacity(224 * 8);
    msg.extend(fr_bits(old_root)?);
    msg.extend(fr_bits(new_root)?);
    msg.extend(fr_bits(v_umt)?);
    msg.extend(bits_of_bytes(&cs, header.map(|h| h.blob_versioned_hash.as_slice()), 32)?);
    msg.extend(u256_be_bits(&cs, header.map(|h| h.batch_number))?);
    msg.extend(u256_be_bits(&cs, header.map(|h| h.chain_id))?);
    let settlement = header.map(|h| crate::public_input::address_word(&h.settlement));
    msg.extend(bits_of_bytes(&cs, settlement.as_ref().map(|w| w.as_slice()), 32)?);
    let hash = keccak256(&msg)?;
    // big-endian uint256 mod r
    let mut acc = FpVar::zero();
    for byte in hash.chunks(8) {
        let b = Boolean::le_bits_to_fp(byte)?;
        acc = acc * Fr::from(256u64) + b;
    }
    acc.enforce_equal(x)?;
    Ok(())
}

impl ConstraintSynthesizer<Fr> for SettleCircuit<'_> {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x = FpVar::new_input(cs.clone(), || self.header.map(|h| h.public_input()).ok_or(SynthesisError::AssignmentMissing))?;
        let stmt = StatementVar::witness(&cs, self.st, self.shape.statement)?;
        let (old_root, new_root, digest) = (stmt.old_root.clone(), stmt.new_root.clone(), stmt.digest.clone());
        let rows = stmt.num_txs();
        let air = StateCircuit { stmt };
        let pv = StarkProofVar::witness(&cs, &air, self.proof, &self.shape.params)?;
        verify_stark(&cs, &air, &pv, &self.shape.params, rows, LABEL)?;

        let mut s = PoseidonSpongeVar::new(cs.clone(), poseidon_config());
        let mut v = vec![digest, pv.main_root.clone(), pv.aux_root.clone(), pv.q_root.clone()];
        v.extend(pv.fri.roots.iter().cloned());
        s.absorb(&v)?;
        let v_umt = s.squeeze_field_elements(1)?.remove(0);

        bind_header(&cs, &x, &old_root, &new_root, &v_umt, self.header)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use ss_rap_v2::hash::HashMode;
    use ss_rap_v2::state::{self, AccountState, Transfer};
    use ss_rap_v2::transcript::Transcript;

    pub(crate) fn small_case() -> (StateStatement, StarkProof, SettleShape) {
        let params = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 1 };
        let accounts = 6usize;
        let addrs: Vec<[u8; 20]> = (0..accounts).map(|i| [i as u8 * 9 + 2; 20]).collect();
        let old: Vec<AccountState> = (0..accounts).map(|i| AccountState { balance: 5_000 + i as u64, nonce: 0 }).collect();
        let mut nonces = vec![0u32; accounts];
        let txs: Vec<Transfer> = (0..10u32)
            .map(|k| {
                let from = k % accounts as u32;
                let tx = Transfer { from, to: (from + 1 + k % 3) % accounts as u32, amount: 7 + k as u64, nonce: nonces[from as usize] };
                nonces[from as usize] += 1;
                tx
            })
            .collect();
        let (st, traces) = state::build(&addrs, &old, &txs, params.log_rows, true).unwrap();
        let proof = state::prove(&st, &traces, &params, &mut Transcript::with_mode(LABEL, HashMode::Poseidon));
        let shape = SettleShape { statement: StatementShape::of(&st, params.log_rows), params };
        (st, proof, shape)
    }

    pub(crate) fn header(st: &StateStatement, proof: &StarkProof) -> BatchHeader {
        BatchHeader { old_state_root: st.old_root(), new_state_root: st.new_root(), v_umt_root: v_umt_root(st, proof), blob_versioned_hash: [0x01; 32], batch_number: 7, chain_id: 31337, settlement: crate::public_input::FORGE_SETTLEMENT }
    }

    fn sat(c: SettleCircuit) -> (bool, usize) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        c.generate_constraints(cs.clone()).unwrap();
        (cs.is_satisfied().unwrap(), cs.num_constraints())
    }

    #[test]
    fn settlement_circuit_binds_roots_proof_and_header() {
        let _heavy = crate::heavy_test_lock();
        let (st, proof, shape) = small_case();
        let h = header(&st, &proof);
        let (ok, n) = sat(SettleCircuit { shape, st: Some(&st), proof: Some(&proof), header: Some(&h) });
        assert!(ok, "honest batch");
        eprintln!("settlement circuit (small shape): {n} constraints");
        // a header claiming another new root
        let mut bad = h.clone();
        bad.new_state_root[0] ^= 1;
        assert!(!sat(SettleCircuit { shape, st: Some(&st), proof: Some(&proof), header: Some(&bad) }).0, "other new root");
        // another batch number than the one hashed (the contract supplies its own)
        let mut bad = h.clone();
        bad.batch_number += 1;
        let x_other = bad.public_input();
        assert_ne!(x_other, h.public_input());
        // a different v_umt_root
        let mut bad = h.clone();
        bad.v_umt_root[3] ^= 1;
        assert!(!sat(SettleCircuit { shape, st: Some(&st), proof: Some(&proof), header: Some(&bad) }).0, "other v_umt_root");
        // a proof of another statement
        let mut st2 = st.clone();
        st2.states[ss_rap_v2::DEFAULT_RNS_CHANNELS][1].balance += 1;
        let h2 = header(&st2, &proof);
        assert!(!sat(SettleCircuit { shape, st: Some(&st2), proof: Some(&proof), header: Some(&h2) }).0, "statement the proof is not about");
    }
}
