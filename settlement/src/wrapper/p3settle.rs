//! P4b: the settlement circuit over the Plonky3 proof. One public input, the contract's:
//!
//! ```text
//! x = keccak256(oldStateRoot, newStateRoot, vUmtRoot, blobhash, batchNumber, chainId, settlement, z, y..) mod r
//! ```
//!
//! The circuit proves that x is the hash of a header whose
//! - old and new state roots are the roots of a well-formed state statement (`StatementVar`),
//! - v_umt_root = Poseidon(statement digest, main, permutation and quotient commitments, FRI
//!   commit-phase commitments) of a Plonky3 batch proof (`ss_rap_p3::record::prove_one`, all 5
//!   lanes, Poseidon2-BN254 Merkle trees and transcript),
//! - that proof verifies (`p3batch_var::verify_batch_var`) for that statement: the public AIRs'
//!   periodic columns are built from the witnessed statement and the digest is observed as the
//!   lane-0 public values, so every Fiat-Shamir challenge depends on the statement;
//! - the blob point z is the hash of the blob digests the proof outputs and of the header's
//!   blobs hash, and each y_j is the value at z of the polynomial of the elements the proof
//!   holds in blob slot j (`blob_var`, audit H-01).
//!
//! Same contract interface as the R8 circuit (`settle_circuit`): only the verifying key changes.

use super::p3batch_var::{batch_shape, batch_witness, verify_batch_var, BatchShape, BatchWitness, PublicIo};
use super::blob_var::{blob_evals, BlobPublicVar};
use super::settle_circuit::{bind_header, HeaderBlobBits};
use ss_rap_p3::blob_eval::{BlobClaim, BlobInput};
use super::par::{self, h, slot, Cs, Merged, Par, H, R};
use super::statement_var::{p3_layout, src_value, Cell, Src, StatementShape, StatementVar};
use super::fp31::M31;
use num_bigint::BigUint;
use std::collections::BTreeMap;
use crate::public_input::BatchHeader;
use ark_bn254::Fr;
use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use p3_batch_stark::BatchProof;
use ss_rap_p3::record::{self, Op};
use ss_rap_p3::state::Params;
use ss_rap_v2::hash::{fr_to_hash, hash_to_fr, poseidon_config, poseidon_hash};
use ss_rap_v2::state::StateStatement;

/// Everything the circuit is built for: the statement's shape and the proof's shape.
pub struct P3SettleShape {
    pub statement: StatementShape,
    pub batch: BatchShape,
    pub params: Params,
}

impl P3SettleShape {
    /// The shape of `st` proven with `p`. `proof` and `ops` (its verification log) may come from
    /// any statement of the same shape: only sizes and transcript seeds are read from them.
    pub fn new(st: &StateStatement, p: &Params, proof: &BatchProof<record::Config>, ops: &[Op]) -> Self {
        // the transfers are private in the Plonky3 proof: the circuit sees the tables only
        Self { statement: StatementShape::of(&st.public_part(), p.log_rows as u32), batch: batch_shape(st, p, &proof.degree_bits, ops), params: *p }
    }

    /// Blob slots of the shape.
    pub fn blob_slots(&self) -> usize {
        let blob = self.batch.inst.iter().find(|s| s.blob).expect("the batch proof has a blob AIR");
        1 << (blob.log_n - ss_rap_p3::blob_eval::LOG_ROWS)
    }
}

/// Native v_umt_root of a proof (`w = batch_witness(..)`) of `st`.
pub fn v_umt_root(st: &StateStatement, w: &BatchWitness) -> [u8; 32] {
    let mut v = vec![hash_to_fr(&st.public_part().digest()), w.main, w.perm, w.quotient];
    v.extend(w.fri.commit_phase_commits.iter().copied());
    fr_to_hash(&poseidon_hash(&v))
}

/// Proves `st` and `blobs` with `p`, checks the proof natively, and returns it with its
/// verification log and blob claim.
pub fn prove(st: &StateStatement, traces: &[Vec<Vec<u32>>; 5], blobs: &BlobInput, p: &Params) -> (BatchProof<record::Config>, Vec<Op>, BlobClaim) {
    let proof = record::prove_one(st, traces, blobs, p);
    let claim = blobs.claim();
    let (ok, ops) = record::verify_one(st, &proof, &claim, p);
    assert!(ok, "Plonky3 proof does not verify natively");
    (proof, ops, claim)
}

pub fn witness(shape: &P3SettleShape, proof: &BatchProof<record::Config>, ops: &[Op]) -> BatchWitness {
    batch_witness(&shape.batch, proof, ops)
}

/// The circuit (values are None during setup).
pub struct P3SettleCircuit<'a> {
    pub shape: &'a P3SettleShape,
    pub st: Option<&'a StateStatement>,
    pub proof: Option<&'a BatchWitness>,
    pub blobs: Option<&'a BlobClaim>,
    pub header: Option<&'a BatchHeader>,
}

impl ConstraintSynthesizer<Fr> for P3SettleCircuit<'_> {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        synth(self.shape, self.st, self.proof, self.blobs, self.header, &cs, &Par::Inline(cs.clone()))
    }
}

/// The same circuit synthesised on several threads (statement, instances at zeta, FRI query
/// groups), merged into one system: same constraints up to the links between the parts.
pub fn synthesize_parallel(shape: &P3SettleShape, st: Option<&StateStatement>, proof: Option<&BatchWitness>, blobs: Option<&BlobClaim>, header: Option<&BatchHeader>, setup: bool) -> R<Merged> {
    par::synthesize(setup, |cs, p| synth(shape, st, proof, blobs, header, cs, p))
}

/// The full assignment only, in the column order of `synthesize_parallel(.., setup = true)`'s
/// matrices: per batch, the matrices of the fixed shape are reused and only this is computed.
pub fn witness_parallel(shape: &P3SettleShape, st: &StateStatement, proof: &BatchWitness, blobs: &BlobClaim, header: &BatchHeader) -> R<Vec<Fr>> {
    par::synthesize_witness(|cs, p| synth(shape, Some(st), Some(proof), Some(blobs), Some(header), cs, p))
}

/// The statement's values the rest of the circuit reads.
struct StmtOut {
    digest: FpVar<Fr>,
    old_root: FpVar<Fr>,
    new_root: FpVar<Fr>,
    limbs: Vec<FpVar<Fr>>,
    cols: Vec<Vec<Vec<M31>>>,
}

fn stages(name: &str, cs: &Cs, t0: std::time::Instant) {
    if std::env::var("P3_STAGES").is_ok() {
        eprintln!("  {name:<28} {:>10} constraints {:>7.2} s", cs.num_constraints(), t0.elapsed().as_secs_f64());
    }
}

#[derive(Clone, Copy)]
enum Table {
    Lane(usize),
    Addr,
}

impl Table {
    fn layout(self, shape: &crate::wrapper::statement_var::StatementShape) -> Vec<Vec<Cell>> {
        match self {
            Table::Lane(l) => p3_layout(shape, l),
            Table::Addr => crate::wrapper::statement_var::p3_addr_layout(shape),
        }
    }
    fn cols(self, stmt: &StatementVar) -> Vec<Vec<M31>> {
        match self {
            Table::Lane(l) => stmt.p3_public_cols(l),
            Table::Addr => stmt.p3_addr_cols(),
        }
    }
}

/// Inline: the statement in the parent. Threads: parent slots for the digest, roots, limbs and
/// every statement value a public table reads, filled by a child that builds `StatementVar`.
fn statement<'s, 'e: 's>(shape: &'e P3SettleShape, st: Option<&'e StateStatement>, cs: &Cs, par: &Par<'s, 'e>) -> R<StmtOut> {
    // which statement table each instance's periodic columns are: a lane's public table or the
    // address table (None: no periodic columns)
    let tables: Vec<Option<Table>> = shape.batch.inst.iter().map(|s| if let Some(l) = s.public_lane { Some(Table::Lane(l)) } else if s.addr_table { Some(Table::Addr) } else { None }).collect();
    if par.is_inline() {
        let t0 = std::time::Instant::now();
        let stmt = StatementVar::witness(cs, st, shape.statement.clone())?;
        stages("statement", cs, t0);
        return Ok(StmtOut {
            limbs: stmt.digest_limbs()?,
            cols: tables.iter().map(|t| t.map(|t| t.cols(&stmt)).unwrap_or_default()).collect(),
            digest: stmt.digest.clone(),
            old_root: stmt.old_root.clone(),
            new_root: stmt.new_root.clone(),
        });
    }
    let fr = |f: fn(&StateStatement) -> [u8; 32]| st.map(|st| hash_to_fr(&f(st)));
    let digest = slot(cs, fr(|st| st.public_part().digest()))?;
    let old_root = slot(cs, fr(StateStatement::old_root))?;
    let new_root = slot(cs, fr(StateStatement::new_root))?;
    let native_limbs = st.map(ss_rap_p3::state::digest_limbs);
    let limbs: Vec<FpVar<Fr>> = (0..ss_rap_p3::state::DIGEST_LIMBS).map(|k| slot(cs, native_limbs.as_ref().map(|l| Fr::from(l[k] as u64)))).collect::<R<_>>()?;
    let layouts: Vec<Option<Vec<Vec<Cell>>>> = tables.iter().map(|t| t.map(|t| t.layout(&shape.statement))).collect();
    let mut srcs: BTreeMap<Src, FpVar<Fr>> = BTreeMap::new();
    for c in layouts.iter().flatten().flatten().flatten() {
        if let Cell::Var(src, _) = c {
            if !srcs.contains_key(src) {
                srcs.insert(*src, slot(cs, st.map(|st| Fr::from(src_value(st, *src))))?);
            }
        }
    }
    let cols = layouts
        .iter()
        .map(|l| {
            l.iter()
                .flatten()
                .map(|c| c.iter().map(|cell| match cell {
                    Cell::Const(v) => M31::constant(*v, 0),
                    Cell::Var(src, bits) => M31 { v: srcs[src].clone(), bound: BigUint::from(1u64) << *bits, ch: 0 },
                }).collect())
                .collect()
        })
        .collect();
    let hd = (h(cs, &digest)?, h(cs, &old_root)?, h(cs, &new_root)?);
    let hl: Vec<H> = limbs.iter().map(|l| h(cs, l)).collect::<R<_>>()?;
    let hs: Vec<(Src, H)> = srcs.iter().map(|(s, v)| Ok((*s, h(cs, v)?))).collect::<R<_>>()?;
    par.spawn(move |io| {
        let t0 = std::time::Instant::now();
        let stmt = StatementVar::witness(&io.cs, st, shape.statement.clone())?;
        io.export(&stmt.digest, &hd.0)?;
        io.export(&stmt.old_root, &hd.1)?;
        io.export(&stmt.new_root, &hd.2)?;
        for (l, t) in stmt.digest_limbs()?.iter().zip(&hl) {
            io.export(l, t)?;
        }
        for (s, t) in &hs {
            io.export(stmt.src(*s), t)?;
        }
        stages("statement (thread)", &io.cs, t0);
        Ok(())
    })?;
    Ok(StmtOut { digest, old_root, new_root, limbs, cols })
}

#[allow(clippy::too_many_arguments)]
fn synth<'s, 'e: 's>(shape: &'e P3SettleShape, st: Option<&'e StateStatement>, proof: Option<&'e BatchWitness>, blobs: Option<&BlobClaim>, header: Option<&BatchHeader>, cs: &Cs, par: &Par<'s, 'e>) -> R<()> {
    let x = FpVar::new_input(cs.clone(), || header.map(|h| h.public_input()).ok_or(SynthesisError::AssignmentMissing))?;
    let so = statement(shape, st, cs, par)?;
    let blob_pv = BlobPublicVar::witness(cs, blobs, shape.blob_slots())?;
    let flat = blob_pv.flat();
    let io = PublicIo { public_values: shape.batch.public_values.iter().map(|&(i, _)| if shape.batch.inst[i].blob { flat.clone() } else { so.limbs.clone() }).collect(), periodic: so.cols };
    let commits = verify_batch_var(cs, &shape.batch, proof, &io, par)?;
    let mut s = PoseidonSpongeVar::new(cs.clone(), poseidon_config());
    let mut v = vec![so.digest.clone()];
    v.extend(commits.0);
    s.absorb(&v)?;
    let v_umt = s.squeeze_field_elements(1)?.remove(0);
    let blobs_hash = HeaderBlobBits::blobs_hash(cs, header)?;
    let evals = blob_evals(cs, &blob_pv, &blobs_hash)?;
    bind_header(cs, &x, &so.old_root, &so.new_root, &v_umt, header, &HeaderBlobBits { blobs_hash, evals })
}

/// Test and fixture helper: the blobs (bytes) of a statement's transfers, with made-up
/// signatures, in the transaction-slot layout.
#[doc(hidden)]
pub fn tests_blob_bytes(st: &StateStatement) -> Vec<Vec<u8>> {
    let txs: Vec<Vec<u8>> = st.lanes.iter().flatten().enumerate().map(|(g, t)| ss_rap_p3::tx_bind::encode_transfer(st, t, 0, &[(g as u8) ^ 0x5a; 65]).to_vec()).collect();
    crate::blob::tx_blobs(&txs).expect("the transfers fit in the blobs")
}

/// The header of a batch proven with `blobs` (the blob point and values from its claim).
#[allow(clippy::too_many_arguments)]
pub fn header(st: &StateStatement, w: &BatchWitness, claim: &BlobClaim, blobs_hash: [u8; 32], batch_number: u64, domain: &crate::public_input::Domain) -> BatchHeader {
    BatchHeader {
        old_state_root: st.old_root(),
        new_state_root: st.new_root(),
        v_umt_root: v_umt_root(st, w),
        blob_versioned_hash: blobs_hash,
        batch_number,
        chain_id: domain.chain_id,
        settlement: domain.settlement,
        blob_point: crate::blob_eval::be32(&claim.z),
        blob_values: super::blob_var::blob_values(claim),
    }
}

/// The blob input for `blobs` (each a full 131072-byte blob) in `slots` slots: elements, and z
/// from their digests and the blobs hash of their versioned hashes.
pub fn blob_input(blobs: &[Vec<u8>], slots: usize) -> Option<(BlobInput, [u8; 32])> {
    if blobs.len() > slots {
        return None;
    }
    let elements: Vec<Vec<BigUint>> = blobs.iter().map(|b| ss_rap_p3::blob_eval::elements(b)).collect::<Option<_>>()?;
    let zero = vec![BigUint::from(0u32); ss_rap_p3::blob_eval::ROWS];
    let d: Vec<[u32; 8]> = (0..slots).map(|j| ss_rap_p3::blob_eval::digests_u32(elements.get(j).unwrap_or(&zero))).collect();
    let hashes: Vec<[u8; 32]> = blobs.iter().map(|b| crate::blob::versioned_hash(b)).collect();
    let bh = crate::blob::blobs_hash(&hashes);
    let z = super::blob_var::blob_point(&d, &bh);
    Some((BlobInput { slots, blobs: elements, z }, bh))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;

    fn sat(c: P3SettleCircuit) -> (bool, usize) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        c.generate_constraints(cs.clone()).unwrap();
        (cs.is_satisfied().unwrap(), cs.num_constraints())
    }

    #[test]
    fn plonky3_settlement_circuit_binds_roots_proof_and_header() {
        let _heavy = crate::heavy_test_lock();
        let (st, traces) = ss_rap_p3::state::tests_case(40, 5);
        let p = Params { log_rows: 5, log_blowup: 1, queries: 4, budget: 3, query_pow: 8 };
        let (bi, bh) = blob_input(&tests_blob_bytes(&st), 1).unwrap();
        let (proof, ops, claim) = prove(&st, &traces, &bi, &p);
        let shape = P3SettleShape::new(&st, &p, &proof, &ops);
        let w = witness(&shape, &proof, &ops);
        let h = header(&st, &w, &claim, bh, 7, &crate::public_input::Domain::DEV);
        let c = Some(&claim);
        let (ok, n) = sat(P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&w), blobs: c, header: Some(&h) });
        assert!(ok, "honest batch");
        eprintln!("Plonky3 settlement circuit (40 tx, 2^5 rows, 4 queries, 8 bits of query grinding): {n} constraints");
        // a header claiming another new root
        let mut bad = h.clone();
        bad.new_state_root[0] ^= 1;
        assert!(!sat(P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&w), blobs: c, header: Some(&bad) }).0, "other new root");
        // a v_umt_root of other commitments
        let mut bad = h.clone();
        bad.v_umt_root[3] ^= 1;
        assert!(!sat(P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&w), blobs: c, header: Some(&bad) }).0, "other v_umt_root");
        // a well-formed statement the proof is not about (one final balance changed), with an
        // honest header for it
        let mut st2 = st.clone();
        st2.states[ss_rap_v2::DEFAULT_RNS_CHANNELS][1].balance += 1;
        let h2 = BatchHeader { new_state_root: st2.new_root(), v_umt_root: v_umt_root(&st2, &w), ..h.clone() };
        assert!(!sat(P3SettleCircuit { shape: &shape, st: Some(&st2), proof: Some(&w), blobs: c, header: Some(&h2) }).0, "statement the proof is not about");
        // a forged opened value
        let mut bw = w.clone();
        bw.inst[1].main_local[3][2] = (bw.inst[1].main_local[3][2] + 5) % 2013265921;
        assert!(!sat(P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&bw), blobs: c, header: Some(&h) }).0, "forged opening");
        // a grinding witness that does not pass the proof-of-work check
        let mut bw = w.clone();
        bw.fri.query_pow_witness = (bw.fri.query_pow_witness + 1) % 2013265921;
        assert!(!sat(P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&bw), blobs: c, header: Some(&h) }).0, "bad proof of work");
        // audit H-01: a header with another blob value, point or blobs hash
        let mut bad = h.clone();
        bad.blob_values[0][31] ^= 1;
        assert!(!sat(P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&w), blobs: c, header: Some(&bad) }).0, "other blob value");
        let mut bad = h.clone();
        bad.blob_point[31] ^= 1;
        assert!(!sat(P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&w), blobs: c, header: Some(&bad) }).0, "other blob point");
        let mut bad = h.clone();
        bad.blob_versioned_hash[0] ^= 1;
        assert!(!sat(P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&w), blobs: c, header: Some(&bad) }).0, "other blobs hash");
        // a blob claim the proof does not make
        let mut c2 = claim.clone();
        c2.s[0] += 1u32;
        let h2 = header(&st, &w, &c2, bh, 7, &crate::public_input::Domain::DEV);
        assert!(!sat(P3SettleCircuit { shape: &shape, st: Some(&st), proof: Some(&w), blobs: Some(&c2), header: Some(&h2) }).0, "blob claim the proof does not make");

        // the parallel synthesis: same statement, merged from the threads' parts
        let m = synthesize_parallel(&shape, Some(&st), Some(&w), c, Some(&h), false).unwrap();
        assert!(m.is_satisfied(), "honest batch, parallel (first unsatisfied: {:?})", m.first_unsatisfied());
        let np = m.matrices.num_constraints;
        eprintln!("parallel synthesis: {np} constraints ({:+} vs inline: links are free, inline exports are equalities)", np as i64 - n as i64);
        assert!(np.abs_diff(n) < n / 100);
        // one set of matrices in memory at a time: keep a fingerprint of these
        let fingerprint = |a: &[Vec<(Fr, usize)>]| {
            use std::hash::{Hash, Hasher};
            let mut hs = std::collections::hash_map::DefaultHasher::new();
            a.hash(&mut hs);
            hs.finish()
        };
        let (nw, fa, assignment) = (m.matrices.num_witness_variables, fingerprint(&m.matrices.a), m.assignment);
        drop(m.matrices);
        let setup = synthesize_parallel(&shape, None, None, None, None, true).unwrap();
        assert_eq!(setup.matrices.num_constraints, np);
        assert_eq!(setup.matrices.num_witness_variables, nw);
        assert_eq!(fingerprint(&setup.matrices.a), fa, "setup and proving matrices");
        // the witness alone (matrices of the shape reused) is the same assignment
        let z = witness_parallel(&shape, &st, &w, &claim, &h).unwrap();
        assert_eq!(z, assignment, "witness-only synthesis");
        drop(assignment);
        let honest = Merged { matrices: setup.matrices, assignment: z };
        assert!(honest.is_satisfied());
        let mut bw = w.clone();
        bw.inst[1].main_local[3][2] = (bw.inst[1].main_local[3][2] + 5) % 2013265921;
        let z = witness_parallel(&shape, &st, &bw, &claim, &h).unwrap();
        assert!(!Merged { matrices: honest.matrices, assignment: z }.is_satisfied(), "forged opening, witness only");
        assert!(!synthesize_parallel(&shape, Some(&st), Some(&bw), c, Some(&h), false).unwrap().is_satisfied(), "forged opening, parallel");
        let mut st2 = st.clone();
        st2.states[ss_rap_v2::DEFAULT_RNS_CHANNELS][1].balance += 1;
        let h2 = BatchHeader { new_state_root: st2.new_root(), v_umt_root: v_umt_root(&st2, &w), ..h.clone() };
        assert!(!synthesize_parallel(&shape, Some(&st2), Some(&w), c, Some(&h2), false).unwrap().is_satisfied(), "statement the proof is not about, parallel");
        let mut bad = h.clone();
        bad.new_state_root[0] ^= 1;
        assert!(!synthesize_parallel(&shape, Some(&st), Some(&w), c, Some(&bad), false).unwrap().is_satisfied(), "other new root, parallel");
    }
}
