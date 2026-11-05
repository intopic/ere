//! STARK configuration whose Merkle trees and Fiat-Shamir transcript use Poseidon2 over BN254
//! (width 3, x^5, 8 full + 56 partial rounds), so that the BN254 settlement circuit (R8) can
//! verify the lane proofs. Lane values are packed several per BN254 element (Plonky3's
//! MultiField32 sponge and challenger).
//!
//! Round constants: our own, derived from blake3("SS-RAP/v2/poseidon2-bn254-t3/<i>") mod r, so
//! that the circuit can regenerate them (`round_constants`). Production should switch to the
//! reference constants of the Poseidon2 paper (zkhash RC3) once the circuit embeds them.
use num_bigint::BigUint;
use p3_bn254::{Bn254, Poseidon2Bn254};
use p3_challenger::MultiField32Challenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::{BinomialExtensionField, BinomiallyExtendable};
use p3_field::{PrimeField32, TwoAdicField};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_poseidon2::ExternalLayerConstants;
use p3_symmetric::{MultiField32PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;

pub const HALF_FULL_ROUNDS: usize = 4;
pub const PARTIAL_ROUNDS: usize = 56;

pub type Perm = Poseidon2Bn254<3>;
type Hash<F> = MultiField32PaddingFreeSponge<F, Bn254, Perm, 3, 2, 1>;
type Compress = TruncatedPermutation<Perm, 2, 1, 3>;
pub type ValMmcs<F> = MerkleTreeMmcs<F, Bn254, Hash<F>, Compress, 2, 1>;
pub type Challenge<F> = BinomialExtensionField<F, 4>;
type ChallengeMmcs<F> = ExtensionMmcs<F, Challenge<F>, ValMmcs<F>>;
pub type Challenger<F> = MultiField32Challenger<F, Bn254, Perm, 3, 2>;
type Pcs<F> = TwoAdicFriPcs<F, Radix2DitParallel<F>, ValMmcs<F>, ChallengeMmcs<F>>;
pub type Config<F> = StarkConfig<Pcs<F>, Challenge<F>, Challenger<F>>;

/// BN254 scalar field modulus r.
pub fn modulus() -> BigUint {
    BigUint::parse_bytes(b"21888242871839275222246405745257275088548364400416034343698204186575808495617", 10).unwrap()
}

fn constant(i: usize) -> BigUint {
    let mut h = blake3::Hasher::new();
    h.update(format!("SS-RAP/v2/poseidon2-bn254-t3/{i}").as_bytes());
    let mut out = [0u8; 64];
    h.finalize_xof().fill(&mut out);
    BigUint::from_bytes_le(&out) % modulus()
}

/// (initial external [4][3], terminal external [4][3], internal [56]) round constants.
pub fn round_constants() -> (Vec<[BigUint; 3]>, Vec<[BigUint; 3]>, Vec<BigUint>) {
    let mut i = 0;
    let mut next = || {
        i += 1;
        constant(i)
    };
    let initial = (0..HALF_FULL_ROUNDS).map(|_| std::array::from_fn(|_| next())).collect();
    let terminal = (0..HALF_FULL_ROUNDS).map(|_| std::array::from_fn(|_| next())).collect();
    let internal = (0..PARTIAL_ROUNDS).map(|_| next()).collect();
    (initial, terminal, internal)
}

pub fn perm() -> Perm {
    let f = |x: &BigUint| Bn254::from_biguint(num_bigint_05::BigUint::from_bytes_le(&x.to_bytes_le())).unwrap();
    let (i, t, p) = round_constants();
    let conv = |v: Vec<[BigUint; 3]>| v.iter().map(|r| [f(&r[0]), f(&r[1]), f(&r[2])]).collect();
    Perm::new(ExternalLayerConstants::new(conv(i), conv(t)), p.iter().map(f).collect())
}

/// FRI with `2^log_blowup` blowup and `queries` queries, no proof of work.
pub fn config<F>(log_blowup: usize, queries: usize) -> Config<F>
where
    F: PrimeField32 + TwoAdicField + BinomiallyExtendable<4>,
{
    let p = perm();
    let mmcs = ValMmcs::<F>::new(Hash::new(p.clone()).unwrap(), Compress::new(p.clone()), 0);
    let fri = FriParameters {
        log_blowup,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: queries,
        batch_proof_of_work_bits: 0,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: ChallengeMmcs::new(mmcs.clone()),
    };
    StarkConfig::new(Pcs::new(Radix2DitParallel::default(), mmcs, fri), Challenger::new(p).unwrap())
}
