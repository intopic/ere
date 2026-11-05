//! STARK configuration: a 31-bit two-adic field, its quartic extension, Poseidon2 Merkle trees
//! and a Poseidon2 duplex challenger (all in the lane's own field).
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::Field;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;
use rand::rngs::StdRng;
use rand::SeedableRng;

pub type Val = BabyBear;
pub type Challenge = BinomialExtensionField<Val, 4>;
type Perm = Poseidon2BabyBear<16>;
type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs = MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, Hash, Compress, 2, 8>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
type Pcs = TwoAdicFriPcs<Val, Radix2DitParallel<Val>, ValMmcs, ChallengeMmcs>;
pub type Config = StarkConfig<Pcs, Challenge, Challenger>;

/// FRI with `2^log_blowup` blowup and `queries` queries, no proof of work.
pub fn config(log_blowup: usize, queries: usize) -> Config {
    let mut rng = StdRng::seed_from_u64(0x5352_4150);
    let perm = Perm::new_from_rng_128(&mut rng);
    let mmcs = ValMmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), 0);
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
    StarkConfig::new(Pcs::new(Radix2DitParallel::default(), mmcs, fri), Challenger::new(perm))
}
