//! STARK configuration for one RNS lane F (any of the 5 Montgomery-31 fields): quartic
//! extension, Keccak Merkle trees and a Keccak challenger (generic over the field).
//! P4 replaces Keccak by Poseidon2 over BN254 so that the R8 circuit can verify the proof.
use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::{BinomialExtensionField, BinomiallyExtendable};
use p3_field::{PrimeField32, TwoAdicField};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_keccak::{Keccak256Hash, KeccakF};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{CompressionFunctionFromHasher, PaddingFreeSponge, SerializingHasher};
use p3_uni_stark::StarkConfig;

pub use crate::fields::{Lane3, Lane4, Lane5};
pub use p3_baby_bear::BabyBear;
pub use p3_koala_bear::KoalaBear;

type U64Hash = PaddingFreeSponge<KeccakF, 25, 17, 4>;
type FieldHash = SerializingHasher<U64Hash>;
type Compress = CompressionFunctionFromHasher<U64Hash, 2, 4>;
pub type ValMmcs<F> = MerkleTreeMmcs<[F; p3_keccak::VECTOR_LEN], [u64; p3_keccak::VECTOR_LEN], FieldHash, Compress, 2, 4>;
pub type Challenge<F> = BinomialExtensionField<F, 4>;
type ChallengeMmcs<F> = ExtensionMmcs<F, Challenge<F>, ValMmcs<F>>;
type Challenger<F> = SerializingChallenger32<F, HashChallenger<u8, Keccak256Hash, 32>>;
type Pcs<F> = TwoAdicFriPcs<F, Radix2DitParallel<F>, ValMmcs<F>, ChallengeMmcs<F>>;
pub type Config<F> = StarkConfig<Pcs<F>, Challenge<F>, Challenger<F>>;

/// FRI with `2^log_blowup` blowup and `queries` queries, no proof of work.
pub fn config<F>(log_blowup: usize, queries: usize) -> Config<F>
where
    F: PrimeField32 + TwoAdicField + BinomiallyExtendable<4>,
{
    let h = U64Hash::new(KeccakF {});
    let mmcs = ValMmcs::<F>::new(FieldHash::new(h), Compress::new(h), 3);
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
    StarkConfig::new(Pcs::new(Radix2DitParallel::default(), mmcs, fri), Challenger::from_hasher(vec![], Keccak256Hash {}))
}
