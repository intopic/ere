//! B2 baseline: N Poseidon2-KoalaBear-16 permutations proven with Plonky3 (p3-uni-stark,
//! p3-poseidon2-air, Keccak Merkle trees), one permutation per row, same FRI parameters as
//! `cargo run --release --example bench_vs_plonky3` in the main repository.
//! cargo run --release -- [log_rows] [log_blowup] [queries]
use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_keccak::{Keccak256Hash, KeccakF};
use p3_koala_bear::{GenericPoseidon2LinearLayersKoalaBear, KoalaBear, KOALABEAR_POSEIDON2_HALF_FULL_ROUNDS, KOALABEAR_POSEIDON2_PARTIAL_ROUNDS_16, KOALABEAR_S_BOX_DEGREE};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_poseidon2_air::{RoundConstants, VectorizedPoseidon2Air};
use p3_symmetric::{CompressionFunctionFromHasher, PaddingFreeSponge, SerializingHasher};
use p3_uni_stark::{prove, verify, StarkConfig};
use rand::rngs::StdRng;
use rand::SeedableRng;
use std::time::Instant;

type Val = KoalaBear;
type Challenge = BinomialExtensionField<Val, 4>;
type U64Hash = PaddingFreeSponge<KeccakF, 25, 17, 4>;
type FieldHash = SerializingHasher<U64Hash>;
type MyCompress = CompressionFunctionFromHasher<U64Hash, 2, 4>;
type ValMmcs = MerkleTreeMmcs<[Val; p3_keccak::VECTOR_LEN], [u64; p3_keccak::VECTOR_LEN], FieldHash, MyCompress, 2, 4>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = SerializingChallenger32<Val, HashChallenger<u8, Keccak256Hash, 32>>;
type Dft = p3_dft::Radix2DitParallel<Val>;
type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn run<const DEG: u64, const REGS: usize>(log_rows: usize, log_blowup: usize, queries: usize) {
    let u64_hash = U64Hash::new(KeccakF {});
    let val_mmcs = ValMmcs::new(FieldHash::new(u64_hash), MyCompress::new(u64_hash), 3);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let mut rng = StdRng::seed_from_u64(1);
    let air: VectorizedPoseidon2Air<Val, GenericPoseidon2LinearLayersKoalaBear, 16, DEG, REGS, KOALABEAR_POSEIDON2_HALF_FULL_ROUNDS, KOALABEAR_POSEIDON2_PARTIAL_ROUNDS_16, 1> =
        VectorizedPoseidon2Air::new(RoundConstants::from_rng(&mut rng));
    let mut fri = FriParameters::new_benchmark(challenge_mmcs);
    fri.log_blowup = log_blowup;
    fri.num_queries = queries;
    fri.query_proof_of_work_bits = 0;
    let t0 = Instant::now();
    let trace = air.generate_vectorized_trace_rows(1 << log_rows, fri.log_blowup);
    let tt = t0.elapsed();
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri);
    let config = MyConfig::new(pcs, Challenger::from_hasher(vec![], Keccak256Hash {}));
    let t0 = Instant::now();
    let proof = prove(&config, &air, trace, &[]).unwrap();
    let pt = t0.elapsed();
    let t0 = Instant::now();
    let ok = verify(&config, &air, &proof, &[]).is_ok();
    let w = p3_air::BaseAir::<Val>::width(&air);
    println!("  plonky3, keccak, x^{DEG}, {REGS} reg, {w} cols   trace {tt:>7.1?}  prove {pt:>8.2?}  verify {:>7.2?}  ok {ok}", t0.elapsed());
}

fn main() {
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (log_rows, log_blowup, queries) = (*a.first().unwrap_or(&13), *a.get(1).unwrap_or(&2), *a.get(2).unwrap_or(&50));
    println!("plonky3 0.9.0-rc.2: {} Poseidon2-KoalaBear-16 permutations, blowup {}, {queries} queries, no PoW", 1 << log_rows, 1 << log_blowup);
    run::<KOALABEAR_S_BOX_DEGREE, 0>(log_rows, log_blowup, queries);
    run::<7, 1>(log_rows, log_blowup, queries);
}
