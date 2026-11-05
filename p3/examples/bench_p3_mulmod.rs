//! P1: MULMOD on Plonky3 vs the in-house engine (`cargo run --release --example bench_stark_mulmod`).
//! One BabyBear lane with 2^log_rows operations; the in-house benchmark proves 5 lanes of 2^log_rows.
//! cargo run --release -p ss_rap_p3 --example bench_p3_mulmod [log_rows] [log_blowup] [queries]
use num_bigint::BigUint;
use p3_batch_stark::{prove_batch, verify_batch, ProverData, StarkInstance};
use ss_rap_p3::config::{config, Config, Val};
use ss_rap_p3::mulmod::{ByteTableAir, MulModAir, MulModAirs};
use ss_rap_v2::uint256::{Modulus256, MulModRow};
use std::time::Instant;

fn main() {
    if std::env::var("TRACE").is_ok() {
        use tracing_subscriber::layer::SubscriberExt;
        use tracing_subscriber::util::SubscriberInitExt;
        tracing_subscriber::Registry::default().with(tracing_subscriber::EnvFilter::new("info")).with(tracing_forest::ForestLayer::default()).init();
    }
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (log_rows, log_blowup, queries) = (*a.first().unwrap_or(&10), *a.get(1).unwrap_or(&2), *a.get(2).unwrap_or(&50));
    let p = Modulus256::secp256k1();
    let mut s = 1u64;
    let mut next = || {
        let w: Vec<u32> = (0..8)
            .map(|_| {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                (s >> 32) as u32
            })
            .collect();
        BigUint::new(w) % &p.value
    };
    let n = 1usize << log_rows;
    let rows: Vec<MulModRow> = (0..n).map(|_| MulModRow::generate(&next(), &next(), &p)).collect();
    let air = MulModAir::new(&p, log_rows);
    let cfg = config(log_blowup, queries);
    let t0 = Instant::now();
    let trace = air.trace::<Val>(&rows);
    let tt = t0.elapsed();
    let global = std::env::var("GLOBAL").is_ok();
    let pad = MulModRow::generate(&0u32.into(), &0u32.into(), &p);
    let table = ByteTableAir::trace::<Val>(&rows, n, &pad);
    let (airs, degs, traces, pvs): (Vec<MulModAirs>, Vec<usize>, Vec<_>, Vec<Vec<Val>>) = if global {
        (vec![MulModAirs::MulMod(air), MulModAirs::Table(ByteTableAir)], vec![log_rows, 8], vec![&trace, &table], vec![vec![], vec![]])
    } else {
        (vec![MulModAirs::MulMod(air)], vec![log_rows], vec![&trace], vec![vec![]])
    };
    let budget: usize = std::env::var("BUDGET").ok().and_then(|b| b.parse().ok()).unwrap_or(0);
    let pd = ProverData::<Config>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &degs, &vec![budget; airs.len()], log_blowup).unwrap();
    let inst = StarkInstance::new_multiple(&airs, &traces, &pvs);
    let t0 = Instant::now();
    let proof = prove_batch(&cfg, &inst, &pd).unwrap();
    let pt = t0.elapsed();
    let t0 = Instant::now();
    let ok = verify_batch(&cfg, &airs, &proof, &pvs, &pd.common).is_ok();
    println!("plonky3 MULMOD secp256k1, BabyBear lane: {n} ops, blowup {}, {queries} queries: trace {tt:.1?}, prove {pt:.2?}, verify {:.1?}, ok {ok}", 1 << log_blowup, t0.elapsed());
    println!("  per op: {:.1} us (x5 lanes ~ {:.2?} for {} ops)", pt.as_secs_f64() * 1e6 / n as f64, pt * 5, 5 * n);
}
