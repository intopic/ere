//! MULMOD on Plonky3 in all 5 RNS lanes vs the in-house engine (`bench_stark_mulmod`).
//! Each lane proves its own 2^log_rows operations (lanes are independent, as in the in-house
//! engine), so the batch is 5 * 2^log_rows.
//! cargo run --release -p ss_rap_p3 --example bench_p3_mulmod [log_rows] [log_blowup] [queries] [budget]
use num_bigint::BigUint;
use p3_batch_stark::{prove_batch, verify_batch, ProverData, StarkInstance};
use p3_field::extension::BinomiallyExtendable;
use p3_field::{PrimeField32, TwoAdicField};
use ss_rap_p3::config::{config, BabyBear, Config, KoalaBear, Lane3, Lane4, Lane5};
use ss_rap_p3::mulmod::{ByteTableAir, MulModAir, MulModAirs};
use ss_rap_v2::uint256::{Modulus256, MulModRow};
use std::time::{Duration, Instant};

fn lane<F>(name: &str, rows: &[MulModRow], p: &Modulus256, log_rows: usize, log_blowup: usize, queries: usize, budget: usize) -> (Duration, Duration)
where
    F: PrimeField32 + TwoAdicField + BinomiallyExtendable<4>,
{
    let cfg = config::<F>(log_blowup, queries);
    let air = MulModAir::new(p, log_rows);
    let trace = air.trace::<F>(rows);
    let pad = MulModRow::generate(&0u32.into(), &0u32.into(), p);
    let table = ByteTableAir::trace::<F>(rows, 1 << log_rows, &pad);
    let airs = vec![MulModAirs::MulMod(air), MulModAirs::Table(ByteTableAir)];
    let pvs: Vec<Vec<F>> = vec![vec![], vec![]];
    let pd = ProverData::<Config<F>>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &[log_rows, 8], &[budget, budget], log_blowup).unwrap();
    let traces = [&trace, &table];
    let inst = StarkInstance::new_multiple(&airs, &traces, &pvs);
    let t0 = Instant::now();
    let proof = prove_batch(&cfg, &inst, &pd).unwrap();
    let pt = t0.elapsed();
    let t0 = Instant::now();
    assert!(verify_batch(&cfg, &airs, &proof, &pvs, &pd.common).is_ok(), "{name}");
    let vt = t0.elapsed();
    println!("  {name:9} prove {pt:>9.2?}  verify {vt:>8.2?}");
    (pt, vt)
}

fn main() {
    let a: Vec<usize> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    let (log_rows, log_blowup, queries, budget) = (*a.first().unwrap_or(&12), *a.get(1).unwrap_or(&1), *a.get(2).unwrap_or(&100), *a.get(3).unwrap_or(&3));
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
    let rows: Vec<Vec<MulModRow>> = (0..5).map(|_| (0..n).map(|_| MulModRow::generate(&next(), &next(), &p)).collect()).collect();
    println!("plonky3 MULMOD secp256k1: {} ops in 5 RNS lanes ({n}/lane), blowup {}, {queries} queries, lookup budget {budget}", 5 * n, 1 << log_blowup);
    let r = [
        lane::<BabyBear>("BabyBear", &rows[0], &p, log_rows, log_blowup, queries, budget),
        lane::<KoalaBear>("KoalaBear", &rows[1], &p, log_rows, log_blowup, queries, budget),
        lane::<Lane3>("Lane3", &rows[2], &p, log_rows, log_blowup, queries, budget),
        lane::<Lane4>("Lane4", &rows[3], &p, log_rows, log_blowup, queries, budget),
        lane::<Lane5>("Lane5", &rows[4], &p, log_rows, log_blowup, queries, budget),
    ];
    let total: Duration = r.iter().map(|x| x.0).sum();
    println!("  total prove {total:.2?} ({:.1} us per MULMOD), lanes one after another on all cores", total.as_secs_f64() * 1e6 / (5 * n) as f64);
}
