//! cargo run --release --example bench_scenarios -- [--prover ark|cpu|cuda] [--quick]
//!     [--accounts 200] [--only S1,S3] [--out bench.jsonl] [--settle-gas 280000]
//!
//! Ten load scenarios modelled on Ethereum mainnet traffic (docs: "Plani i testeve në GPU"),
//! run through the real pipeline: signed txs -> sequencer -> 5-lane Plonky3 STARK -> Plonky3
//! settlement circuit -> Groth16 (MSMs on arkworks, or ICICLE on CPU or CUDA) -> verify.
//! One JSON line per batch and per scenario goes to --out; a summary table to stdout.
//!
//! A circuit key is for one batch shape (accounts in the state, txs per lane), so each new
//! shape pays a one-off setup (reported apart, `setup_s`); batches of the same shape reuse it.

use ark_bn254::{Bn254, Fr};
use ark_groth16::{ProvingKey, VerifyingKey};
use ss_rap_gpu::{blinding, init, prove, Backend, GpuKey};
use ss_rap_settlement::fees::{batch_economics, CostModel, FeeSchedule, TxKind};
use ss_rap_settlement::pipeline::{blob_versioned_hash, P3Params, P3Prover};
use ss_rap_settlement::public_input::BatchHeader;
use ss_rap_settlement::sequencer::{address_of, dev_key, SealedBatch, SeqError, Sequencer, Tx};
use ss_rap_settlement::wrapper::p3settle;
use std::io::Write;
use std::time::{Duration, Instant};

const CHAIN: u64 = 31337;
/// Ethereum mainnet today: about 12-15 tx/s, one block every 12 s.
const ETH_TPS: usize = 15;
const BLOCK_S: f64 = 12.0;

struct Opts {
    prover: String,
    quick: bool,
    accounts: usize,
    only: Option<Vec<String>>,
    out: String,
    settle_gas: u64,
}

fn opts() -> Opts {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let get = |k: &str| a.iter().position(|x| x == k).and_then(|i| a.get(i + 1)).cloned();
    Opts {
        prover: get("--prover").unwrap_or_else(|| "ark".into()),
        quick: a.iter().any(|x| x == "--quick"),
        accounts: get("--accounts").map(|v| v.parse().unwrap()).unwrap_or(200),
        only: get("--only").map(|v| v.split(',').map(|s| s.trim().to_uppercase()).collect()),
        out: get("--out").unwrap_or_else(|| "bench.jsonl".into()),
        settle_gas: get("--settle-gas").map(|v| v.parse().unwrap()).unwrap_or(280_000),
    }
}

/// The world every scenario starts from: `n` funded accounts with deterministic keys.
struct World {
    keys: Vec<k256::ecdsa::SigningKey>,
    addrs: Vec<[u8; 20]>,
}

impl World {
    fn new(n: usize) -> Self {
        let keys: Vec<_> = (0..n as u64).map(dev_key).collect();
        let addrs = keys.iter().map(|k| address_of(k.verifying_key())).collect();
        Self { keys, addrs }
    }
    fn sequencer(&self, max_batch: usize) -> Sequencer {
        let g: Vec<([u8; 20], u64)> = self.addrs.iter().map(|a| (*a, 1_000_000_000)).collect();
        let mut s = Sequencer::new(&g, max_batch, FeeSchedule::default());
        s.chain_id = CHAIN;
        s
    }
}

/// Deterministic xorshift, so CPU and GPU runs prove exactly the same transactions.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Builds batches from (from, to) pairs; `kind_at(k)` follows the PDF mix (52.6% transfers).
struct Gen<'w> {
    w: &'w World,
    seq: Sequencer,
    nonces: Vec<u32>,
    soft: Vec<Duration>,
    k: usize,
}

impl<'w> Gen<'w> {
    fn new(w: &'w World, max_batch: usize) -> Self {
        Self { w, seq: w.sequencer(max_batch), nonces: vec![0; w.addrs.len()], soft: Vec::new(), k: 0 }
    }
    fn send(&mut self, from: usize, to: [u8; 20]) {
        let kind = if (self.k * 1000 / 1000) % 1000 < 526 && self.k % 1000 < 526 { TxKind::Transfer } else { TxKind::Swap };
        let tx = Tx::signed(&self.w.keys[from], to, 1 + (self.k as u64 * 7919) % 10_000, self.nonces[from], kind, CHAIN);
        let t0 = Instant::now();
        self.seq.submit(tx).expect("valid tx");
        self.soft.push(t0.elapsed());
        self.nonces[from] += 1;
        self.k += 1;
    }
    fn seal(&mut self) -> SealedBatch {
        self.seq.seal()
    }
}

fn uniform(w: &World, rng: &mut Rng, g: &mut Gen, n: usize) {
    for _ in 0..n {
        let f = rng.below(w.addrs.len());
        let mut t = rng.below(w.addrs.len());
        if t == f {
            t = (t + 1) % w.addrs.len();
        }
        g.send(f, w.addrs[t]);
    }
}

struct Scenario {
    id: &'static str,
    name: &'static str,
    batches: Vec<SealedBatch>,
    soft: Vec<Duration>,
    /// Seconds over which the scenario's transactions arrive.
    arrival_s: f64,
}

fn scenarios(w: &World, only: &Option<Vec<String>>) -> Vec<Scenario> {
    let want = |id: &str| only.as_ref().map_or(true, |o| o.iter().any(|x| x == id));
    let n = w.addrs.len();
    let mut out = Vec::new();
    let mut push = |id, name, g: Gen, batches, arrival_s| out.push(Scenario { id, name, batches, soft: g.soft, arrival_s });
    if want("S1") {
        // quiet night: one user, the batch closes on the timer
        let mut g = Gen::new(w, 1000);
        g.send(0, w.addrs[1]);
        let b = vec![g.seal()];
        push("S1", "Natë e qetë: 1 tx", g, b, BLOCK_S);
    }
    if want("S2") {
        // a normal day: 15 tx/s, one batch per 12 s block (180 tx), three blocks
        let mut g = Gen::new(w, 1000);
        let mut rng = Rng(2);
        let mut b = Vec::new();
        for _ in 0..3 {
            uniform(w, &mut rng, &mut g, ETH_TPS * BLOCK_S as usize);
            b.push(g.seal());
        }
        push("S2", "Ditë normale: 15 tx/s", g, b, 3.0 * BLOCK_S);
    }
    if want("S3") {
        let mut g = Gen::new(w, 1000);
        uniform(w, &mut Rng(3), &mut g, 1000);
        let b = vec![g.seal()];
        push("S3", "Batch i plotë: 1 000 tx", g, b, 1.0);
    }
    if want("S4") {
        // NFT mint: 5 000 tx in 10 s -> five full batches queued behind each other
        let mut g = Gen::new(w, 1000);
        let mut rng = Rng(4);
        let mut b = Vec::new();
        for _ in 0..5 {
            uniform(w, &mut rng, &mut g, 1000);
            b.push(g.seal());
        }
        push("S4", "Pikë (mint NFT): 5 000 tx në 10 s", g, b, 10.0);
    }
    if want("S5") {
        // sustained mainnet load: ten 12-s batches back to back, extrapolated to 24 h
        let mut g = Gen::new(w, 1000);
        let mut rng = Rng(5);
        let mut b = Vec::new();
        for _ in 0..10 {
            uniform(w, &mut rng, &mut g, ETH_TPS * BLOCK_S as usize);
            b.push(g.seal());
        }
        push("S5", "Pa ndalim: 10 batch-e radhazi (shtrirë në 24 orë)", g, b, 10.0 * BLOCK_S);
    }
    if want("S6") {
        // hot accounts: 80% of the txs come from 1% of the accounts (long nonce chains)
        let mut g = Gen::new(w, 1000);
        let mut rng = Rng(6);
        let hot = (n / 100).max(1);
        for _ in 0..1000 {
            let f = if rng.below(10) < 8 { rng.below(hot) } else { rng.below(n) };
            let t = (f + 1 + rng.below(n - 1)) % n;
            g.send(f, w.addrs[t]);
        }
        let b = vec![g.seal()];
        push("S6", "Llogari të nxehta: 80% nga 1%", g, b, 1.0);
    }
    if want("S7") {
        // state growth: 1 000 transfers to 1 000 new addresses
        let mut g = Gen::new(w, 1000);
        for k in 0..1000 {
            let fresh = address_of(dev_key(1_000_000 + k as u64).verifying_key());
            g.send(k % n, fresh);
        }
        let b = vec![g.seal()];
        push("S7", "1 000 llogari të reja", g, b, 1.0);
    }
    if want("S9") {
        let mut g = Gen::new(w, 1000);
        uniform(w, &mut Rng(9), &mut g, 1000);
        let b = vec![g.seal()];
        push("S9", "Përzierja e PDF-së: 52.6% transfere / 47.4% swap", g, b, 1.0);
    }
    out
}

/// S8: a flood of invalid transactions (bad signature, zero amount, bad nonce): refusal rate.
fn invalid_flood(w: &World, n: usize) -> (f64, usize) {
    let mut s = w.sequencer(1000);
    let t0 = Instant::now();
    let mut refused = 0;
    for k in 0..n {
        let mut tx = Tx::signed(&w.keys[k % w.keys.len()], w.addrs[(k + 1) % w.addrs.len()], 5, 0, TxKind::Transfer, CHAIN);
        match k % 3 {
            0 => tx.sig[10] ^= 1,
            1 => tx = Tx::signed(&w.keys[k % w.keys.len()], w.addrs[(k + 1) % w.addrs.len()], 0, 0, TxKind::Transfer, CHAIN),
            _ => tx = Tx::signed(&w.keys[k % w.keys.len()], w.addrs[(k + 1) % w.addrs.len()], 5, 99, TxKind::Transfer, CHAIN),
        }
        if matches!(s.submit(tx), Err(SeqError::BadSignature | SeqError::ZeroAmount | SeqError::BadNonce { .. })) {
            refused += 1;
        }
    }
    (n as f64 / t0.elapsed().as_secs_f64(), refused)
}

struct Keyed {
    shape: (usize, usize),
    prover: P3Prover,
    pk: ProvingKey<Bn254>,
    vk: VerifyingKey<Bn254>,
    gpu: Option<GpuKey>,
    setup_s: f64,
}

fn params(n_tx: usize, quick: bool) -> P3Params {
    let log_rows = ss_rap_v2::state::params(n_tx, 2, 50).log_rows as usize;
    if quick {
        P3Params { log_rows, log_blowup: 1, queries: 4, budget: 3, query_pow: 8 }
    } else {
        P3Params { log_rows, log_blowup: 3, queries: 28, budget: 3, query_pow: 16 }
    }
}

fn pct(v: &mut [Duration], p: usize) -> f64 {
    v.sort();
    v[(v.len() * p / 100).min(v.len() - 1)].as_secs_f64() * 1e3
}

fn peak_rss_gb() -> f64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).and_then(|l| l.split_whitespace().nth(1)?.parse::<f64>().ok()))
        .map_or(0.0, |kb| kb / 1048576.0)
}

fn main() {
    let o = opts();
    let backend = match o.prover.as_str() {
        "ark" => Backend::Ark,
        "cpu" => {
            init("CPU").expect("ICICLE CPU backend");
            Backend::Icicle
        }
        "cuda" => {
            init("CUDA").expect("ICICLE CUDA backend: set ICICLE_BACKEND_INSTALL_DIR");
            Backend::Icicle
        }
        p => panic!("unknown --prover {p} (ark, cpu, cuda)"),
    };
    let mut out = std::fs::File::create(&o.out).unwrap();
    let w = World::new(o.accounts);
    println!("SS-RAP v2 scenarios: prover {}, {} accounts, {} parameters, {} threads", o.prover, o.accounts, if o.quick { "quick (NOT production)" } else { "blowup 8 x 28 queries + 16 bits" }, rayon::current_num_threads());
    println!("{:<4} {:<46} {:>6} {:>8} {:>9} {:>9} {:>9} {:>9} {:>9}", "id", "skenari", "tx", "setup s", "STARK s", "witn. s", "MSM s", "prova s", "$/tx");

    let mut keyed: Option<Keyed> = None;
    for sc in scenarios(&w, &o.only) {
        let mut soft = sc.soft.clone();
        let (p50, p99) = (pct(&mut soft, 50), pct(&mut soft, 99));
        let mut total_prove = 0.0;
        let mut last = (0.0, 0.0, 0.0, 0.0, 0.0);
        let mut setup_s = 0.0;
        let mut econ = None;
        for b in &sc.batches {
            let shape = (b.addrs.len(), b.txs.len());
            if keyed.as_ref().map_or(true, |k| k.shape != shape) {
                drop(keyed.take()); // free the previous key first
                let t0 = Instant::now();
                let (prover, (pk, vk)) = P3Prover::new(b, params(b.txs.len(), o.quick)).expect("shape");
                let gpu = matches!(backend, Backend::Icicle).then(|| GpuKey::new(&pk));
                keyed = Some(Keyed { shape, prover, pk, vk, gpu, setup_s: t0.elapsed().as_secs_f64() });
                setup_s += keyed.as_ref().unwrap().setup_s;
            }
            let k = keyed.as_ref().unwrap();
            let p = k.prover.shape.params;
            let t_batch = Instant::now();
            let t0 = Instant::now();
            let (st, traces) = ss_rap_v2::state::build(&b.addrs, &b.old_states, &b.transfers(), p.log_rows as u32, true).expect("valid batch");
            let (proof, ops) = p3settle::prove(&st, &traces, &p);
            let stark_s = t0.elapsed().as_secs_f64();
            let wit = p3settle::witness(&k.prover.shape, &proof, &ops);
            let header = BatchHeader { old_state_root: b.old_state_root, new_state_root: b.new_state_root, v_umt_root: p3settle::v_umt_root(&st, &wit), blob_versioned_hash: blob_versioned_hash(&b.blob_data()).expect("blob"), batch_number: b.batch_number, chain_id: CHAIN };
            let t0 = Instant::now();
            let z = p3settle::witness_parallel(&k.prover.shape, &st, &wit, &header).expect("witness");
            let witness_s = t0.elapsed().as_secs_f64();
            let (r, s) = blinding(b.batch_number);
            let (g, times) = prove(&k.pk, k.gpu.as_ref(), &k.prover.matrices, &z, r, s, &backend);
            let ok = ss_rap_settlement::groth16::verify(&k.vk, header.public_input(), &g);
            assert!(ok, "{}: proof of batch {} does not verify", sc.id, b.batch_number);
            let batch_s = t_batch.elapsed().as_secs_f64();
            total_prove += batch_s;
            let msm_s = (times.msm_g1 + times.msm_g2 + times.convert).as_secs_f64();
            last = (stark_s, witness_s, times.witness_map.as_secs_f64(), msm_s, batch_s);
            let cost = CostModel { settle_gas: o.settle_gas, prover_seconds: batch_s, ..CostModel::default() };
            let e = batch_economics(&b.kinds(), &FeeSchedule::default(), &cost);
            writeln!(
                out,
                r#"{{"kind":"batch","scenario":"{}","prover":"{}","batch":{},"txs":{},"accounts":{},"constraints":{},"setup_s":{:.2},"stark_s":{:.3},"witness_s":{:.3},"ntt_s":{:.3},"msm_g1_s":{:.3},"msm_g2_s":{:.3},"convert_s":{:.3},"groth16_s":{:.3},"batch_s":{:.3},"verified":{},"cost_per_tx_usd":{:.6},"fee_usd":{:.6},"margin_pct":{:.1},"peak_rss_gb":{:.2}}}"#,
                sc.id, o.prover, b.batch_number, b.txs.len(), b.addrs.len(), k.prover.matrices.num_constraints, k.setup_s, stark_s, witness_s,
                times.witness_map.as_secs_f64(), times.msm_g1.as_secs_f64(), times.msm_g2.as_secs_f64(), times.convert.as_secs_f64(), times.total.as_secs_f64(), batch_s, ok,
                e.cost_per_tx_usd, e.avg_fee_usd, e.net_margin_pct, peak_rss_gb()
            )
            .unwrap();
            econ = Some(e);
        }
        let e = econ.unwrap();
        let txs: usize = sc.batches.iter().map(|b| b.txs.len()).sum();
        let per_batch = total_prove / sc.batches.len() as f64;
        // one prover, batches proven one after another as they arrive
        let drain_s = total_prove.max(sc.arrival_s);
        writeln!(
            out,
            r#"{{"kind":"scenario","scenario":"{}","name":"{}","prover":"{}","batches":{},"txs":{},"soft_p50_ms":{:.3},"soft_p99_ms":{:.3},"setup_s":{:.2},"prove_per_batch_s":{:.3},"all_proven_after_s":{:.2},"keeps_up_with_12s_blocks":{},"batches_per_day_one_machine":{:.0},"tx_per_day_one_machine_full_batches":{:.0},"cost_per_tx_usd":{:.6}}}"#,
            sc.id, sc.name, o.prover, sc.batches.len(), txs, p50, p99, setup_s, per_batch, drain_s, per_batch <= BLOCK_S, 86_400.0 / per_batch,
            86_400.0 / per_batch * 1000.0, e.cost_per_tx_usd
        )
        .unwrap();
        println!("{:<4} {:<46} {:>6} {:>8.1} {:>9.2} {:>9.2} {:>9.2} {:>9.2} {:>9.5}", sc.id, sc.name, txs, setup_s, last.0, last.1, last.3, per_batch, e.cost_per_tx_usd);
        if sc.id == "S9" {
            // S10: the same batch at higher L1 gas prices
            for gwei in [1.0, 10.0, 100.0] {
                let cost = CostModel { settle_gas: o.settle_gas, gas_price_gwei: gwei, prover_seconds: per_batch, ..CostModel::default() };
                let e = batch_economics(&sc.batches[0].kinds(), &FeeSchedule::default(), &cost);
                writeln!(out, r#"{{"kind":"economics","scenario":"S10","gas_gwei":{gwei},"cost_per_tx_usd":{:.6},"fee_usd":{:.6},"margin_pct":{:.1},"floor_active":{}}}"#, e.cost_per_tx_usd, e.avg_fee_usd, e.net_margin_pct, e.floor_active).unwrap();
                println!("S10  gazi {gwei:>5} gwei: kosto ${:.5}/tx, tarifa ${:.4}, marzhi {:.1}%{}", e.cost_per_tx_usd, e.avg_fee_usd, e.net_margin_pct, if e.floor_active { " (dysheme e kostos)" } else { "" });
            }
        }
    }
    if o.only.as_ref().map_or(true, |v| v.iter().any(|x| x == "S8")) {
        let n = 100_000;
        let (rate, refused) = invalid_flood(&w, n);
        writeln!(out, r#"{{"kind":"scenario","scenario":"S8","txs":{n},"refused":{refused},"refusals_per_s":{rate:.0}}}"#).unwrap();
        println!("S8   sulm me {n} tx të pavlefshme: {refused} u refuzuan, {rate:.0} tx/s");
    }
    println!("peak RAM {:.1} GB; detajet: {}", peak_rss_gb(), o.out);
    let _ = Fr::from(0u64);
}
