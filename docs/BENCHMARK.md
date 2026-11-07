# Benchmark: a jemi më të shpejtë se të tjerët? (5.11.2026)

Makina: cloud, 4 bërthama CPU, 15 GB RAM, pa GPU. Të gjitha matjet në të njëjtën makinë.

## B1. MULMOD 256-bit: korsitë RNS kundrejt metodës me limb-a

Brenda STARK-ut, `src/uint256.rs` e provon MULMOD-in me **byte-limb + bartje** në çdo korsi (shih komentin në krye
të skedarit): CRT-ja ndërmjet korsive nuk mund të përdoret, sepse korsitë jetojnë në fusha të ndryshme dhe asgjë nuk i
lidh. Pra metoda për korsi është ajo standarde e zkEVM-ve; avantazhi ynë është se **5 korsitë provohen paralelisht**,
plus truket e PDF-së të matura te `bench_pdf_strategy` (S1 verifikim 2.5×, S3 Barrett 1.5×, S4 batch inversion 6.1×,
S5 V-UMT 2.9×, S2 4.5× vonesë më e ulët me 5 kanale). Një krahasim "RNS kundrejt limb-ave" brenda STARK-ut do të
krahasonte metodën me veten, ndaj nuk e bëmë.

## B2. Motori: prover-i ynë kundrejt Plonky3

E njëjta punë: N permutacione Poseidon2-KoalaBear (gjerësi 16), një për rresht, blowup 4, 50 query, pa PoW.
- Ne: `cargo run --release --example bench_vs_plonky3 -- 16 2 50`
- Plonky3 0.9.0-rc.2: `cd bench/plonky3 && cargo run --release -- 16 2 50`

| 65 536 permutacione | Kolona | Prove | Verify |
|---|---|---|---|
| Plonky3, x^3 (S-box natyrale e KoalaBear) | 164 | 0.53 s | 3 ms |
| Plonky3, x^7, 1 regjistër (si ne) | 312 | 0.87 s | 3 ms |
| Ne, Blake3, 5 korsi (4 bosh) | 617 | 28.7 s | 92 ms |
| Ne, Poseidon2, vetëm korsia KoalaBear | 617 | 97 s | 83 s |

8 192 permutacione: Plonky3 0.07–0.12 s, ne 2.0–3.1 s.

**Sa më i ngadaltë është motori ynë, dhe pse (~33× në total):**
- ~5×: motori ynë provon gjithmonë 5 korsi; këtu 4 janë bosh. (Te MULMOD dhe te gjendja të 5 punojnë, aty kjo nuk humbet.)
- ~2×: motori ynë lejon vetëm kufizime të shkallës 2, ndaj na duhen 617 kolona aty ku Plonky3 përdor 312.
- ~3.3×: efikasiteti për qelizë (LDE, Merkle, FRI) — Plonky3 ka vite optimizimi (SIMD, Montgomery, layout i memories).
- Verifikimi në modalitetin Poseidon2 (83 s) është patologjik: llogarit hash-et Poseidon2 të listës publike një nga një.

## B3. Finaliteti në L1 (burime publike)

| Sistemi | Konfirmim i butë | Finaliteti në L1 |
|---|---|---|
| Base (OP Stack, Flashblocks) | ~200 ms | 7 ditë për tërheqje (optimistik) |
| Arbitrum | ~250 ms | 7 ditë për tërheqje (optimistik) |
| zkSync Era, Scroll, Linea | < 1–2 s | minuta deri në orë (batch + provë + vonesë ekzekutimi), sipas L2BEAT |
| SP1 Hypercube (Succinct) | — | provon blloqe Ethereum në kohë reale (< 12 s) me ~16 GPU |
| **Ne sot** | p50 ~150 µs në proces (verifikimi ECDSA) | ~2.5 min (projeksion, CPU) |
| **Ne, objektivi** | < 200 ms | 12–45 s |

Burime: L2BEAT (l2beat.com, "Tracking time to finality of L2 transactions"), docs.base.org (Flashblocks),
blog.succinct.xyz (SP1 Hypercube, "Real Time Proving with 16 GPUs").

## Përfundimi i ndershëm

- Konfirmimi i butë nuk është avantazh: të gjithë janë nën 1 s.
- Finaliteti i shpejtë është avantazhi i mundshëm, por **SP1 Hypercube e ka arritur tashmë** për blloqe të plota Ethereum.
- Motori ynë STARK është ~33× më i ngadaltë se Plonky3 në të njëjtën punë. Kjo është pengesa kryesore për shpejtësinë,
  më shumë se Groth16.
