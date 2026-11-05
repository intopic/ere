# Çfarë inovacioni sjell SS-RAP në tregun e Ethereum-it — versioni i verifikuar (v2.1)

Ky dokument ndan **atë që është matur dhe testuar** nga **ato që janë ende hipoteza**.
Të gjitha numrat më poshtë janë marrë me `cargo test` dhe `cargo run --release --example bench_rns256`
në një laptop Intel i5-7200U (2 bërthama, 2016) me ngarkesë në sfond. Në GPU numrat absolutë do jenë
të ndryshëm, por raportet ndërmjet metodave janë ato që kanë rëndësi.

---

## 1. Problemi që zgjidhim

Në një zkEVM (Scroll, Linea, ZKsync, Polygon…) pjesa më e shtrenjtë e provës është **aritmetika 256-bit e Ethereum-it**:
`MULMOD`, `ADDMOD`, dhe precompile-t `ecrecover` (secp256k1) e `ecAdd/ecMul/ecPairing` (BN254).
Proverët modernë punojnë në fusha të vogla 31-bit (BabyBear, KoalaBear) sepse janë shumë të shpejta në GPU,
por atëherë çdo shumëzim 256-bit duhet emuluar me ~16×16 copa (limbs) + zinxhir bartjesh (carries).
Bartjet janë **sekuenciale**: limb-i k pret limb-in k−1. Kjo e bën të vështirë paralelizimin.

## 2. Strategjia e PDF-së: "mos llogarit, verifiko"

PDF-ja (f.1–4) nuk e eliminon shumëzimin. Ajo heq **operacionet e shtrenjta rreth tij**, duke kombinuar disa algoritme:

| Nuk bëjmë | Në vend të saj | PDF |
| :--- | :--- | :--- |
| Llogaritje `r = a·b mod p` | **Verifikim**: prover-i jep `q, r` si dëshmitarë, qarku kontrollon vetëm `a·b = q·p + r` | f.1, f.3, f.8 |
| Zinxhir bartjesh | 5 kanale RNS 31-bit, çdo kanal i pavarur ("pa zinxhirë bartjesh") | f.1, f.3 |
| Pjesëtim `%` | Barrett me konstante μ (`__umul64hi` në GPU) | f.2, f.4, f.13 |
| N inversione | Montgomery batch: 1 invers + 3(N−1) shumëzime | f.2, f.6 |
| Rindërtim CRT | Kanalet lidhen me byte-limbs të përbashkëta + LogUp | f.1, f.4 |
| 5 commitment-e | V-UMT: 1 pemë Merkle për 5 kanalet | f.9 |

Në v2.1 e zgjerova idenë në 17 kanale për 256-bit (`src/rns256.rs`). Ky ishte vendimi im, jo i PDF-së: PDF-ja përdor
5 kanale mbi limbs 64-bit. Moduli mbetet si eksperiment, por matja kryesore tani ndjek strategjinë e PDF-së.

## 3. Çfarë matëm (fakte)

`cargo run --release --example bench_pdf_strategy` (n = 65 536, një thread, CPU x86-64 në cloud; GitHub Actions e
ekzekuton në çdo push). Raportet janë ato që kanë rëndësi, numrat absolutë ndryshojnë nga makina në makinë.

| # | Zëvendësimi | Rruga naive | Rruga e PDF-së | Rezultati |
| :--- | :--- | :--- | :--- | :--- |
| S1 | Verifiko në vend që të llogaritësh (64-bit mod Goldilocks) | 3.07 ns | 1.22 ns | **2.5× më shpejt** |
| S3 | Barrett në vend të `%` | 3.00 ns | 1.98 ns | **1.5× më shpejt** |
| S4 | Batch inversion (N = 65 536) | 89.6 ns/elem | 14.7 ns/elem | **6.1× më shpejt** |
| S5 | V-UMT kundrejt 5 pemëve | 655 355 hash, 40.3 ms | 131 071 hash, 14.0 ms | **5× më pak hash, 2.9× më shpejt, 5× më pak rrënjë/shtigje** |
| S2 | Kufizimet RNS pa bartje kundrejt zinxhirit me bartje (16-bit limbs) | thellësi 8, 85 ns/rresht | thellësi 1, 5 kanale të pavarura, 130 ns/kanal, 610 ns gjithsej | **Struktura: 8 → 1 thellësi, 0 kolona bartjesh. Në CPU: më i ngadaltë** |

**Përfundim i ndershëm:**
* Katër nga pesë zëvendësimet e PDF-së (S1, S3, S4, S5) janë **të matura dhe japin përfitim real** në CPU.
* S2, thelbi "pa bartje", e heq zinxhirin sekuencial (thellësia nga 8 në 1), që është ajo që nevojitet për
  paralelizëm në GPU. Por në CPU, me një thread, kontrolli RNS kushton më shumë se zinxhiri klasik, sepse `limb_tie`
  rillogarit fuqitë 256^k në çdo thirrje. Përfitimi i S2 mbetet **hipotezë deri në benchmark GPU**.
* Pretendimet "15×–100×", "2.5–4 s", "−55% thellësi gjurme" dhe "89% marzh" **nuk janë matur** ende. Ato kërkojnë
  një prover të plotë dhe GPU.
* Matja e mëparshme "1.36× më shumë punë" krahasonte numrin e shumëzimeve me 17 kanale. Kjo nuk mat strategjinë e
  PDF-së dhe u hoq.

## 4. Çfarë rregullova në kod (v2.0 → v2.1)

1. **Boshllëk sigurie i rëndë në `CarryFreeMulWitnessRow` (64-bit):** vetëm mbetja `r` ishte e lidhur me byte-limbs.
   Një prover mashtrues mund të zgjidhte `q` për çdo kanal dhe të "provonte" një rezultat të gabuar.
   Tani `a, b, q, r` janë të gjitha të lidhura. Testi `test_forged_remainder_is_rejected` e demonstron sulmin dhe bllokimin.
2. **`Extension4::mul` përdorte `%`** (pjesëtim u128) edhe pse dokumentacioni thoshte "zero %". Tani është pa pjesëtim.
3. **Moduli i ri `src/rns256.rs`:** shumëzim modular 256-bit për secp256k1 dhe BN254:
   * bazë deterministe me 17 numra të thjeshtë (përfshin 5 të v2.0), log2(M) = 525.5 > 514 bit të nevojshme;
   * kufizimi `s + r + 1 = P` që garanton `r < P` (pa të, një prover mund të jepte `r + P` si rezultat);
   * dy teste sulmi (rezultat i falsifikuar, rezultat jo-kanonik) që refuzohen;
   * strukturë SoA (kolonë për çdo kanal) gati për kernel GPU;
   * aritmetikë pa degëzime (branchless).
4. **Benchmark i drejtë:** `examples/bench_rns256.rs`.

## 5. Probleme të hapura (para se të flasim me investitorë ose të vendosim në mainnet)

1. **Kontrata Solidity nuk është e sigurt.** Çelësi verifikues përdor shumëfisha të njohur të gjeneratorit
   (11·G1, 5·G2, 7·G2, 13·G2…). Kushdo që i di këta numra mund të falsifikojë një provë Groth16.
   Duhet një ceremoni e vërtetë (trusted setup) mbi qarkun real.
2. **Lidhja ndërmjet fushave (cross-field binding) nuk është vërtetuar formalisht.** 17 STARK-e në 17 fusha
   të ndryshme duhet të provojnë se po përdorin të njëjtat byte-limbs. Ideja (pema e përbashkët Merkle V-UMT +
   pyetje të përbashkëta FRI) është e arsyeshme, por duhet një provë sigurie me shkrim.
3. **Nuk kemi ende një prover të plotë.** Kemi kufizimet (AIR), FRI-folding dhe Merkle; mungon AIR-i për
   instruksionet e EVM-it, kompozimi i kufizimeve, pyetjet FRI dhe mbështjellja Groth16.
4. **`verify_logup_byte_range_channel`** llogarit të dyja anët nga të njëjtat të dhëna, ndaj është kontroll
   konsistence, jo provë. Në prover-in e vërtetë, shumëfishimet duhet të angazhohen (commit) para sfidës alpha.
5. **Kerneli CUDA** është vetëm dekompozim 64-bit/5 kanale; duhet zgjeruar në 17 kanale dhe testuar në GPU (këtu nuk ka `nvcc`).

## 6. Hapat e ardhshëm (sipas rëndësisë)

1. Kerneli CUDA 17-kanalësh për `MulModBatch` + benchmark në GPU të vërtetë (H100/4090).
2. Zinxhir operacionesh në RNS (p.sh. një shumëzim i plotë pike në secp256k1 = `ecrecover`) për të matur
   sa zbret kostoja kur mbetjet nuk dekompozohen pas çdo hapi.
3. Shkrim formal i argumentit të sigurisë për lidhjen ndërmjet fushave.
4. Trusted setup i vërtetë dhe kontratë verifikuese e gjeneruar nga qarku.
