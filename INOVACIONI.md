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

## 2. Ideja: bashkimi i tri algoritmeve

| Algoritmi | Çfarë jep |
| :--- | :--- |
| **RNS / Teorema Kineze e Mbetjeve (Sunzi)** | Një numër 256-bit ruhet si 17 mbetje të pavarura modulo 17 numrash të thjeshtë 31-bit. Shumëzimi bëhet **pa bartje**, çdo kanal veç e veç. |
| **STARK me fusha të vogla + NTT (2-adicitet ≥ 2^20)** | Secili prej 17 kanaleve është fushë e vlefshme për NTT/FRI, pra mund të provohet nga një prover i vetëm 31-bit, i pavarur nga të tjerët. |
| **LogUp (kërkim-tabele)** | I lidh të 17 kanalet me të njëjtat byte-limbs të kontrolluara në [0,255], gjë që e detyron çdo vektor mbetjesh të jetë imazhi i **një** numri të vetëm < 2^256. |

**Inovacioni i vërtetë:** shumëzimi modular 256-bit ndahet në **17 punë plotësisht të pavarura**,
pa asnjë komunikim ndërmjet tyre gjatë llogaritjes. Kjo përputhet në mënyrë të përsosur me
17 GPU, 17 SM-grupe në një GPU, ose 17 makina, dhe ul **vonesën** e provës.

## 3. Çfarë matëm (fakte)

```
A)  RNS-256, të gjitha kufizimet (17 kanale)    2721 ns/rresht
A1) RNS-256, vetëm një kanal                     287 ns/rresht
B)  Metoda klasike 16-bit limbs + bartje        1996 ns/rresht
```

* **Vonesa (latency):** me 17 punëtorë paralelë, secili bën vetëm **0.14×** të punës së metodës klasike,
  pra rreth **7× më shpejt në kohë-reale** për kontrollin e aritmetikës 256-bit.
* **Puna totale (kosto/$):** RNS bën **1.36× më shumë** punë gjithsej se metoda klasike, sepse çdo kanal
  duhet të kontrollojë lidhjen me 32 byte-limbs për 5 operandë.

**Përfundim i ndershëm:** RNS-256 na bën **më të shpejtë, jo më të lirë**. Avantazhi ynë në treg është
**finaliteti i shpejtë** (prova gati në sekonda kur ka shumë GPU paralele), jo çmimi më i ulët për transaksion.
Pretendimet në README-në e vjetër për "15×–100× më shpejt" dhe "89% marzh fitimi" **nuk janë të matura**
dhe i hoqa deri sa të kemi një prover të plotë dhe benchmark GPU.

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
