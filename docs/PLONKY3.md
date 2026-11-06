# Kalimi te Plonky3 (dega `plonky3`)

Vendimi (5.11.2026): motori STARK zëvendësohet me Plonky3 0.9.0-rc.2. Ekuacionet (AIR-et), korsitë RNS dhe metoda
e PDF-së mbeten të njëjta. Bashkohet në `main` vetëm kur e gjithë rruga (gjendja + R8) është më e shpejtë.

## P1–P2: MULMOD 256-bit në 5 korsi

- `p3/src/mulmod.rs`: i njëjti AIR si `src/uint256.rs` (byte-limb, bartje, "verifiko, mos llogarit").
  Çdo byte shkon në bus-in global "byte" drejt `ByteTableAir` (256 rreshta, tabelë e parallogaritur).
  Lookup-et lokale në një grup të vetëm ishin 20× më të ngadalta: kostoja e p3-lookup rritet më shpejt se lineare
  me numrin e tuple-ve në një ndërveprim.
- `p3/src/fields.rs`: 3 primet RNS që Plonky3 nuk i ka (2113929217, 1811939329, 1711276033) si fusha Monty-31,
  me zgjerim x^4 − W (W = `EXTENSION_BETA`). Konstantet gjenerohen nga `scripts/gen_lane_fields.py`, i cili i
  verifikon edhe kundrejt konstanteve të BabyBear në Plonky3. Testi `lane_fields_are_the_rns_moduli` kontrollon
  gjeneratorin, rrënjët 2-adike, Frobenius-in dhe zgjerimin 2-adik për të 5 fushat.
- Merkle dhe transcript: Keccak (P4 i kalon në Poseidon2 mbi BN254 për qarkun R8).

## Matjet (4 bërthama me AVX-512, `RUSTFLAGS="-C target-cpu=native"`, 5 korsi njëra pas tjetrës)

| MULMOD secp256k1 | Plonky3 | Motori ynë | Raporti |
|---|---|---|---|
| 20 480 op, blowup 2 × 100 query (P3) / blowup 4 × 50 query (ne) | 0.33 s | 3.39 s | **~10×** |
| 20 480 op, blowup 4 × 50 query për të dy | 0.47 s | 3.39 s | ~7× |
| 81 920 op, blowup 2 × 100 / 4 × 50 | 1.23 s | 14.2 s | **~11.6×** |

Pa `target-cpu=native` (pa AVX-512) Plonky3 është ~3–4× më i ngadaltë se këto shifra; motori ynë nuk ndryshon.
Motori ynë kërkon blowup ≥ 4 (kufizime vetëm të shkallës 2); Plonky3 lejon blowup 2 me më shumë query, i njëjti
nivel sigurie i supozuar (~100 bit).

Komanda:
```
CARGO_TARGET_DIR=target-native RUSTFLAGS="-C target-cpu=native" cargo run --release -p ss_rap_p3 --example bench_p3_mulmod -- 12 1 100 3
CARGO_TARGET_DIR=target-native RUSTFLAGS="-C target-cpu=native" cargo run --release --example bench_stark_mulmod -- 12
```

## P3: AIR-i i gjendjes (transferet) në 5 korsi

- `p3/src/state.rs`: të njëjtat kolona dhe kufizime si `src/state.rs`. Bus-et bëhen bus-e me emër në Plonky3:
  "mem" (kontrolli i memories), "tx" (transaksionet), "byte" (range-check).
- Ana publike (tabela fillestare, tabela finale, transaksionet e korsisë) është `PublicAir`: tuple-t e saj janë
  **kolona periodike** të ndërtuara nga deklarata. Plonky3 i lidh në transcript dhe verifikuesi i vlerëson vetë,
  pra prover-i nuk mund t'i ndryshojë. Kontrolli i Plonky3 "të gjitha bus-et mblidhen në zero" jep atëherë
  init + writes = reads + final dhe "çdo transaksion publik ekzekutohet një herë, në indeksin e vet".
- Teste: prova e ndershme kalon; tabelë finale tjetër, tabelë fillestare tjetër, shumë tjetër, renditje tjetër,
  transaksion i hequr, dhe batch me tejkalim balance refuzohen.

| Transferet (100 llogari) | Plonky3 (Keccak), blowup 2 × 100 | Ne, Blake3, blowup 4 × 50 | Ne, Poseidon-BN254 |
|---|---|---|---|
| 1 000 | 56 ms | 86 ms | 812 ms |
| 20 000 | 250 ms | 1.16 s | 12.3 s |

`CARGO_TARGET_DIR=target-native RUSTFLAGS="-C target-cpu=native" cargo run --release -p ss_rap_p3 --example bench_p3_state -- 20000 1 100`

## P4 (në punë): Poseidon2 mbi BN254 për qarkun R8

`p3/src/bn254.rs`: Merkle dhe transcript me Poseidon2-BN254 (t = 3, x^5, 8 + 56 raunde; vlerat e korsisë paketohen
disa në një element BN254, si në SP1). Konstantet e raundeve janë tonat (blake3, të rigjenerueshme nga qarku);
prodhimi duhet të kalojë te konstantet e referencës (zkhash RC3).

| Transferet | Plonky3 Poseidon2-BN254, blowup 2 × 100 | Ne, Poseidon-BN254, blowup 4 × 50 |
|---|---|---|
| 1 000 | 0.27 s | 0.78 s |
| 20 000 | 3.3 s | 12.1 s |

## Unifikimi i korsive në BabyBear

Të 5 korsitë tani provohen mbi BabyBear (`p3/src/state.rs`: `StateProof { lanes: [..; 5] }`).
U hoqën KoalaBear, Lane3–Lane5, `p3/src/fields.rs` dhe `scripts/gen_lane_fields.py`.
Korsitë mbeten 5 prova të pavarura (secila me pjesën e vet të transfertave), testet e falsifikimit
kalojnë për çdo korsi.

Matje (native, AVX-512), pa ndryshim të dukshëm shpejtësie kundrejt fushave të ndryshme:

| | Prove |
|---|---|
| MULMOD 20,480 (5 × 4096), blowup 2 × 100 | 0.37 s |
| Gjendja 20,000 transferta, Keccak | 0.21 s |
| Gjendja 20,000 transferta, Poseidon2-BN254 | 4.0 s |

Shënim për qarkun Groth16: kostoja në qark varet kryesisht nga numri i provave dhe i query-ve
(hash Poseidon2-BN254 i shtigjeve Merkle), jo nga sa fusha përdoren. Fitimi i unifikimit është
një gadget i vetëm aritmetike BabyBear (më pak kod, më pak rrezik), jo 3–5× më pak kufizime vetë.
Ulja reale vjen nga bashkimi i 5 korsive në një provë të vetme (një trace më i gjatë ose një
batch) dhe nga më pak query (p.sh. blowup 16 × 25), gjë që po e bëj te P4b.

## P4b hapi 1: të 5 korsitë në NJË provë

`keccak::prove_one` / `poseidon2_bn254::prove_one` (`p3/src/state.rs`) provojnë të 5 korsitë në
një batch proof të vetëm (11 AIR: 5 gjendje, 1 tabelë bajtesh e përbashkët, 5 publike). Tuplet
"mem" dhe "tx" fillojnë me numrin e korsisë, kështu që rreshtat e një korsie nuk anulojnë ata të
një tjetre (testi: tx e zhvendosur në korsi tjetër refuzohet). Qarku Groth16 tani verifikon 1 FRI
në vend të 5.

20,000 transferta, native (Poseidon2-BN254, të gjitha ~100 bit):

| FRI | Prove (5 prova) | Prove (1 provë) | Verify (1 provë) |
|---|---|---|---|
| blowup 2 × 100 | 4.5 s | 2.7 s | 0.22 s |
| blowup 4 × 50 | | 5.2 s | 0.16 s |
| blowup 8 × 34 | | 10.1 s | 0.14 s |
| blowup 16 × 25 | | 20.3 s | 0.14 s |

Me Keccak, 1 provë, blowup 2 × 100: 0.16 s (kundrejt 0.23 s me 5 prova).
Query-të më të pakta e ulin qarkun afërsisht në proporcion (100 → 25 = ~4×), por e rrisin kohën e
provimit; zgjedhja përfundimtare bëhet pasi të matim qarkun.

## P4b hapi 2: verifikuesi i provës Plonky3 brenda Groth16

Qarku i settlement-it mbi Plonky3 (`settlement/src/wrapper/p3settle.rs`) ka të njëjtin input publik
si kontrata, `x = keccak256(oldRoot, newRoot, vUmtRoot, blobhash, batchNumber, chainId) mod r`,
dhe provon që:

- rrënjët e vjetra/të reja janë ato të një deklarate të mirëformuar (`StatementVar`, deklarata si dëshmi);
- `v_umt_root = Poseidon(digest, main, permutation, quotient, commit-et e FRI)` i provës Plonky3;
- prova Plonky3 me 5 korsi (`record::prove_one`, Merkle dhe transcript Poseidon2-BN254) verifikohet
  në R1CS (`p3batch_var::verify_batch_var`): transcript-i (`challenger_var`), FRI/PCS (`p3fri_var`),
  kufizimet AIR + LogUp në zeta nga listat simbolike të p3 (`p3air_eval`), shuma e terminaleve = 0.

Pjesët, të testuara secila kundrejt provave reale të Plonky3, me teste negative:

| Moduli | Çfarë bën |
|---|---|
| `poseidon2_var` | Poseidon2-BN254 (t = 3), sponge MultiField32, Merkle me lartësi të përziera |
| `challenger_var` | `MultiField32Challenger`: observe/sample/sample_bits, ndarja kanonike në bazën p |
| `p3fri_var` | `TwoAdicFriPcs`: hapjet e reduktuara, palosja arity 2, Merkle, proof-of-work i query-ve |
| `p3air_eval` | kufizimet në zeta nga `get_symbolic_constraints` (bazë + ext), selektorët, kolonat periodike |
| `p3batch_var` | verifikuesi i plotë `verify_batch` për 11 instancat (5 gjendje, bajtet, 5 publike) |
| `p3settle` | deklarata + verifikuesi + `v_umt_root` + header keccak |

**Lidhja e deklaratës me Fiat-Shamir (rregullim sigurie).** `p3-batch-stark` 0.9.0-rc.2 NUK i fut
kolonat periodike (as `periodic_statement`) në transcript. Pa ndryshim, një provues mund të
angazhonte një trace publik me tuple të sajuara, të mësonte zeta dhe vetëm pastaj të zgjidhte
deklaratën që kalon kontrollin e vetëm në zeta. Tani AIR-i publik i korsisë 0 deklaron si vlera
publike digest-in e deklaratës (9 limbs × 30 bit); Plonky3 i vëzhgon menjëherë pas commit-it main,
para çdo sfide, dhe verifikuesi (natív dhe në qark) i rillogarit nga deklarata.

**Kufizimet** (600 transferta, 5 korsi × 2^8 rreshta, blowup 2 × 20 query): 5.57M → 3.88M pas
optimizimeve (hapjet e reduktuara grupohen sipas (lartësi, pikë): 1.71M → 0.32M; twiddle-t e
palosjes rrjedhin nga njëri-tjetri në vend të fuqizimit për çdo raund: 0.25M → 0.12M; inverset e
kolonave periodike ndahen mes korsive). Ndarja (`P3_STAGES=1`):

| Pjesa | Kufizime |
|---|---|
| alokimi i dëshmive (vlerat e hapura, rreshtat e query-ve) | 1.14M |
| transcript-i i PCS + shumat në z | 0.71M |
| hapjet Merkle të input-eve | 0.60M |
| hapjet e reduktuara | 0.32M |
| Merkle i fazës commit | 0.26M |
| palosja | 0.12M |
| kufizimet në zeta | 0.72M |

**Groth16 i vërtetë** (`cargo run --release -p ss_rap_settlement --example export_p3_fixture`,
40 transferta, 5 × 2^5 rreshta, blowup 2 × 4 query + 8 bit grinding, 4 bërthama):
2.40M kufizime, setup 49 s, prove 38 s, verify 2.7 ms, kujtesa maksimale ~8 GB. Shkruan
`contracts/P3WrapperVerifier.sol` dhe `test/P3SettlementFixture.sol`; `test/P3Settlement.t.sol`
e settle-on përmes `SSRapSettlementVerifierV2.verifyAndSettleBatchV2` dhe refuzon një rrënjë tjetër,
një `v_umt_root` tjetër dhe pika të ndërruara. CI e rigjeneron dhe dështon nëse ndryshon.
Çelësi vjen nga `groth16::p3_dev_setup` me farë publike: VETËM për zhvillim, prodhimi kërkon ceremoni.
