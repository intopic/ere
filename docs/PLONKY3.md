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
