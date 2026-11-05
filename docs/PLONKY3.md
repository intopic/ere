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
