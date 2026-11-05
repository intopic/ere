# SS-RAP v2: plani end-to-end i MVP-së

Burimi: `SS_RAP_v2_Arkitektura_dhe_Kodi_i_Verifikuar.pdf`, i lexuar i gjithi (faqet 1–16). PDF-ja është prototipi dhe
plani. Ne mund ta përmirësojmë dhe ta fortifikojmë, por **qëllimi dhe mënyra mbeten të njëjta**:

> **Inovacion në shpejtësi dhe në pagesë.** Prova ZK në 2.5–4 s në GPU, konfirmim në aplikacion < 200 ms dhe
> finalitet në Ethereum L1 brenda 12–45 s. Tarifat janë $0.006/tx për transferim dhe $0.025/tx për swap DeFi
> (mesatarisht $0.015/tx), rreth 35–50% më lirë se tregu, me kosto të brendshme rreth $0.0016/tx.

## 1. Mënyra (nuk ndryshon)

"Mos llogarit, verifiko", bashkë me kombinimin e algoritmeve:

1. **Dëshmitar kuotienti:** prover-i jep Q dhe R, qarku kontrollon vetëm A·B − Q·p − R = 0.
2. **RNS me 5 kanale 31-bit** (BabyBear, KoalaBear dhe tre të tjerë, M ≈ 2^154.3), pa zinxhirë bartjesh. Për EVM
   `uint256` përdoren limbs 64-bit (f.3).
3. **Limbs 8-bit + LogUp:** e njëjta R/Q në të 5 kanalet, pa rindërtim CRT.
4. **Barrett** në vend të `%`, në CPU dhe në GPU (`__umul64hi`).
5. **Montgomery batch inversion** në FRI dhe në emëruesit e LogUp.
6. **Fushë e zgjeruar F_m[u]/(u⁴−β_j)**, me invers përmes kullës kuadratike.
7. **V-UMT:** një pemë Merkle Blake3 për 5 kanalet.
8. **Groth16 mbi BN254:** rreth 240k gas, me hyrje publike të lidhur me state roots, V-UMT root, `blobhash` (EIP-4844),
   batch dhe chainid.

## 2. Rrjedha end-to-end që duhet të funksionojë

```
Transaksionet ─► Sequencer (soft-finality < 200 ms) ─► Batch 1000 tx ─► Gjurma (trace) EVM
   ─► Kufizimet RNS (Q,R + LogUp) ─► STARK: NTT/LDE + V-UMT + FRI ─► Wrapper Groth16 (BN254)
   ─► Blob EIP-4844 + verifyAndSettleBatchV2() në L1 ─► BatchSettledV2 (finalitet 12–45 s)
   ─► Moduli i pagesës: tarifa e arkëtuar kundrejt kostos (gas + GPU) për çdo batch
```

## 3. Ku jemi tani dhe çfarë mungon

| # | Komponenti | Gjendja tani (main) | Çfarë duhet për MVP |
|---|---|---|---|
| 1 | Aritmetika bazë (Barrett, F⁴, batch inverse) | ✅ e testuar, `POW256` i parallogaritur (S2: 4.5× vonesë) | — |
| 2 | Kufizimet RNS Q/R (64-bit + `uint256`) | ✅ `uint256::MulModRow`: 4 limbs 64-bit × 5 kanale, r < P, teste sulmi | ADDMOD dhe opkodet e tjera të EVM-së |
| 3 | LogUp | ✅ `logup.rs`: shumësi të angazhuara para α, α për çdo kanal, batch inversion | Lidhja me commitment-in e gjurmës (V-UMT) në STARK |
| 4 | Transcript Fiat-Shamir | ✅ `transcript.rs` (Blake3) | — |
| 5 | STARK: NTT, LDE, kompozimi | ⚠️ `ntt.rs`: NTT/LDE gati | Interpolimi i gjurmës, polinomi i kompozimit, lidhja me FRI |
| 6 | FRI | ✅ `fri.rs`: commit, query, V-UMT për shtresë, verifikues, teste sulmi | Më shumë query për ≥ 100 bit |
| 7 | GPU (CUDA) | ⚠️ kernel i palidhur | Host launcher, NTT batch, V-UMT Blake3 në GPU, benchmark RTX 4090 |
| 8 | Wrapper Groth16 | ❌ | Verifikuesi STARK si qark BN254 (gnark/SP1), trusted setup real |
| 9 | Kontrata L1 | ⚠️ kompilohet, VK demo e pasigurt | VK reale, teste Foundry (provë e vlefshme, e falsifikuar, sekuencë, blob), deploy në Sepolia |
| 10 | Sequencer / aggregator | ❌ | Shërbim minimal që mbledh tx, jep soft-confirm dhe dërgon blob + provë |
| 11 | Moduli i pagesës | ❌ | Tabela e tarifave (transferim/swap), kostoja reale për batch, marzhi |
| 12 | Benchmark dhe CI | ✅ CI jeshil, `bench_pdf_strategy` | Matje end-to-end: koha e provës, gas, finaliteti, $/tx |

## 4. Fazat (sipas planit 60-ditor të PDF-së, f.3 §2.4)

**Faza A, ditët 1–20: bërthama e saktë dhe e sigurt (CPU)**
- Rreshtat 1–6 të tabelës: `uint256` me 4×64-bit, LogUp real, Fiat-Shamir, NTT/LDE, FRI i plotë me verifikues.
- Prover-i STARK i plotë në CPU për një batch me shumëzime EVM.
- Testi: prova verifikohet dhe çdo dëshmitar i falsifikuar refuzohet.

**Faza B, ditët 21–40: shpejtësia (GPU)**
- Kernel CUDA + NTT + V-UMT në GPU (rreshti 7).
- Testi: matet koha e provës dhe krahasohet me objektivin 2.5–4 s.

**Faza C, ditët 41–60: settlement dhe pagesa**
- Wrapper Groth16, VK reale, kontratë në Sepolia, sequencer dhe moduli i pagesës (rreshtat 8–11).
- Testi: batch real 1000 tx → provë → L1, me matje të gas-it (objektivi ~240k), finalitetit (12–45 s) dhe $/tx
  (objektivi $0.015, kosto ~$0.0016).

## 5. Përkufizimi i "MVP gati"

1. Një batch transaksionesh shkon end-to-end në Sepolia dhe kontrata e pranon provën.
2. Një provë e falsifikuar refuzohet në çdo nivel (Rust, STARK, kontratë).
3. Raporti i matjeve (koha e provës, gas, finaliteti, $/tx) krahasohet me tabelën e PDF-së.
4. CI teston gjithçka në çdo push.

## 6. Shënime për fortifikimin (pa ndryshuar qëllimin)

- VK e kontratës duhet të vijë nga një trusted setup i vërtetë. VK-ja e tanishme (11·G1, 5·G2…) lejon falsifikime.
- Gabim i vogël në PDF: 714670540² mod KoalaBear = 43091733, jo 11. Përfundimi që 11 është QR mbetet i saktë.
- Moduli eksperimental `rns256.rs` (17 kanale) mbetet jashtë rrugës kryesore. Rruga kryesore ndjek PDF-në: 5 kanale + limbs 64-bit.
