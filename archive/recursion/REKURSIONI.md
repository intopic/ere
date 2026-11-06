# Wrapper-i STARK → Groth16 me rekursion (plani)

Vendimi: rekursion që në fillim, që prova në L1 të jetë e sigurt pa humbur objektivin e shpejtësisë.

## Pse rekursion

Matja (`cargo run --release -p ss_rap_settlement --example wrapper_cost`): një qark BN254 që verifikon direkt
STARK-un e gjendjes (1000 tx) ka ~8 milion kufizime edhe pas paketimit, algjebrës dembele dhe blowup 64.
Groth16 në këtë makinë kushton ~24 µs për kufizim, pra rreth 3 minuta. Pjesa më e madhe vjen nga vlerat e
hapura (5 korsi × ~275 vlera × 4 hapje × çdo query) dhe nga hash-et e Merkle.

Rekursioni e zvogëlon atë që duhet të kontrollojë qarku final:

```text
1. STARK-u i gjendjes      5 korsi, Blake3, i shpejtë (~70 ms për 1000 tx)
2. STARK-u rekursiv        provon "verifikuesi i (1) pranoi"; hash-i i (1) zëvendësohet me një hash
                           që kushton pak në AIR mbi fusha 31-bit
3. STARK-u final           i vogël, me Poseidon mbi BN254 (gati: HashMode::Poseidon), pak query, blowup i madh
4. Qarku BN254 + Groth16   verifikon vetëm (3): synimi < 1 milion kufizime
5. Kontrata L1             e njëjta ndërfaqe: një hyrje publike, i njëjti kontroll pairing
```

## Vendim: pemë për korsi në rrugën e rekursionit

Në rrugën e rekursionit çdo korsi ka pemët, transcript-in dhe hash-in e vet: Poseidon2 mbi fushën e korsisë
(S-box x^7 për BabyBear, x^3 për KoalaBear, x^5 për tre të tjerat). Kështu çdo korsi verifikohet tërësisht
brenda fushës së vet, pa asnjë lidhje ndër-fusha. V-UMT mbetet në rrugën e shpejtë native (Blake3).

## Problemi kryesor dhe zgjidhja (versioni i parë, i zëvendësuar nga vendimi më sipër)

Verifikuesi i (1) bën aritmetikë në 5 fusha të ndryshme (një për korsi). Një AIR mbi fushën F_j e bën
aritmetikën e F_j direkt, por jo atë të fushave të tjera. Prandaj:

- Korsia rekursive j verifikon kontrollet algjebrike të korsisë j të provës (1) (kompozimi, FRI), direkt në F_j.
- Hash-et (Merkle, Fiat-Shamir) janë të përbashkëta. I bën një korsi e vetme (KoalaBear, 2^24 rrënjë),
  me Poseidon2 mbi atë fushë.
- Sfidat dhe rrënjët që përdorin të gjitha korsitë bëhen hyrje publike të provës rekursive. Qarku final
  (BN254) kontrollon që të jenë të njëjtat në çdo korsi. Kështu shmanget lidhja ndër-fushë brenda STARK-ut.

## Hapat (secili me teste sulmi para se të vazhdojmë)

| # | Hapi | Gjendja |
|---|---|---|
| R0 | Gadget-e BN254 për 5 fushat + F⁴, modeli i kostos | ✅ `settlement/src/wrapper` |
| R1 | Poseidon mbi BN254 për commitment dhe Fiat-Shamir (shtresa 3) | ✅ `src/hash.rs` |
| R2 | Poseidon2 mbi KoalaBear: native (`src/poseidon2.rs`, 1.15 µs/permutim, M_I me polinom karakteristik të pareduktueshëm) + AIR (`src/poseidon2_air.rs`, një permutim për rresht, teste falsifikimi) | ✅ |
| R3 | Hyrje publike në motorin STARK: deklarata absorbohet në transcript, vlerat publike hyjnë si shuma bus-i që i llogarit verifikuesi; kufiri i rreshtit të parë me `Point::first_row` | ✅ `src/stark.rs` |
| R4 | AIR i verifikimit të Merkle-s me Poseidon2: një nivel për rresht, nivelet lidhen me bus (fëmijë → prind), pretendimet (gjethe, indeks, rrënjë) publike; teste sulmi | ✅ `src/merkle_air.rs` |
| R5 | Fiat-Shamir me Poseidon2: `HashMode::Poseidon2` për STARK-un e jashtëm (✅ prova e gjendjes 1000 tx në ~160 ms, kundrejt ~70 ms me Blake3 dhe ~950 ms me Poseidon BN254) + AIR i sponge-it (`src/sponge_air.rs`: një permutim për rresht, zinxhir kapaciteti me bus, blloqet dhe daljet publike; refuzon sfida ose mesazhe të falsifikuara) | ✅ |
| R6.1 | Motori në mënyrën për korsi: `HashMode::Lane(j)`, transcript-i Poseidon2 mbi F_{m_j}, pemët dhe FRI vetëm me vlerat e korsisë j; `prove_air_lanes`/`verify_air_lanes` (5 prova të pavarura, paralele). Teste: prova e një korsie nuk pranohet si korsi tjetër, ndërrimi i provave dhe vlerat e futura në korsi të huaj refuzohen, falsifikimi në korsinë 3 rrëzon vetëm korsinë 3 | ✅ `src/stark.rs`, `src/fri.rs` |
| R6.2a | AIR i palosjes FRI për korsi (`src/fri_air.rs`): një rresht për (query, shtresë), fold = (f0+f1)/2 + α(f0−f1)/(2x) në F_{m_j}, zinxhiri i pikave x_{l+1} = (−1)^{b_l} x_l² nga x_0 = s·ω^i, biti zgjedh vendin në çiftin e shtresës tjetër, shtresa e fundit = konstantja publike. Teste: në të 5 korsitë; refuzohen vlera e falsifikuar, α/indeksi/konstantja e gabuar, zinxhiri i prerë, biti i ndërruar, prova FRI mashtruese | ✅ |
| R6.2b | AIR i kompozimit për korsi (`src/composition_air.rs`), i përgjithshëm për çdo AIR me bus linear (`Air::bus_tuples`): një rresht për (query, x / −x), kontrollon C(x) = Q(x)·(x^N − 1) me `eval`-in e vetë AIR-it të brendshëm, LogUp-in e bajteve, inverset e bus-eve dhe hapin e shumës, plus kombinimin FRI f(x). Për AIR-in e gjendjes: 1698 kolona, 1329 kufizime, ~0.56 s provë+verifikim. Teste: në të 5 korsitë; refuzohen vlera e hapur, Q, shuma vijuese, f, α, S/N dhe pozicioni i falsifikuar | ✅ |
| R7.1 | Motori me shumë tabela (`src/multi_air.rs`): AIR-et vendosen krah për krah në një provë, kufizimet bashkohen, të gjitha bus-et në një shumë LogUp. Një tuple që e dërgon një tabelë dhe e merr tjetra anulohet, pra nuk duhet të jetë publike. Teste: lidhja verifikohet në të 5 korsitë pa tuple publike; një tuple që tabela tjetër nuk e dërgon refuzohet | ✅ |
| R7.2a | AIR-et e Merkle-s dhe të sponge-it punojnë në fushën e çdo korsie (`lane`); lidhja e parë në `src/recursion.rs`: vlerat e shtresës 0 që paloson FRI janë f(x) që AIR-i i kompozimit rillogariti nga vlerat e hapura (bus `LINK_LAYER0`). Test: një çift i falsifikuar që e ruan palosjen kalon te tabela FRI e vetme, por refuzohet kur tabelat lidhen | ✅ |
| R7.2b | Hash-i i gjetheve (`src/leaf_air.rs`): një permutim për rresht, zinxhir me bus, copat e gjethes vijnë nga AIR-i i kompozimit dhe digest-i shkon te AIR-i i Merkle-s si niveli 0. Në stack (`recursion.rs`) çdo vlerë e hapur (main, aux, quotient, në x dhe në rreshtin tjetër) hash-ohet dhe autentikohet kundrejt rrënjës; publike mbeten vetëm rrënjët dhe pozicionet. Teste: vlera e hapur e ndryshuar, gjethe jashtë pemës, aux i rreshtit tjetër, rrënjë e gabuar refuzohen. Matja e parë: 4 query të brendshme, stack 2^10 rreshta × 3204 kolona, ~13 s për korsi (tabela e kompozimit mbushet deri në lartësinë e përbashkët; tabelat me lartësi të ndryshme janë optimizimi i radhës) | ✅ |
| R7.2c | Pemët e shtresave FRI: çdo çift që paloson FRI hash-ohet si gjethe dhe autentikohet kundrejt rrënjës së shtresës. Test: një zinxhir i falsifikuar që i bindet palosjes deri te konstantja finale (që tabela FRI e vetme e pranon) refuzohet nga stack-u | ✅ |
| R7.2d | Transcript-i brenda stack-ut (`src/transcript_air.rs`, `src/link_air.rs`): çdo fjalë e bllokut absorbohet si tuple (k, p, fjala); rrënjët ku mbarojnë shtigjet e Merkle-s dhe shtresa finale e FRI shkruhen në blloqe nga tabelat e lidhjes; α, β, ρ, γ, δ dhe α-të e FRI lexohen nga daljet e permutimeve. Në mënyrën për korsi shtresa finale absorbohet si fjalë fushe dhe indeksi i query-t merr bitet e ulëta të një fjale. Teste: α e kompozimit ose e FRI jo nga transcript-i, fjalë publike e ndryshuar, rrënjë e absorbuar ≠ rrënja e pemës, shtresa finale e zhvendosur, etiketë tjetër, të gjitha refuzohen. Publike mbeten ende indekset e query-ve dhe S/N | ✅ |
| R7.2e | Indekset e query-ve (`src/index_air.rs`): fjala e transcript-it zbërthehet në 31 bite në mënyrë kanonike (w < m, ndryshe w + m do të zhvendoste indeksin), dhe prej saj dalin bitet e palosjes, x0 = s·ω^i dhe pozicioni i çdo gjetheje (i, i + n/2, rreshti tjetër, i mod n_l/2 për FRI). Teste: fjalë indeksi jo nga transcript-i, indekse të ndërruara mes query-ve, FRI në indeks tjetër, zbërthim jo kanonik, të gjitha refuzohen | ✅ |
| R7.2f | Shuma publike S/N brenda stack-ut (`src/public_sum_air.rs`): një rresht për çdo tuple publik të provës së brendshme (gjendja fillestare, finale, transaksionet), gjurmë e shenjës me Horner nën β, ρ të brendshëm (që vijnë nga transcript-i), inversi dhe shuma vrapuese; rreshti i fundit ia jep S/N rreshtave të kompozimit. Kështu β, ρ dhe S/N nuk janë publike | ✅ |
| R7.3 | Prova rekursive e një korsie me vetëm deklaratën publike: `strip_private()` fshin sfidat, vlerat e hapura, pozicionet, rrënjët dhe vlerat FRI, dhe prova e jashtme verifikohet vetëm me deklaratën e brendshme + formën. Orari i transcript-it (pozicionet e sfidave, rrënjëve, indekseve) varet vetëm nga forma: dy deklarata të ndryshme me të njëjtën formë japin të njëjtin orar. Teste: gjendje finale/transaksion/peshë tjetër, tuple i hequr, lexues shtesë, β nga permutacion tjetër, deklaratë e brendshme tjetër, të gjitha refuzohen | ✅ |
| R7 | STARK-u rekursiv: lidhja e AIR-eve (Merkle ↔ hapjet, sponge ↔ sfidat, kompozimi ↔ FRI) me bus, (1) → (2), test me prova të falsifikuara | ⏳ |
| R8 | Vendim (5.11): qarku verifikon **direkt** provën e gjendjes (~8 M kufizime e projektuar) sepse prova rekursive kushton 113–228 M në qark (`wrapper_cost`); R7 mbetet për agregim/kompresim më vonë | ⏳ |
| R8.1 | Gadget-et BN254 (`settlement/src/wrapper/hash_var.rs`): transcript Poseidon, hash i gjetheve (vlera 31-bit, 8 për element), shtigje Merkle; identike me native, refuzojnë vlerë/pozicion/rrënjë të falsifikuar | ✅ |
| R8.2 | FRI në qark (`fri_var.rs`) për 5 korsitë: palosje pa inversion 2x·next = x(f0+f1) + α(f0−f1), x_{l+1} = ±x_l², shtresa finale kanonike; refuzon çift, shtresë finale, shteg të falsifikuar | ✅ |
| R8.3 | Verifikuesi i plotë STARK në qark (`stark_var.rs`) për AIR-in e gjendjes: transcript, 4 hapje × 3 pemë, kompozimi C = Q·(x^N−1) dhe kombinimi FRI në x, −x për çdo korsi, shuma publike S/N nga tuple-t publike. Prova e ndershme kalon; vlerë e hapur, kuocient, deklaratë tjetër refuzohen. Matja (1000 tx, blowup 64): ~1.56 M fikse + ~0.49 M për query → ~9.4 M me 16 query | ✅ |
| R8.4 | Qarku i shlyerjes (`settle_circuit.rs`): deklarata (adresa të renditura, rrënjët e vjetra/reja si zinxhir Poseidon, digest), verifikuesi STARK, v_umt_root = Poseidon(digest, rrënjët e provës), dhe keccak256 i header-it në qark (308 K kufizime) i barabartë me inputin e vetëm publik. Kontrata nuk ndryshon. Pipeline-i kalon në transcript Poseidon me label konstant (`SS-RAP/v2/settle`) dhe `Wrapper::Stark` | ✅ |
| R8.4c | Groth16 real me STARK-un brenda: formë e vogël (6 llogari, 12 tx, 2 query) → 1.38 M kufizime, setup ~35–40 s, prove ~18–22 s, verify 2.5 ms në 4 bërthama. `export_stark_fixture` gjeneron `contracts/StarkWrapperVerifier.sol` + fixture; testi Foundry `test/StarkSettlement.t.sol` shlyen batch-in me këtë verifikues dhe refuzon rrënjë/v_umt/provë tjetër | ✅ |

## Ndershmëria

Qarku i shlyerjes (R8.4) e verifikon STARK-un brenda SNARK-ut, por vetëm për **një formë fikse**
(numri i llogarive, transaksionet për korsi, parametrat STARK): çelësi Groth16 lidhet me formën.
Batch-et e madhësive të ndryshme kërkojnë mbushje (padding) deri në një formë standarde, kjo është R8.5.
Deri atëherë fixture-i 1000 tx përdor ende qarkun DEV (`Groth16Verifier.sol`), dhe STARK-u i tij verifikohet
nga aggregator-i. Mangësi të tjera të hapura:
- blobhash është fushë e lirë në header: lidhja e përmbajtjes së blob-it me transaksionet e provuara (KZG) mbetet.
- Fixture-i CI përdor 2 query FRI (i pasigurt); prodhimi kërkon ~100 bit siguri (p.sh. blowup 16 × 25 query).
- Setup-i me farë publike nuk është i sigurt; prodhimi kërkon ceremoni shumë-palëshe.
- Madhësia e plotë (1000 tx, 100 llogari, ~10–11 M kufizime) kërkon ~4 GB+ çelës dhe ~4 min prove në CPU: makina GPU në fund.

## Matja me madhësi reale (`cargo run --release --example bench_recursion -- 50 2`)

Prova e brendshme: 1000 tx, 2^8 rreshta për korsi, blowup 4, 50 query, një korsi (Poseidon2 i korsisë), 4 bërthama CPU.

| Hapi | Koha |
|---|---|
| Prova e brendshme e një korsie | ~0.62 s (484 KiB) |
| Riluajtja + dëshmitari | ~0.11 s |
| Prova e jashtme (stack 2^14 × 4013) | ~100 s (1.3 MiB) |
| Verifikimi i jashtëm | ~0.22 s |

| Tabela | Rreshta | Kolona |
|---|---|---|
| composition | 100 | 1902 |
| fri fold | 400 | 37 |
| leaf hash | 8000 | 629 |
| merkle | 8200 | 637 |
| transcript | 43 | 624 |
| pid roots | 1000 | 12 |
| index | 50 | 52 |
| public sum | 656 | 88 |

Qelizat e përdorura janë 10.6 M, të mbushura 65.7 M (6.2×): lartësia e përbashkët është humbja kryesore. Nga qelizat
e përdorura, 97% janë hash-et (gjethet e hapura dhe shtigjet Merkle).

### Pas optimizimeve (R7.4)

| Hapi | Para | Pas |
|---|---|---|
| Poseidon2 (një permutim) | 3.2–4.9 µs | 1.2–2.2 µs (modul konstant për çdo fushë, e njëjta dalje) |
| LDE, kuocienti, kombinimi FRI brenda korsisë | sekuencial | paralel në të gjitha bërthamat |
| Tabelat | një lartësi (2^14 × 4013, 65.7 M qeliza) | 5 grupe me lartësinë e vet mbi një bus (16.4 M qeliza) |
| Prova e jashtme e një korsie, 1000 tx, 50 query | ~100 s | **~7.2 s** (4 bërthama CPU), verifikimi ~0.12 s |

Grupet: 2^8 × 2610 (composition, transcript, tree roots, final, index), 2^9 × 37 (fri fold), 2^10 × 100
(pid roots, public sum), 2^13 × 629 (leaf hash), 2^14 × 637 (merkle).

Prova me shumë tabela (`stark::prove_multi` / `verify_multi`): çdo tabelë angazhon trace-in e vet; sfidat e bus-it
janë të përbashkëta; çdo tabelë deklaron pjesën e vet S_t të bus-it (e absorbuar para γ) dhe verifikuesi kontrollon
Σ S_t = shuma publike. Teste: pjesë e zhvendosur mes tabelave, pjesë e ndryshuar, lartësi tjetër, prova të ndërruara,
të gjitha refuzohen; të gjitha testet e sulmit të R7 kalojnë mbi provën e ndarë.
