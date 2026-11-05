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
| R8 | Qarku BN254 që verifikon (3) + Groth16 + kontrata, end-to-end në CI | ⏳ |

## Ndershmëria

Deri sa të mbarojë R8, kontrata pranon provën Groth16 të qarkut DEV. STARK-u verifikohet nga aggregator-i.
Ky kufizim është shkruar edhe te `settlement/src/groth16.rs`.
