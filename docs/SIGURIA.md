# Siguria: profilet dhe çfarë mbetet hapur

Ky skedar ndjek rregullimet nga auditimi i jashtëm (commit `2db7836`, 7.11.2026) dhe atë që kodi
garanton sot. Gjetjet: C-01, C-02, H-01, H-02, C-03, M-01…M-06, SET-06.

## Profili i parametrave (H-02)

`ss_rap_p3::state::Params::conjectured_bits()` = `log_blowup * queries + query_pow`. Kjo është vetëm
pjesa FRI e sigurisë, nën hamendësimin e zakonshëm (proximity gaps). Nuk është provë për gjithë
sistemin.

| Profili | log_blowup | queries | query_pow | bit (hamendësuar) | Ku përdoret |
|---|---|---|---|---|---|
| `Params::production(log_rows)` | 3 (×8) | 28 | 16 | 100 | mainnet |
| Sepolia (`sepolia_e2e`) | 1 (×2) | 4 | 8 | 12 | testnet, `Profile::Development` |
| Fixture-t e CI-së | 1 | 4 | 8 | 12 | vetëm teste |

`P3Prover::new(batch, params, Profile::Production)` e refuzon çdo profil nën
`MIN_PRODUCTION_BITS = 100` (`PipelineError::InsecureParams`). Profili i zhvillimit duhet zgjedhur
shprehimisht (`Profile::Development`). `E2E_PRODUCTION=1 script/sepolia_e2e.sh` e provon batch-in
me profilin e prodhimit.

Kufizime që mbeten dhe duhen analizuar veç e veç para mainnet-it:
- Fusha e sfidave është BabyBear⁴ (|K| ≈ 2^123.6), pra kufiri Schwartz–Zippel për një kontroll të
  vetëm është rreth 2^-(123.6 − log2 shkalla). 128 bit të plota nuk arrihen pa një zgjerim më të madh.
- LogUp, Fiat–Shamir mbi Poseidon2-BN254 dhe Groth16 mbi BN254 (~100–110 bit) shtojnë humbjet e
  tyre. Synimi i deklaruar është **100 bit të hamendësuar**, jo 128.
- Pesë korsitë nuk shumëzojnë sigurinë: sulmuesit i mjafton të thyejë një.

## Domeni i vendosjes (SET-06)

Hyrja publike është
`keccak256(oldRoot, newRoot, vUmtRoot, blobsHash, batchNumber, chainid, uint256(uint160(address(this)))) mod r`,
dhe nënshkrimet e transaksioneve mbulojnë `TX_DOMAIN || chain id || adresa e kontratës || trupi`
(`public_input::Domain`). Një provë ose një nënshkrim për një kontratë nuk vlen në një tjetër.

## Pa parazgjedhje DEV (C-03, M-03)

- Nuk ka më `settle()` me wrapper-in DEV; thirrësi zgjedh `Wrapper::P3` / `Stark` / `Dev`.
- `P3Prover::new` nuk krijon çelësa; `P3Prover::dev_keys()` është setup-i me seed publik (vetëm teste/testnet).
- Rastësia e Groth16 vjen nga thirrësi (`RngCore + CryptoRng`): `OsRng` në prodhim, ChaCha me seed vetëm për fixture.

## H-01: dizajni i lidhjes së blob-it (në punë)

Përmbajtja e blob-it arrin në EVM vetëm përmes precompile-it 0x0a: për një pikë `z` ai vërteton
`p_blob(z) = y`, ku `p_blob` është polinomi mbi fushën e BLS12-381 që blob-i mban në formë
vlerësimesh (rrënjët e njësisë në rend bit-reversed). Lidhja që ndërtojmë:

1. **Referenca native** (`settlement/src/blob_eval.rs`, gati): `p_blob(z)` nga bajtet e blob-it me
   formulën baricentrike të EIP-4844, e testuar kundrejt c-kzg, dhe hyrja 192-bajtëshe e 0x0a.
2. **Angazhimi i elementeve** (gati, brenda `BlobEvalAir`): një sponge Poseidon2-BabyBear me gjerësi
   24 (`p3/src/poseidon2_24.rs`, i njëjti permutacion si `default_babybear_poseidon2_24`), rate 16 dhe
   capacity 8, një permutacion për rresht: çdo element (31 bajte) hyn si 11 vlera me nga 3 bajte.
   Digest-i `D` (8 elemente BabyBear, ~124 bit kundër përplasjeve) del si vlerë publike, O(1) për
   Groth16.
3. **Pika:** `z = H(D, versioned hashes) mod r_bls`, e llogaritur në qarkun Groth16. Prover-i nuk
   mund ta zgjedhë `z` para se të fiksojë elementet.
4. **Vlerësimi brenda STARK-ut** (`p3/src/blob_eval.rs`, gati si AIR më vete): me AIR-in MULMOD (moduli BLS12-381), për çdo element
   `u_i·(z − w_i) ≡ e_i·w_i`, shuma `Σ u_i`, pastaj `y·4096 = Σ u_i·(z^4096 − 1)`. Rreth 2 rreshta
   MULMOD për element, pra rreth 50k rreshta për 6 blob-e. Në fakt: një AIR me 600 kolona dhe 4 096
   rreshta për blob; `S = Σ e_i·w_i/(z − w_i)` del si vlerë publike dhe `p(z) = S·(z^4096 − 1)/4096`
   llogaritet në qarkun Groth16. Testi kundrejt c-kzg kalon; një blob provohet në ~1 s në CPU.
   Pas lehtësimit (pjesa 4): një identitet i vetëm `u·d + q2·P = e·w + q1·P` me një grup
   carry-sh, bajtet kontrollohen dy nga dy në busin "byte2" (`BytePairTableAir`, 2^16 rreshta),
   815 kolona. Disa blob-e (slot-e) hyjnë në një instancë; slot-i bosh jep `S = 0`.
5. **Lidhja me ekzekutimin** (`p3/src/tx_bind.rs`, gati): formati i blob-it ka një slot për
   transaksion, 4 elemente (124 bajte: 118 bajtet e `Tx::encode` dhe 6 zero), 1 024 slot-e për
   blob. Transaksioni g i batch-it është te slot-i g dhe ekzekutohet te korsia g / 2^log_rows,
   rreshti g mod 2^log_rows. `TxAir` ka një rresht për slot. Merr 4 elementet e slot-it nga
   `BlobEvalAir` (busi "elem": çdo element i çdo blob-i konsumohet një herë). Një slot joaktiv
   duhet të jetë krejt zero. Një slot aktiv i dërgon korsisë (korsia, t, id e dërguesit, id e
   marrësit, shuma, nonce) në busin "tx", dhe çdo rresht aktiv i korsisë e merr. Adresat
   lidhen me id-të përmes tabelës publike të adresave (`AddrAir`, kolona periodike nga
   statement-i, që qarku Groth16 i nxjerr nga bajtet e adresave). Testi
   `the_blob_holds_exactly_the_executed_transfers` refuzon: një shumë tjetër, një marrës tjetër,
   dy transaksione të ndërruara, një transaksion që mungon, një transaksion shtesë dhe një slot
   të fikur që mban bajte. Bajtet e nënshkrimit mbarten, por nuk kontrollohen ende (C-02).
6. **L1:** `z` dhe `y_j` hyjnë në hash-in e header-it; kontrata thërret 0x0a për çdo blob
   (~50k gas për blob).

**Kostoja në Groth16** (forma e CI-së, 40 tx, 1 blob): 2,17M kufizime para blob-it, 6,6M me
AIR-in e parë, 2,96M pas lehtësimit, **3,20M** me lidhjen e transaksioneve (pika 5). Pjesa më e madhe e fitimit vjen nga verifikuesi në R1CS
dhe vlen për gjithë qarkun: shumëzimet lihen të pareduktuara kur kufiri e lejon, shprehjet
lineare (shtresat lineare të Poseidon2) nuk kushtojnë asgjë, palosja e kufizimeve me alpha bëhet
në dy nivele (një reduktim për 32 kufizime) dhe shkalla e fuqive të alpha në PCS gjithashtu.
Gjenerimi i fixture-it (setup + provë Groth16) arrin ~14 GB kujtesë; prova vetë ~19 s.

Dy blob-e të ndryshme përputhen në një `z` të rastësishme me probabilitet ≤ 4096/r_bls ≈ 2^-243.

## Ende hapur

| Gjetja | Gjendja |
|---|---|
| H-01 Lidhja e përmbajtjes së blob-it me transaksionet e ekzekutuara | e mbyllur në kod (1–6); nënshkrimet mbeten te C-02 |
| C-02 ECDSA brenda provës | hapur (hapi 4) |
| C-01 Ceremonia e çelësave | e shtyrë me vendim: bëhet pasi qarku të ngrihet |
| M-01, M-02, M-05, M-06, I-01 | jo në rrugën e settlement-it; të paprekura |
