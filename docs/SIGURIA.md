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
2. **Angazhimi i elementeve:** STARK-u mban elementet e blob-it si bajte dhe i thith në një
   sponge Poseidon2-BabyBear; digest-i `D` del si vlerë publike (O(1) për Groth16).
3. **Pika:** `z = H(D, versioned hashes) mod r_bls`, e llogaritur në qarkun Groth16. Prover-i nuk
   mund ta zgjedhë `z` para se të fiksojë elementet.
4. **Vlerësimi brenda STARK-ut:** me AIR-in MULMOD (moduli BLS12-381), për çdo element
   `u_i·(z − w_i) ≡ e_i·w_i`, shuma `Σ u_i`, pastaj `y·4096 = Σ u_i·(z^4096 − 1)`. Rreth 2 rreshta
   MULMOD për element, pra rreth 50k rreshta për 6 blob-e.
5. **Lidhja me ekzekutimin:** një bus nga rreshtat e transaksioneve te bajtet e blob-it (pozicioni,
   vlera), sipas formatit kanonik `Tx::encode`.
6. **L1:** `z` dhe `y_j` hyjnë në hash-in e header-it; kontrata thërret 0x0a për çdo blob
   (~50k gas për blob).

Dy blob-e të ndryshme përputhen në një `z` të rastësishme me probabilitet ≤ 4096/r_bls ≈ 2^-243.

## Ende hapur

| Gjetja | Gjendja |
|---|---|
| H-01 Lidhja e përmbajtjes së blob-it me transaksionet e ekzekutuara | në punë (pjesa 1/6 gati) |
| C-02 ECDSA brenda provës | hapur (hapi 4) |
| C-01 Ceremonia e çelësave | e shtyrë me vendim: bëhet pasi qarku të ngrihet |
| M-01, M-02, M-05, M-06, I-01 | jo në rrugën e settlement-it; të paprekura |
