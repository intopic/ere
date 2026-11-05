# Rruga drejt një projekti të nivelit institucional

Qëllimi nuk ndryshon: **inovacion në shpejtësi dhe në pagesë**, me metodën e PDF-së ("mos llogarit, verifiko").
Më poshtë janë propozimet që e forcojnë projektin para investitorëve, auditimit dhe klientëve institucionalë.
Secila është e shënuar me fazën ku hyn.

## A. Inovacione që forcojnë avantazhin (shpejtësi dhe pagesë)

1. **Shkallëzim horizontal sipas kanaleve (B).** Kanalet RNS janë plotësisht të pavarura, kështu që çdo kanal mund
   të shkojë në një GPU më vete (5 GPU = 5 kanale), pa komunikim gjatë provës. Ky është një avantazh unik që
   proverët me bartje nuk e kanë. Synimi është ta masim dhe ta vendosim në qendër të prezantimit.
2. **Konfirmim i butë me garanci ekonomike (C).** Sequencer-i nënshkruan konfirmimin < 200 ms dhe ka një depozitë
   (bond). Nëse tx nuk përfshihet në batch, depozita digjet. Institucionet marrin shpejtësi bashkë me garanci.
3. **Agregim i provave (C).** Disa batch mbështillen në një provë Groth16, kështu që kostoja ~240k gas ndahet në
   më shumë tx. Kjo ul koston për tx dhe ruan marzhin edhe kur gas-i në L1 rritet.
4. **Tarifa transparente "çmim i mesëm" (C).** Formula publike: tarifa = max(çmimi bazë, kosto reale × (1 + tampon)),
   me kufi te $0.006 / $0.025. Kostoja reale (blob gas + GPU) publikohet në event-in e çdo batch-i, që
   institucionet ta auditojnë vetë.
5. **Pagesë me stablecoin (C).** Paymaster ERC-4337, me të cilin klientët paguajnë tarifat në USDC/EURC pa
   pasur ETH. Kjo është shumë e rëndësishme për klientët institucionalë.

## B. Fortifikime të domosdoshme (para mainnet-it)

1. **Trusted setup i vërtetë** (ceremoni me shumë palë, mbi Powers of Tau publik). VK-ja e tanishme demo (11·G1…)
   lejon falsifikime.
2. **Vërtetim formal i sigurisë.** Argumenti i PDF-së (§2.2) duhet zgjeruar për kolonat 64-bit të `uint256`,
   LogUp me Fiat-Shamir dhe parametrat e FRI, deri në ≥ 100 bit siguri (p.sh. 50+ query me blowup 4, ose grinding).
3. **Auditim i jashtëm.** Një për kriptografinë (Rust/AIR) dhe një për Solidity.
4. **Kontrata.**
   - multisig + timelock për përditësime
   - pause guardian
   - "escape hatch" (forced inclusion) që përdoruesit të mund të tërheqin fondet edhe kur sequencer-i ndalon
   - disa aggregator-ë
5. **Testim i thellë në CI.**
   - fuzzing (cargo-fuzz, proptest)
   - Foundry fuzz/invariant
   - Slither për kontratën
   - teste sulmi për çdo kufizim (kjo praktikë ka nisur te `uint256`, `logup` dhe `fri`)
6. **Operacione.**
   - çelësi i aggregator-it në HSM
   - `SECURITY.md` dhe programi i raportimit të dobësive
   - monitorim i kohës së provës dhe kostos për batch
7. **Pretendimet publike vetëm të matura.** Çdo shifër në README/PDF lidhet me një benchmark në CI. Ky parim
   ndiqet tashmë: S1–S6 ekzekutohen në çdo push.

## C. Gjendja e matur tani (faza A, CPU, një thread)

| Matja | Rezultati |
|---|---|
| Verifiko në vend që të llogaritësh | 2.3–2.5× |
| Kufizimet pa bartje (5 kanale paralele) | 4.5× vonesë më e ulët, 0.88× punë |
| Batch inversion | 5–6× |
| V-UMT | 5× më pak hash |
| FRI i plotë, 5 kanale, shkallë < 2^14 | prove ~67 ms, verify ~1.3 ms, provë ~237 KiB |
| STARK end-to-end, 1024 × MULMOD uint256 (secp256k1), 50 query | prove ~1.1 s në 4 bërthama CPU, verify ~23 ms, provë ~4.7 MiB |

Prova STARK është e madhe (4.7 MiB) dhe ende në CPU. Për L1 ajo mbështillet në Groth16 (faza C), kështu që në zinxhir
shkon vetëm një provë e vogël me kosto ~240k gas. Shpejtësia 2.5–4 s për një batch të plotë synohet në fazën B (GPU,
një kanal për GPU).
