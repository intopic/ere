# Arkiv: rekursioni STARK-brenda-STARK (eksperimental)

Ky folder nuk kompilohet (nuk është pjesë e workspace-it). Përmban eksperimentin e
rekursionit me motorin tonë (AIR për Merkle, FRI, transcript, kompozim) dhe `rns256.rs`.

Pse u arkivua: në qarkun Groth16 kushton 113–228M kufizime (shih `REKURSIONI.md`), gjë që
nuk është praktike. Rruga kryesore tani është Plonky3 (`p3/`) me mbështjellës Groth16 direkt.

Për ta rikthyer: zhvendos skedarët te `src/` dhe shto `pub mod ...;` te `src/lib.rs`.
