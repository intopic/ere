//! Poseidon over BN254 (t = 3, rate 2, x^5, 8 full + 57 partial rounds), native and in-circuit.

use ark_bn254::Fr;
use ark_crypto_primitives::sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonConfig, PoseidonSponge};
use ark_crypto_primitives::sponge::CryptographicSponge;

pub fn config() -> PoseidonConfig<Fr> {
    let (ark, mds) = find_poseidon_ark_and_mds::<Fr>(254, 2, 8, 57, 0);
    PoseidonConfig::new(8, 57, 5, mds, ark, 2, 1)
}

/// Native 2-to-1 compression used for Merkle nodes.
pub fn hash2(cfg: &PoseidonConfig<Fr>, a: Fr, b: Fr) -> Fr {
    let mut s = PoseidonSponge::new(cfg);
    s.absorb(&vec![a, b]);
    s.squeeze_field_elements::<Fr>(1)[0]
}
