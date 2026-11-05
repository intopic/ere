//! Constraint counts of the wrapper gadgets, measured on real circuits, and the projection of
//! the full in-circuit STARK verifier for a given proof shape.

use super::fp31::{E4, M31};

use ark_bn254::Fr;
use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef};
use ss_rap_v2::RNS_MODULI;

fn count<F: FnOnce(&ConstraintSystemRef<Fr>)>(f: F) -> usize {
    let cs = ConstraintSystem::<Fr>::new_ref();
    f(&cs);
    assert!(cs.is_satisfied().unwrap());
    cs.num_constraints()
}

#[derive(Clone, Copy, Debug)]
pub struct GadgetCosts {
    /// Range-checked 31-bit value opened from a commitment.
    pub value: usize,
    /// One F_m^4 multiplication followed by a reduction (the unit of the algebra).
    pub ext_mul: usize,
    /// One Poseidon permutation absorbing 2 field elements (Merkle node).
    pub hash2: usize,
    /// One unreduced F_m^4 product accumulated lazily (no reduction).
    pub ext_mul_lazy: usize,
}

pub fn measure() -> GadgetCosts {
    let ch = 0;
    let m = RNS_MODULI[ch];
    let value = count(|cs| {
        M31::witness(cs, Some(m - 1), ch).unwrap();
    });
    let ext = |reduce: bool| {
        count(|cs| {
            let a = E4::witness(cs, Some([m - 1, 2, 3, 4]), ch).unwrap();
            let b = E4::witness(cs, Some([5, m - 6, 7, 8]), ch).unwrap();
            let p = a.mul(&b);
            if reduce {
                p.reduce(cs).unwrap();
            }
        }) - 2 * 4 * value
    };
    let (ext_mul, ext_mul_lazy) = (ext(true), ext(false));
    let cfg = ss_rap_v2::hash::poseidon_config();
    let hash2 = count(|cs| {
        let a = FpVar::new_witness(cs.clone(), || Ok(Fr::from(1u64))).unwrap();
        let b = FpVar::new_witness(cs.clone(), || Ok(Fr::from(2u64))).unwrap();
        let mut s = PoseidonSpongeVar::new(cs.clone(), cfg);
        s.absorb(&vec![a, b]).unwrap();
        s.squeeze_field_elements(1).unwrap();
    });
    GadgetCosts { value, ext_mul, hash2, ext_mul_lazy }
}

/// Shape of a STARK proof as the in-circuit verifier sees it.
#[derive(Clone, Copy, Debug)]
pub struct ProofShape {
    pub lanes: usize,
    pub main_cols: usize,
    /// Extension-field aux columns.
    pub aux_cols: usize,
    /// AIR constraints per row (base field), plus range/bus inverse checks and the running sum.
    pub composition_terms: usize,
    pub log_domain: u32,
    pub fri_layers: usize,
    pub queries: usize,
    /// 31-bit values packed per native element when hashing leaves (1 = no packing).
    pub pack: usize,
    /// Linear combinations with precomputed powers and one reduction at the end, instead of
    /// Horner with a reduction per step.
    pub lazy: bool,
}

#[derive(Clone, Copy, Debug)]
pub struct Projection {
    pub per_query: usize,
    pub total: usize,
    pub hashing_share: f64,
}

pub fn project(s: &ProofShape, g: &GadgetCosts) -> Projection {
    let lane_vals = s.main_cols + 4 * s.aux_cols + 4; // + quotient
    let leaf_vals = s.lanes * lane_vals;
    let leaf_hash = leaf_vals.div_ceil(2 * s.pack) * g.hash2;
    let depth = s.log_domain as usize;
    // 4 openings (x, -x and both next rows), 3 trees each: leaves, paths and range checks.
    let openings = 4 * (leaf_hash + 3 * depth * g.hash2 + leaf_vals * g.value);
    // At x and -x, per lane: composition (Horner in gamma) and the FRI combination (in delta).
    let terms = s.composition_terms + s.main_cols + s.aux_cols + 4;
    let algebra = if s.lazy {
        // terms * lazy product + the AIR's own products (~2 per constraint) + 8 final reductions,
        // and the powers gamma^k, delta^k once per proof (amortised over the queries below).
        2 * s.lanes * (terms * g.ext_mul_lazy + 2 * s.composition_terms * g.ext_mul_lazy / 4 + 8 * g.ext_mul) + s.lanes * terms * g.ext_mul / s.queries
    } else {
        2 * s.lanes * terms * g.ext_mul
    };
    // FRI: per layer, one path + a leaf of 2 ext values per lane + a fold (~3 ext ops) per lane.
    let fri: usize = (0..s.fri_layers).map(|l| (depth - l) * g.hash2 + (s.lanes * 8).div_ceil(2) * g.hash2 + s.lanes * (8 * g.value + 3 * g.ext_mul)).sum();
    let hashing = 4 * (leaf_hash + 3 * depth * g.hash2) + (0..s.fri_layers).map(|l| (depth - l) * g.hash2).sum::<usize>();
    let per_query = openings + algebra + fri;
    Projection { per_query, total: s.queries * per_query, hashing_share: s.queries as f64 * hashing as f64 / (s.queries * per_query) as f64 }
}

/// Shape of today's state-transition proof for a 1000-tx batch (256 rows per lane, blowup 4).
pub fn state_shape(queries: usize, log_blowup: u32, pack: usize, lazy: bool) -> ProofShape {
    let log_rows = 8;
    ProofShape {
        lanes: 5,
        main_cols: 67,
        aux_cols: 44 + 1 + 5 + 1,
        composition_terms: 35 + 44 + 1 + 5 + 1,
        log_domain: log_rows + log_blowup,
        fri_layers: log_rows as usize,
        queries,
        pack,
        lazy,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gadget_costs_are_small() {
        let g = measure();
        assert!(g.value <= 40, "{g:?}");
        assert!(g.ext_mul < 400, "{g:?}");
        assert!(g.hash2 < 400, "{g:?}");
    }
}
