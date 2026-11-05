//! R8.2: the FRI verifier of `ss_rap_v2::fri::verify_view` (HashMode::Poseidon, all 5 lanes) as
//! BN254 constraints.
//!
//! Per query and layer: the pair leaf is hashed and authenticated against the layer root at
//! position j = i mod (n_l / 2), and every lane checks the fold without inversion:
//!   2 x * next = x (f0 + f1) + alpha (f0 - f1)
//! with x the pair's point. x_0 = shift * w^i comes from the bits of i (one product per bit), and
//! x_{l+1} = +-x_l^2 (the sign is the bit that also selects which value of the next pair the
//! fold must equal). The final layer is absorbed as canonical values (no grinding through a
//! second encoding) and must be constant, as natively.
//!
//! What the STARK part needs back: the query bits, x_0 and the layer-0 pairs of every query.

use super::fp31::{range_witness, E4, M31};
use super::hash_var::{digest_witness, leaf_hash, merkle_root, value31, TranscriptVar};
use ark_bn254::Fr;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use num_bigint::BigUint;
use ss_rap_v2::fri::{FriParams, FriProof};
use ss_rap_v2::hash::tag_fr;
use ss_rap_v2::ntt::root_of_unity;
use ss_rap_v2::{mul_mod_channel, DEFAULT_RNS_CHANNELS, RNS_MODULI};

type R<T> = Result<T, SynthesisError>;
pub type Lanes<T> = [T; DEFAULT_RNS_CHANNELS];

fn lanes<T, F: FnMut(usize) -> R<T>>(mut f: F) -> R<Lanes<T>> {
    let v: Vec<T> = (0..DEFAULT_RNS_CHANNELS).map(&mut f).collect::<R<Vec<T>>>()?;
    Ok(v.try_into().unwrap_or_else(|_| unreachable!()))
}

fn ext_witness(cs: &ConstraintSystemRef<Fr>, x: Option<[u32; 4]>, ch: usize) -> R<E4> {
    let [a, b, c, d] = [0, 1, 2, 3].map(|k| value31(cs, x.map(|v| v[k]), ch));
    Ok(E4 { c: [a?, b?, c?, d?] })
}

/// A canonical value (< m): 31 bits plus the bits of m - 1 - v.
fn canonical(cs: &ConstraintSystemRef<Fr>, x: Option<u32>, ch: usize) -> R<M31> {
    let v = value31(cs, x, ch)?;
    let m = RNS_MODULI[ch];
    let d = range_witness(cs, x.map(|x| BigUint::from(m - 1 - x)), 31)?;
    (&v.v + &d).enforce_equal(&FpVar::constant(Fr::from(m - 1)))?;
    Ok(v)
}

pub struct LayerOpeningVar {
    pub pair: Lanes<[E4; 2]>,
    pub path: Vec<FpVar<Fr>>,
}

pub struct FriProofVar {
    pub roots: Vec<FpVar<Fr>>,
    /// The constant of the final layer, per lane.
    pub final_value: Lanes<E4>,
    pub queries: Vec<Vec<LayerOpeningVar>>,
}

impl FriProofVar {
    /// Witnesses a proof of shape `params` (values only when `proof` is given).
    pub fn witness(cs: &ConstraintSystemRef<Fr>, proof: Option<&FriProof>, params: &FriParams) -> R<Self> {
        let rounds = params.log_degree as usize;
        let n0 = params.domain_size();
        let roots = (0..rounds).map(|l| digest_witness(cs, proof.map(|p| &p.layer_roots[l]))).collect::<R<Vec<_>>>()?;
        let final_value = lanes(|ch| {
            let c = [0, 1, 2, 3].map(|k| canonical(cs, proof.map(|p| p.final_layer[ch][0].c[k]), ch));
            let [a, b, c2, d] = c;
            Ok(E4 { c: [a?, b?, c2?, d?] })
        })?;
        let mut queries = Vec::with_capacity(params.num_queries);
        for q in 0..params.num_queries {
            let mut layers = Vec::with_capacity(rounds);
            for l in 0..rounds {
                let o = proof.map(|p| &p.queries[q][l]);
                let pair = lanes(|ch| Ok([ext_witness(cs, o.map(|o| o.pair[ch][0].c), ch)?, ext_witness(cs, o.map(|o| o.pair[ch][1].c), ch)?]))?;
                let depth = ((n0 >> l) / 2).trailing_zeros() as usize;
                let path = (0..depth).map(|k| digest_witness(cs, o.map(|o| &o.path[k]))).collect::<R<Vec<_>>>()?;
                layers.push(LayerOpeningVar { pair, path });
            }
            queries.push(layers);
        }
        Ok(Self { roots, final_value, queries })
    }
}

pub struct FriOut {
    /// Bits of each query index i (LSB first, log2(n0 / 2) bits).
    pub index_bits: Vec<Vec<Boolean<Fr>>>,
    /// x_0 = shift * w_{n0}^i per query and lane (reduced).
    pub x0: Vec<Lanes<M31>>,
    pub alphas: Vec<Lanes<E4>>,
}

fn pow_const(b: u32, e: u64, ch: usize) -> u32 {
    let (mut b, mut e, mut r) = (b, e, 1u32);
    while e > 0 {
        if e & 1 == 1 {
            r = mul_mod_channel(r, b, ch);
        }
        b = mul_mod_channel(b, b, ch);
        e >>= 1;
    }
    r
}

/// Runs the FRI verifier on the transcript (positioned where `fri::verify_view` starts).
pub fn verify_fri(cs: &ConstraintSystemRef<Fr>, t: &mut TranscriptVar, proof: &FriProofVar, params: &FriParams, shift0: &Lanes<u32>) -> R<FriOut> {
    let rounds = params.log_degree as usize;
    let n0 = params.domain_size();
    let blowup = 1usize << params.log_blowup;
    t.absorb_const(b"fri/params", &[params.log_degree as u8, params.log_blowup as u8, params.num_queries as u8])?;
    let mut alphas = Vec::with_capacity(rounds);
    for root in &proof.roots {
        t.absorb_root(b"fri/root", root)?;
        alphas.push(t.challenge_ext4_all()?);
    }
    // final layer: `blowup` copies of the constant per lane, each 16 bytes = one element
    let mut msg = vec![FpVar::constant(tag_fr(b"fri/final")), FpVar::constant(Fr::from((DEFAULT_RNS_CHANNELS * blowup * 16) as u64))];
    for ch in 0..DEFAULT_RNS_CHANNELS {
        let c = &proof.final_value[ch].c;
        let e = &c[0].v + &c[1].v * Fr::from(1u64 << 32) + &c[2].v * Fr::from(1u128 << 64) + &c[3].v * Fr::from(1u128 << 96);
        for _ in 0..blowup {
            msg.push(e.clone());
        }
    }
    t.absorb_elements(&msg)?;

    let k_bits = (n0 / 2).trailing_zeros() as usize;
    let mut out = FriOut { index_bits: Vec::new(), x0: Vec::new(), alphas: alphas.clone() };
    for _ in 0..params.num_queries {
        out.index_bits.push(t.challenge_index(k_bits)?);
    }
    for (q, layers) in proof.queries.iter().enumerate() {
        let bits = &out.index_bits[q];
        // x_0 per lane: shift * prod_k (w^(2^k))^(b_k)
        let x0 = lanes(|ch| {
            let w = root_of_unity(n0, ch);
            let mut acc = M31::constant(shift0[ch], ch);
            for (k, b) in bits.iter().enumerate() {
                let c = pow_const(w, 1u64 << k, ch);
                let bf: FpVar<Fr> = b.clone().into();
                let factor = M31 { v: bf * Fr::from(c.wrapping_sub(1) as u64 + if c == 0 { RNS_MODULI[ch] as u64 } else { 0 }) + FpVar::one(), bound: BigUint::from(c) + 1u32, ch };
                acc = acc.mul(&factor);
                if acc.bound.bits() > 180 {
                    acc = acc.reduce(cs)?;
                }
            }
            acc.reduce(cs)
        })?;
        let mut x = x0.clone();
        for (l, open) in layers.iter().enumerate() {
            let half = (n0 >> l) / 2;
            let depth = half.trailing_zeros() as usize;
            // leaf: per lane, pair[0] then pair[1]
            let vals: Vec<FpVar<Fr>> = open.pair.iter().flat_map(|p| p.iter().flat_map(|e| e.c.iter().map(|v| v.v.clone()))).collect();
            let leaf = leaf_hash(cs, b"SS-RAP/v2/fri-leaf", &vals)?;
            let root = merkle_root(cs, &leaf, &bits[..depth], &open.path)?;
            root.enforce_equal(&proof.roots[l])?;
            // the bit that selects the next pair's value and the sign of the next point
            let sel = if l + 1 < rounds { Some(&bits[depth - 1]) } else { None };
            for ch in 0..DEFAULT_RNS_CHANNELS {
                let [f0, f1] = &open.pair[ch];
                let expected = match sel {
                    Some(b) => {
                        let [n0v, n1v] = &layers[l + 1].pair[ch];
                        select_e4(b, n1v, n0v)
                    }
                    None => proof.final_value[ch].clone(),
                };
                // 2 x * expected = x (f0 + f1) + alpha (f0 - f1)
                let lhs = expected.mul_base(&x[ch].mul_const(2));
                let rhs = f0.add(f1).mul_base(&x[ch]).add(&alphas[l][ch].mul(&f0.sub(f1)));
                lhs.sub(&rhs).assert_zero(cs)?;
            }
            if let Some(b) = sel {
                // x_{l+1} = x_l^2, negated when the pair's point is the second half
                x = lanes(|ch| {
                    let sq = x[ch].mul(&x[ch]).reduce(cs)?;
                    let m = RNS_MODULI[ch];
                    let neg = M31::constant(0, ch).sub(&sq);
                    let bf: FpVar<Fr> = b.clone().into();
                    let v = &sq.v + bf * (&neg.v - &sq.v);
                    Ok(M31 { v, bound: neg.bound.clone().max(sq.bound.clone()) + BigUint::from(m), ch })
                })?;
            }
        }
        out.x0.push(x0);
    }
    Ok(out)
}

fn select_e4(b: &Boolean<Fr>, if_true: &E4, if_false: &E4) -> E4 {
    let bf: FpVar<Fr> = b.clone().into();
    E4 {
        c: std::array::from_fn(|k| {
            let (t, f) = (&if_true.c[k], &if_false.c[k]);
            M31 { v: &f.v + bf.clone() * (&t.v - &f.v), bound: t.bound.clone().max(f.bound.clone()), ch: t.ch }
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use ss_rap_v2::fri::{prove_coset, verify_view};
    use ss_rap_v2::hash::HashMode;
    use ss_rap_v2::transcript::Transcript;
    use ss_rap_v2::Extension4;

    const P: FriParams = FriParams { log_degree: 5, log_blowup: 2, num_queries: 3 };

    fn shifts() -> Lanes<u32> {
        std::array::from_fn(ss_rap_v2::stark::shift)
    }

    fn honest() -> FriProof {
        let n = P.domain_size();
        let d = 1usize << P.log_degree;
        let layer: ss_rap_v2::fri::Layer = std::array::from_fn(|ch| {
            // evaluations of a degree < d polynomial on the coset shift * <w_n>
            let coeffs: Vec<Extension4> = (0..d).map(|k| Extension4::new((k as u32 * 77 + 5) % 1000, k as u32, 3, 9)).collect();
            let w = root_of_unity(n, ch);
            (0..n)
                .map(|i| {
                    let x = mul_mod_channel(shifts()[ch], pow_const(w, i as u64, ch), ch);
                    coeffs.iter().rev().fold(Extension4::ZERO, |acc, c| acc.mul_scalar(x, ch).add(c, ch))
                })
                .collect()
        });
        let mut t = Transcript::with_mode(b"fri-var", HashMode::Poseidon);
        prove_coset(layer, &shifts(), &P, &mut t).0
    }

    fn circuit_ok(proof: &FriProof) -> (bool, Option<FriOut>, usize) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut t = TranscriptVar::new(&cs, b"fri-var").unwrap();
        let pv = FriProofVar::witness(&cs, Some(proof), &P).unwrap();
        let out = verify_fri(&cs, &mut t, &pv, &P, &shifts()).unwrap();
        (cs.is_satisfied().unwrap(), Some(out), cs.num_constraints())
    }

    #[test]
    fn fri_gadget_accepts_honest_and_rejects_forgeries() {
        let proof = honest();
        let view = verify_view(&proof, &shifts(), &P, &mut Transcript::with_mode(b"fri-var", HashMode::Poseidon)).expect("native");
        let (ok, out, n) = circuit_ok(&proof);
        assert!(ok, "honest proof");
        eprintln!("FRI gadget: {n} constraints ({} queries, {} rounds, 5 lanes)", P.num_queries, P.log_degree);
        let out = out.unwrap();
        for (q, bits) in out.index_bits.iter().enumerate() {
            let i = bits.iter().enumerate().fold(0usize, |a, (k, b)| a | ((ark_r1cs_std::R1CSVar::value(b).unwrap() as usize) << k));
            assert_eq!(i, view.indices[q]);
            let n = P.domain_size();
            for ch in 0..DEFAULT_RNS_CHANNELS {
                let want = mul_mod_channel(shifts()[ch], pow_const(root_of_unity(n, ch), i as u64, ch), ch);
                assert_eq!(out.x0[q][ch].value().unwrap(), want);
            }
        }

        let mut bad = proof.clone();
        bad.queries[1][2].pair[3][0] = bad.queries[1][2].pair[3][0].add(&Extension4::ONE, 3);
        assert!(!circuit_ok(&bad).0, "opened pair changed");
        let mut bad = proof.clone();
        for ch in 0..DEFAULT_RNS_CHANNELS {
            for e in bad.final_layer[ch].iter_mut() {
                *e = e.add(&Extension4::ONE, ch);
            }
        }
        assert!(!circuit_ok(&bad).0, "final layer changed");
        let mut bad = proof.clone();
        bad.queries[0][1].path[0][3] ^= 1;
        // a path element that is no longer a canonical digest still hashes to another root
        assert!(!circuit_ok(&bad).0, "path changed");
    }
}
