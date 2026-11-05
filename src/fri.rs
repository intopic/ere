//! Complete unified multi-channel FRI: commit phase, query phase and verifier.
//!
//! v2.0 (`prove_unified_multi_fri`) had only the folding half. This module adds what makes FRI a
//! proof: Fiat-Shamir folding challenges, Merkle openings, random queries and a verifier.
//!
//! PDF elements kept (f.4, f.9, f.10):
//! - all 5 RNS channels are folded together, each with its own challenge in F_{m_j}^4;
//! - V-UMT: one Merkle tree per layer for all 5 channels (a leaf holds the pair f(x), f(-x) of
//!   every channel), so one authentication path per query per layer instead of five;
//! - the prover inverts each layer's domain with one Montgomery batch inversion.
//!
//! Folding rule (natural-order domain w^0..w^(n-1), so x_{j+n/2} = -x_j):
//!   f'(x^2) = (f(x) + f(-x)) / 2 + alpha * (f(x) - f(-x)) / (2x)
//! A polynomial of degree < D on a domain of size D * blowup folds to a constant after log2(D)
//! rounds; the prover sends that last layer and the verifier checks it is constant.
//!
//! Soundness (standard FRI, conjectured bound): about `num_queries * log2(blowup)` bits.

use crate::ntt::{lde, root_of_unity};
use crate::transcript::Transcript;
use crate::{batch_inverse_channel, mod_inv_single, mul_mod_channel, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};
pub use crate::hash::Hash;
use crate::hash::{hash_leaf, hash_node, HashMode};
pub type Layer = [Vec<Extension4>; DEFAULT_RNS_CHANNELS];
type Pair = [[Extension4; 2]; DEFAULT_RNS_CHANNELS];

#[derive(Clone, Copy, Debug)]
pub struct FriParams {
    pub log_degree: u32,
    pub log_blowup: u32,
    pub num_queries: usize,
}

impl FriParams {
    pub fn domain_size(&self) -> usize {
        1usize << (self.log_degree + self.log_blowup)
    }
    pub fn conjectured_security_bits(&self) -> u32 {
        self.num_queries as u32 * self.log_blowup
    }
}

#[derive(Clone, Debug)]
pub struct LayerOpening {
    pub pair: Pair,
    pub path: Vec<Hash>,
}

#[derive(Clone, Debug)]
pub struct FriProof {
    pub layer_roots: Vec<Hash>,
    pub final_layer: Layer,
    pub queries: Vec<Vec<LayerOpening>>, // [query][layer]
}

impl FriProof {
    pub fn size_bytes(&self) -> usize {
        let opening: usize = self.queries.iter().flatten().map(|o| DEFAULT_RNS_CHANNELS * 2 * 16 + o.path.len() * 32).sum();
        self.layer_roots.len() * 32 + self.final_layer.iter().map(|v| v.len() * 16).sum::<usize>() + opening
    }
}

fn leaf_hash(mode: HashMode, pair: &Pair) -> Hash {
    let v: Vec<u32> = pair.iter().flat_map(|p| p[0].c.into_iter().chain(p[1].c)).collect();
    hash_leaf(mode, b"SS-RAP/v2/fri-leaf", &v)
}

pub fn node_hash(mode: HashMode, l: &Hash, r: &Hash) -> Hash {
    hash_node(mode, l, r)
}

/// Binary Merkle tree (V-UMT when a leaf packs all 5 channels). levels[0] = leaves.
pub struct Tree {
    levels: Vec<Vec<Hash>>,
}

impl Tree {
    fn build(mode: HashMode, layer: &Layer) -> Self {
        let half = layer[0].len() / 2;
        let leaves = crate::par_map(half, |j| leaf_hash(mode, &pair_at(layer, j)));
        Self::from_leaves(mode, leaves)
    }
    pub fn from_leaves(mode: HashMode, leaves: Vec<Hash>) -> Self {
        assert!(leaves.len().is_power_of_two());
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let next = crate::par_map(prev.len() / 2, |i| node_hash(mode, &prev[2 * i], &prev[2 * i + 1]));
            levels.push(next);
        }
        Self { levels }
    }
    pub fn root(&self) -> Hash {
        self.levels.last().unwrap()[0]
    }
    pub fn path(&self, mut idx: usize) -> Vec<Hash> {
        let mut out = Vec::new();
        for lvl in &self.levels[..self.levels.len() - 1] {
            out.push(lvl[idx ^ 1]);
            idx >>= 1;
        }
        out
    }
}

pub fn verify_path(mode: HashMode, root: &Hash, leaf: Hash, mut idx: usize, path: &[Hash]) -> bool {
    let mut h = leaf;
    for sib in path {
        h = if idx & 1 == 0 { node_hash(mode, &h, sib) } else { node_hash(mode, sib, &h) };
        idx >>= 1;
    }
    &h == root
}

fn pair_at(layer: &Layer, j: usize) -> Pair {
    let half = layer[0].len() / 2;
    std::array::from_fn(|ch| [layer[ch][j], layer[ch][j + half]])
}

fn fold_value(f0: Extension4, f1: Extension4, alpha: &Extension4, inv_x: u32, ch: usize) -> Extension4 {
    let inv_two = (RNS_MODULI[ch] + 1) / 2;
    let even = f0.add(&f1, ch).mul_scalar(inv_two, ch);
    let odd = f0.sub(&f1, ch).mul_scalar(inv_two, ch).mul_scalar(inv_x, ch);
    even.add(&alpha.mul(&odd, ch), ch)
}

fn fold_layer(layer: &Layer, alphas: &[Extension4; DEFAULT_RNS_CHANNELS], shift: &[u32; DEFAULT_RNS_CHANNELS]) -> Layer {
    let n = layer[0].len();
    let half = n / 2;
    std::array::from_fn(|ch| {
        let w = root_of_unity(n, ch);
        let mut xs = Vec::with_capacity(half);
        let mut x = shift[ch];
        for _ in 0..half {
            xs.push(x);
            x = mul_mod_channel(x, w, ch);
        }
        let inv = batch_inverse_channel(&xs, ch);
        (0..half).map(|j| fold_value(layer[ch][j], layer[ch][j + half], &alphas[ch], inv[j], ch)).collect()
    })
}

/// Commits to the evaluations of one polynomial per channel (coefficients, degree < 2^log_degree)
/// and proves they are low-degree.
pub fn prove(coeffs: &[Vec<u32>; DEFAULT_RNS_CHANNELS], params: &FriParams, t: &mut Transcript) -> FriProof {
    let d = 1usize << params.log_degree;
    let blowup = 1usize << params.log_blowup;
    let initial: Layer = std::array::from_fn(|ch| {
        assert!(coeffs[ch].len() <= d, "polynomial degree too high for params");
        let mut c = coeffs[ch].clone();
        c.resize(d, 0);
        lde(&c, blowup, ch).into_iter().map(Extension4::from_base).collect()
    });
    prove_from_evaluations(initial, params, t)
}

/// Same as `prove`, starting from evaluations on the domain of size `domain_size()`.
pub fn prove_from_evaluations(initial: Layer, params: &FriParams, t: &mut Transcript) -> FriProof {
    prove_coset(initial, &[1; DEFAULT_RNS_CHANNELS], params, t).0
}

/// FRI on the coset shift * <w> (per channel). Returns the proof and the layer-0 query indices
/// (each index i opens positions i and i + n/2), so that a STARK can open its trace there.
pub fn prove_coset(initial: Layer, shift: &[u32; DEFAULT_RNS_CHANNELS], params: &FriParams, t: &mut Transcript) -> (FriProof, Vec<usize>) {
    assert_eq!(initial[0].len(), params.domain_size());
    let mut shift = *shift;
    t.absorb(b"fri/params", &[params.log_degree as u8, params.log_blowup as u8, params.num_queries as u8]);
    let mut layers = vec![initial];
    let mut trees = Vec::new();
    let mut roots = Vec::new();
    for _ in 0..params.log_degree {
        let tree = Tree::build(t.mode(), layers.last().unwrap());
        t.absorb(b"fri/root", &tree.root());
        roots.push(tree.root());
        trees.push(tree);
        let alphas = t.challenge_ext4_all(b"fri/alpha");
        let next = fold_layer(layers.last().unwrap(), &alphas, &shift);
        layers.push(next);
        shift = std::array::from_fn(|ch| mul_mod_channel(shift[ch], shift[ch], ch));
    }
    let final_layer = layers.pop().unwrap();
    absorb_final(t, &final_layer);

    let half0 = params.domain_size() / 2;
    let indices: Vec<usize> = (0..params.num_queries).map(|_| t.challenge_index(b"fri/query", half0)).collect();
    let queries = indices
        .iter()
        .map(|&i| {
            layers
                .iter()
                .zip(&trees)
                .map(|(layer, tree)| {
                    let j = i % (layer[0].len() / 2);
                    LayerOpening { pair: pair_at(layer, j), path: tree.path(j) }
                })
                .collect()
        })
        .collect();
    (FriProof { layer_roots: roots, final_layer, queries }, indices)
}

fn absorb_final(t: &mut Transcript, final_layer: &Layer) {
    let bytes: Vec<u8> = final_layer.iter().flatten().flat_map(|e| e.to_bytes()).collect();
    t.absorb(b"fri/final", &bytes);
}

/// Verifier. Returns true iff every query is consistent with a polynomial of degree < 2^log_degree.
pub fn verify(proof: &FriProof, params: &FriParams, t: &mut Transcript) -> bool {
    verify_coset(proof, &[1; DEFAULT_RNS_CHANNELS], params, t).is_some()
}

/// Coset verifier. On success returns the layer-0 query indices.
pub fn verify_coset(proof: &FriProof, shift0: &[u32; DEFAULT_RNS_CHANNELS], params: &FriParams, t: &mut Transcript) -> Option<Vec<usize>> {
    verify_inner(proof, shift0, params, t)
}

fn verify_inner(proof: &FriProof, shift0: &[u32; DEFAULT_RNS_CHANNELS], params: &FriParams, t: &mut Transcript) -> Option<Vec<usize>> {
    let rounds = params.log_degree as usize;
    let n0 = params.domain_size();
    let blowup = 1usize << params.log_blowup;
    if proof.layer_roots.len() != rounds || proof.queries.len() != params.num_queries {
        return None;
    }
    if proof.final_layer.iter().any(|v| v.len() != blowup || v.iter().any(|e| *e != v[0])) {
        return None; // last layer must be a constant
    }
    t.absorb(b"fri/params", &[params.log_degree as u8, params.log_blowup as u8, params.num_queries as u8]);
    let mut alphas = Vec::with_capacity(rounds);
    for root in &proof.layer_roots {
        t.absorb(b"fri/root", root);
        alphas.push(t.challenge_ext4_all(b"fri/alpha"));
    }
    absorb_final(t, &proof.final_layer);

    let indices: Vec<usize> = (0..params.num_queries).map(|_| t.challenge_index(b"fri/query", n0 / 2)).collect();
    for (q, &i) in proof.queries.iter().zip(&indices) {
        if q.len() != rounds {
            return None;
        }
        let mut n = n0;
        let mut shift = *shift0;
        for (l, open) in q.iter().enumerate() {
            let half = n / 2;
            let j = i % half;
            if open.path.len() != half.trailing_zeros() as usize
                || !verify_path(t.mode(), &proof.layer_roots[l], leaf_hash(t.mode(), &open.pair), j, &open.path)
            {
                return None;
            }
            for ch in 0..DEFAULT_RNS_CHANNELS {
                let x = mul_mod_channel(shift[ch], pow(root_of_unity(n, ch), j as u64, ch), ch);
                let inv_x = mod_inv_single(x, RNS_MODULI[ch]);
                let folded = fold_value(open.pair[ch][0], open.pair[ch][1], &alphas[l][ch], inv_x, ch);
                let expected = if l + 1 < rounds {
                    let next_half = half / 2;
                    q[l + 1].pair[ch][(j >= next_half) as usize]
                } else {
                    proof.final_layer[ch][j]
                };
                if folded != expected {
                    return None;
                }
            }
            n = half;
            shift = std::array::from_fn(|ch| mul_mod_channel(shift[ch], shift[ch], ch));
        }
    }
    Some(indices)
}

fn pow(mut b: u32, mut e: u64, ch: usize) -> u32 {
    let mut r = 1u32;
    while e > 0 {
        if e & 1 == 1 {
            r = mul_mod_channel(r, b, ch);
        }
        b = mul_mod_channel(b, b, ch);
        e >>= 1;
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;

    fn params() -> FriParams {
        FriParams { log_degree: 8, log_blowup: 2, num_queries: 30 }
    }

    fn random_poly(seed: u64, len: usize) -> [Vec<u32>; DEFAULT_RNS_CHANNELS] {
        let mut s = seed;
        std::array::from_fn(|ch| {
            (0..len)
                .map(|_| {
                    s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    ((s >> 33) as u32) % RNS_MODULI[ch]
                })
                .collect()
        })
    }

    #[test]
    fn honest_low_degree_polynomial_verifies() {
        let p = params();
        let coeffs = random_poly(1, 1 << p.log_degree);
        let proof = prove(&coeffs, &p, &mut Transcript::new(b"fri-test"));
        assert!(verify(&proof, &p, &mut Transcript::new(b"fri-test")));
        assert_eq!(proof.layer_roots.len(), 8);
    }

    #[test]
    fn too_high_degree_is_rejected() {
        // Degree 4x too high: the evaluations are far from any degree < 2^8 polynomial.
        let p = params();
        let coeffs = random_poly(2, 1 << 10);
        let evals: Layer = std::array::from_fn(|ch| {
            let mut c = coeffs[ch].clone();
            crate::ntt::ntt(&mut c, ch);
            c.into_iter().map(Extension4::from_base).collect()
        });
        assert_eq!(evals[0].len(), p.domain_size());
        // An honest-looking prover runs the protocol on these evaluations; the last layer is not
        // constant (and any attempt to fake it fails the query checks).
        let proof = prove_from_evaluations(evals, &p, &mut Transcript::new(b"fri-test"));
        assert!(!verify(&proof, &p, &mut Transcript::new(b"fri-test")));

        let mut faked = proof.clone();
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let c = faked.final_layer[ch][0];
            faked.final_layer[ch].iter_mut().for_each(|e| *e = c);
        }
        assert!(!verify(&faked, &p, &mut Transcript::new(b"fri-test")));
    }

    #[test]
    fn corrupted_codeword_is_rejected() {
        // Change 30% of the committed evaluations of an honest codeword.
        let p = params();
        let coeffs = random_poly(3, 1 << p.log_degree);
        let mut evals: Layer = std::array::from_fn(|ch| {
            let mut c = coeffs[ch].clone();
            c.resize(p.domain_size(), 0);
            crate::ntt::ntt(&mut c, ch);
            c.into_iter().map(Extension4::from_base).collect()
        });
        for ch in 0..DEFAULT_RNS_CHANNELS {
            for k in (0..p.domain_size()).step_by(3) {
                evals[ch][k] = evals[ch][k].add(&Extension4::ONE, ch);
            }
        }
        let proof = prove_from_evaluations(evals, &p, &mut Transcript::new(b"fri-test"));
        assert!(!verify(&proof, &p, &mut Transcript::new(b"fri-test")));
    }

    #[test]
    fn tampered_proof_is_rejected() {
        let p = params();
        let coeffs = random_poly(4, 1 << p.log_degree);
        let proof = prove(&coeffs, &p, &mut Transcript::new(b"fri-test"));

        let mut bad = proof.clone();
        bad.queries[0][2].pair[1][0] = bad.queries[0][2].pair[1][0].add(&Extension4::ONE, 1);
        assert!(!verify(&bad, &p, &mut Transcript::new(b"fri-test")), "opening value changed");

        let mut bad = proof.clone();
        bad.layer_roots[0][0] ^= 1;
        assert!(!verify(&bad, &p, &mut Transcript::new(b"fri-test")), "root changed");

        let mut bad = proof.clone();
        bad.queries[3][0].path[0][5] ^= 1;
        assert!(!verify(&bad, &p, &mut Transcript::new(b"fri-test")), "path changed");

        assert!(!verify(&proof, &p, &mut Transcript::new(b"other-label")), "different transcript");
    }
}
