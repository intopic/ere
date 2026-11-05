//! LogUp byte range check, made sound with Fiat-Shamir (PDF f.3, §2.2, constraint 2).
//!
//! Claim: every limb value l_i lies in the table T = [0, 255].
//! The prover commits to the limbs and to a multiplicity vector mult[t] *before* the challenge
//! alpha is drawn from the transcript. The verifier then checks, in every RNS channel j,
//!
//! ```text
//! sum_i 1 / (alpha_j - l_i)  ==  sum_t mult[t] / (alpha_j - t)        in F_{m_j}^4
//! ```
//!
//! If some l_i is not in T, the two sides are different rational functions of alpha, so they
//! agree only if alpha_j hits one of at most (n + 256) roots: probability <= (n + 256) / m_j^4
//! per channel (about 2^-104 for n = 2^20), and the 5 channels use independent challenges.
//!
//! v2.0 (`verify_logup_byte_range_channel`) recomputed mult[] from the limbs it was checking and
//! used a fixed alpha, so it could never fail. That function is kept only as a consistency check.
//!
//! All denominators are inverted with one Montgomery batch inversion per channel (PDF f.2,
//! "batch inversion ... for LogUp denominators"), not one extended-Euclid call per limb.

use crate::transcript::Transcript;
use crate::{CarryFreeMulWitnessRow, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};
use blake3::Hasher;

pub const TABLE_SIZE: usize = 256;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogUpProof {
    pub limb_commitment: [u8; 32],
    pub multiplicities: Vec<u32>, // length TABLE_SIZE
}

/// Stand-in for the trace commitment: hash of the limb column. In the full STARK this is the
/// V-UMT root of the trace, and the verifier reads limbs through Merkle openings.
pub fn commit_limbs(limbs: &[u32]) -> [u8; 32] {
    let mut h = Hasher::new();
    h.update(b"SS-RAP/v2/limbs");
    h.update(&(limbs.len() as u64).to_le_bytes());
    for l in limbs {
        h.update(&l.to_le_bytes());
    }
    *h.finalize().as_bytes()
}

/// All byte limbs of a, b, q, r of every row, as field elements.
pub fn limbs_of_rows(rows: &[CarryFreeMulWitnessRow]) -> Vec<u32> {
    rows.iter()
        .flat_map(|r| {
            r.a_limbs
                .iter()
                .chain(r.b_limbs.iter())
                .chain(r.q_limbs.iter())
                .chain(r.r_limbs.iter())
                .map(|&b| b as u32)
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Montgomery batch inversion in F_m^4: one tower inverse + 3(n-1) multiplications.
/// Returns None if any element is zero.
pub fn batch_inverse_ext4(values: &[Extension4], ch: usize) -> Option<Vec<Extension4>> {
    let n = values.len();
    if n == 0 {
        return Some(Vec::new());
    }
    let mut prefix = Vec::with_capacity(n);
    let mut acc = Extension4::ONE;
    for v in values {
        if *v == Extension4::ZERO {
            return None;
        }
        acc = acc.mul(v, ch);
        prefix.push(acc);
    }
    let mut inv = acc.inverse(ch);
    let mut out = vec![Extension4::ZERO; n];
    for i in (1..n).rev() {
        out[i] = inv.mul(&prefix[i - 1], ch);
        inv = inv.mul(&values[i], ch);
    }
    out[0] = inv;
    Some(out)
}

fn bind(t: &mut Transcript, proof: &LogUpProof) -> [Extension4; DEFAULT_RNS_CHANNELS] {
    t.absorb(b"logup/limbs", &proof.limb_commitment);
    t.absorb_u32s(b"logup/mult", &proof.multiplicities);
    t.challenge_ext4_all(b"logup/alpha")
}

/// Prover: count multiplicities and bind them to the transcript.
pub fn prove(limbs: &[u32], t: &mut Transcript) -> LogUpProof {
    let mut mult = vec![0u32; TABLE_SIZE];
    for &l in limbs {
        // An honest prover only has in-range limbs. Out-of-range limbs get no table entry, so
        // a cheating prover that calls this still produces a proof that fails verification.
        if (l as usize) < TABLE_SIZE {
            mult[l as usize] += 1;
        }
    }
    let proof = LogUpProof { limb_commitment: commit_limbs(limbs), multiplicities: mult };
    let _ = bind(t, &proof);
    proof
}

/// Verifier: re-derive alpha from the transcript and check the grand-sum identity per channel.
pub fn verify(limbs: &[u32], proof: &LogUpProof, t: &mut Transcript) -> bool {
    if proof.multiplicities.len() != TABLE_SIZE || commit_limbs(limbs) != proof.limb_commitment {
        return false;
    }
    // Multiplicities must not wrap around in any channel.
    let min_m = *RNS_MODULI.iter().min().unwrap() as u64;
    if (limbs.len() as u64) >= min_m || proof.multiplicities.iter().any(|&x| x as u64 >= min_m) {
        return false;
    }
    let alphas = bind(t, proof);

    (0..DEFAULT_RNS_CHANNELS).all(|ch| {
        let m = RNS_MODULI[ch];
        let alpha = alphas[ch];
        let lhs_den: Vec<Extension4> = limbs
            .iter()
            .map(|&l| alpha.sub(&Extension4::from_base(l % m), ch))
            .collect();
        let rhs_den: Vec<Extension4> = (0..TABLE_SIZE as u32)
            .map(|v| alpha.sub(&Extension4::from_base(v), ch))
            .collect();
        let (Some(lhs_inv), Some(rhs_inv)) =
            (batch_inverse_ext4(&lhs_den, ch), batch_inverse_ext4(&rhs_den, ch))
        else {
            return false; // alpha hit a limb or table value: negligible, reject
        };
        let lhs = lhs_inv.iter().fold(Extension4::ZERO, |s, x| s.add(x, ch));
        let rhs = rhs_inv
            .iter()
            .zip(&proof.multiplicities)
            .fold(Extension4::ZERO, |s, (x, &k)| s.add(&x.mul_scalar(k % m, ch), ch));
        lhs == rhs
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn honest_limbs() -> Vec<u32> {
        let rows: Vec<CarryFreeMulWitnessRow> = [(u64::MAX, u64::MAX - 7), (123456789, 987654321), (0, 5)]
            .iter()
            .map(|&(a, b)| CarryFreeMulWitnessRow::generate(a, b))
            .collect();
        limbs_of_rows(&rows)
    }

    #[test]
    fn honest_limbs_verify() {
        let limbs = honest_limbs();
        let proof = prove(&limbs, &mut Transcript::new(b"logup-test"));
        assert!(verify(&limbs, &proof, &mut Transcript::new(b"logup-test")));
    }

    #[test]
    fn out_of_range_limb_is_rejected() {
        let mut limbs = honest_limbs();
        limbs[3] = 300; // not a byte
        let proof = prove(&limbs, &mut Transcript::new(b"logup-test"));
        assert!(!verify(&limbs, &proof, &mut Transcript::new(b"logup-test")));

        // Cheater tries to hide 300 as 300 - 256 = 44 in the multiplicities.
        let mut forged = proof.clone();
        forged.multiplicities[44] += 1;
        assert!(!verify(&limbs, &forged, &mut Transcript::new(b"logup-test")));
    }

    #[test]
    fn value_congruent_to_table_entry_in_one_channel_is_rejected() {
        // v = 5 + m_0 is "5" in channel 0 but not in the other channels.
        let mut limbs = honest_limbs();
        limbs[0] = 5 + RNS_MODULI[0];
        let mut proof = prove(&limbs, &mut Transcript::new(b"logup-test"));
        proof.multiplicities[5] += 1;
        assert!(!verify(&limbs, &proof, &mut Transcript::new(b"logup-test")));
    }

    #[test]
    fn tampered_multiplicities_or_limbs_are_rejected() {
        let limbs = honest_limbs();
        let proof = prove(&limbs, &mut Transcript::new(b"logup-test"));
        let mut bad = proof.clone();
        bad.multiplicities[0] += 1;
        bad.multiplicities[1] -= 1.min(bad.multiplicities[1]);
        assert!(!verify(&limbs, &bad, &mut Transcript::new(b"logup-test")));

        let mut other = limbs.clone();
        other[1] ^= 1;
        assert!(!verify(&other, &proof, &mut Transcript::new(b"logup-test")));
    }

    #[test]
    fn batch_inverse_ext4_matches_single_inverse() {
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let vals: Vec<Extension4> = (1..50u32).map(|i| Extension4::new(i, 3 * i, 7, i * i)).collect();
            let inv = batch_inverse_ext4(&vals, ch).unwrap();
            for (v, w) in vals.iter().zip(&inv) {
                assert_eq!(v.mul(w, ch), Extension4::ONE);
                assert_eq!(*w, v.inverse(ch));
            }
        }
    }
}
