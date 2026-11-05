//! Radix-2 NTT per RNS channel, using the PDF's primitive 2^24-th roots (f.3, §2.1).
//! All reductions use Barrett (`mul_mod_channel`), no `%` in the butterflies.

use crate::{add_mod, mod_inv_single, mul_mod_channel, sub_mod, RNS_MODULI, TWO_ADIC_OMEGA_24};

pub const MAX_LOG_N: u32 = 24;

/// Primitive n-th root of unity in channel `ch`, n a power of two <= 2^24.
pub fn root_of_unity(n: usize, ch: usize) -> u32 {
    assert!(n.is_power_of_two() && n.trailing_zeros() <= MAX_LOG_N);
    let mut w = TWO_ADIC_OMEGA_24[ch];
    for _ in n.trailing_zeros()..MAX_LOG_N {
        w = mul_mod_channel(w, w, ch);
    }
    w
}

fn bit_reverse(v: &mut [u32]) {
    let n = v.len();
    let bits = n.trailing_zeros();
    if bits == 0 {
        return;
    }
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - bits);
        if i < j {
            v.swap(i, j);
        }
    }
}

/// In-place forward NTT: coefficients -> evaluations at w^0, w^1, ..., w^(n-1) (natural order).
pub fn ntt(v: &mut [u32], ch: usize) {
    let n = v.len();
    assert!(n.is_power_of_two());
    let m = RNS_MODULI[ch];
    bit_reverse(v);
    let mut len = 2;
    while len <= n {
        let w_len = root_of_unity(len, ch);
        // twiddles for this stage, computed once
        let half = len / 2;
        let mut tw = Vec::with_capacity(half);
        let mut w = 1u32;
        for _ in 0..half {
            tw.push(w);
            w = mul_mod_channel(w, w_len, ch);
        }
        for start in (0..n).step_by(len) {
            for j in 0..half {
                let u = v[start + j];
                let t = mul_mod_channel(v[start + j + half], tw[j], ch);
                v[start + j] = add_mod(u, t, m);
                v[start + j + half] = sub_mod(u, t, m);
            }
        }
        len <<= 1;
    }
}

/// In-place inverse NTT: evaluations (natural order) -> coefficients.
pub fn intt(v: &mut [u32], ch: usize) {
    let n = v.len();
    ntt(v, ch);
    // evaluations at w^{-i}: reverse indices 1..n
    v[1..].reverse();
    let n_inv = mod_inv_single(n as u32 % RNS_MODULI[ch], RNS_MODULI[ch]);
    for x in v.iter_mut() {
        *x = mul_mod_channel(*x, n_inv, ch);
    }
}

/// Low-degree extension: evaluate a polynomial of degree < coeffs.len() on a domain `blowup`
/// times larger.
pub fn lde(coeffs: &[u32], blowup: usize, ch: usize) -> Vec<u32> {
    let mut v = coeffs.to_vec();
    v.resize(coeffs.len() * blowup, 0);
    ntt(&mut v, ch);
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DEFAULT_RNS_CHANNELS;

    fn eval(coeffs: &[u32], x: u32, ch: usize) -> u32 {
        let m = RNS_MODULI[ch];
        coeffs.iter().rev().fold(0, |acc, &c| add_mod(mul_mod_channel(acc, x, ch), c, m))
    }

    #[test]
    fn ntt_matches_naive_evaluation_and_inverts() {
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let n = 64;
            let coeffs: Vec<u32> = (0..n as u32).map(|i| (i * 7919 + 13) % RNS_MODULI[ch]).collect();
            let mut v = coeffs.clone();
            ntt(&mut v, ch);
            let w = root_of_unity(n, ch);
            let mut x = 1;
            for i in 0..n {
                assert_eq!(v[i], eval(&coeffs, x, ch), "ch {ch} i {i}");
                x = mul_mod_channel(x, w, ch);
            }
            intt(&mut v, ch);
            assert_eq!(v, coeffs);
        }
    }

    #[test]
    fn roots_have_exact_order() {
        for ch in 0..DEFAULT_RNS_CHANNELS {
            for log_n in [1u32, 4, 10, 24] {
                let n = 1usize << log_n;
                let w = root_of_unity(n, ch);
                let mut x = w;
                for _ in 0..log_n - 1 {
                    x = mul_mod_channel(x, x, ch);
                }
                assert_eq!(x, RNS_MODULI[ch] - 1, "w^(n/2) must be -1");
            }
        }
    }
}
