//! Poseidon2 over each of the five 31-bit RNS fields, width 16.
//!
//! This is the hash the recursion layer uses inside the STARK (docs/REKURSIONI.md): it is
//! native to the field of each lane, so a permutation costs a few hundred trace cells instead
//! of the thousands of bit operations Blake3 needs, and every lane can verify its own
//! commitments and challenges without leaving its field.
//!
//! Construction (Grassi, Khovratovich, Schofnegger, "Poseidon2", 2023):
//!   initial M_E, then 4 full rounds, 22 partial rounds, 4 full rounds.
//!   full round:    add 16 constants, x^d on every word, M_E
//!   partial round: add 1 constant to word 0, x^d on word 0, M_I
//!   M_E = circ(2 M4, M4, M4, M4) with the paper's M4; M_I = 1 1^T + diag(D).
//! The S-box degree d is the smallest of 3, 5, 7 with gcd(d, m - 1) = 1, so x^d is a
//! permutation: BabyBear 7, KoalaBear 3, the other three primes 5. The paper's bound for
//! 128-bit security with a 31-bit field and t = 16 is 8 full and at most 21 partial rounds
//! (d = 3); we use 22 for every field.
//! Round constants come from a Blake3 XOF (uniform mod m by rejection), and D is the first
//! vector found by a deterministic search for which the characteristic polynomial of M_I is
//! irreducible (the paper's sufficient condition against invariant subspaces); the tests
//! re-check both properties for every field.
//!
//! The functions without a channel argument are the KoalaBear instance (channel 1).

use crate::{DEFAULT_RNS_CHANNELS, KOALA_BEAR, RNS_MODULI};
use std::sync::OnceLock;

pub const P: u32 = KOALA_BEAR;
pub const KOALA: usize = 1;
pub const WIDTH: usize = 16;
pub const FULL_ROUNDS: usize = 8;
pub const PARTIAL_ROUNDS: usize = 22;
/// S-box degree per channel.
pub const SBOX_DEGREE: [u32; DEFAULT_RNS_CHANNELS] = [7, 3, 5, 5, 5];

const M4: [[u64; 4]; 4] = [[5, 7, 1, 3], [4, 6, 1, 1], [1, 3, 5, 7], [1, 1, 4, 6]];

#[inline]
fn add(a: u32, b: u32, m: u32) -> u32 {
    let s = a as u64 + b as u64;
    (if s >= m as u64 { s - m as u64 } else { s }) as u32
}

#[inline]
fn mul(a: u32, b: u32, m: u32) -> u32 {
    ((a as u64 * b as u64) % m as u64) as u32
}

#[inline]
pub fn sbox_ch(x: u32, ch: usize) -> u32 {
    let m = RNS_MODULI[ch];
    let x2 = mul(x, x, m);
    match SBOX_DEGREE[ch] {
        3 => mul(x2, x, m),
        5 => mul(mul(x2, x2, m), x, m),
        7 => mul(mul(mul(x2, x2, m), x2, m), x, m),
        _ => unreachable!(),
    }
}

#[inline]
pub fn sbox(x: u32) -> u32 {
    sbox_ch(x, KOALA)
}

pub struct Params {
    pub full_rc: [[u32; WIDTH]; FULL_ROUNDS],
    pub partial_rc: [u32; PARTIAL_ROUNDS],
    /// Diagonal of M_I - 1 1^T.
    pub diag: [u32; WIDTH],
}

fn xof_elements(seed: &[u8], n: usize, m: u32) -> Vec<u32> {
    let mut reader = blake3::Hasher::new().update(seed).finalize_xof();
    let mut out = Vec::with_capacity(n);
    let mut buf = [0u8; 4];
    while out.len() < n {
        reader.fill(&mut buf);
        let v = u32::from_le_bytes(buf) & 0x7fff_ffff;
        if v < m {
            out.push(v);
        }
    }
    out
}

pub fn params_ch(ch: usize) -> &'static Params {
    static PARAMS: OnceLock<Vec<Params>> = OnceLock::new();
    &PARAMS.get_or_init(|| {
        (0..DEFAULT_RNS_CHANNELS)
            .map(|ch| {
                let m = RNS_MODULI[ch];
                // KoalaBear keeps the seed it was introduced with.
                let seed = if ch == KOALA { b"SS-RAP/v2/poseidon2/koalabear/16/rc".to_vec() } else { format!("SS-RAP/v2/poseidon2/rns{ch}/16/rc").into_bytes() };
                let rc = xof_elements(&seed, FULL_ROUNDS * WIDTH + PARTIAL_ROUNDS, m);
                let full_rc = std::array::from_fn(|r| std::array::from_fn(|i| rc[r * WIDTH + i]));
                let partial_rc = std::array::from_fn(|r| rc[FULL_ROUNDS * WIDTH + r]);
                Params { full_rc, partial_rc, diag: find_diag(m) }
            })
            .collect()
    })[ch]
}

pub fn params() -> &'static Params {
    params_ch(KOALA)
}

/// Deterministic search for a small diagonal with an irreducible characteristic polynomial.
fn find_diag(m: u32) -> [u32; WIDTH] {
    let mut seed = 0u64;
    loop {
        let mut d = [0u32; WIDTH];
        let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x5151;
        for x in d.iter_mut() {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let small = ((s >> 33) % 64) as u32 + 1; // 1..64
            *x = if (s >> 20) & 1 == 1 { m - small } else { small };
        }
        if internal_matrix_ok(&d, m as u64) {
            return d;
        }
        seed += 1;
    }
}

/// M_E applied in place.
pub fn external_linear_ch(state: &mut [u32; WIDTH], ch: usize) {
    let m = RNS_MODULI[ch] as u64;
    let mut y = [0u64; WIDTH];
    let mut sums = [0u64; 4];
    for c in 0..4 {
        for r in 0..4 {
            let mut acc = 0u64;
            for k in 0..4 {
                acc += M4[r][k] * state[4 * c + k] as u64;
            }
            y[4 * c + r] = acc % m;
            sums[r] += y[4 * c + r];
        }
    }
    for c in 0..4 {
        for r in 0..4 {
            state[4 * c + r] = ((y[4 * c + r] + sums[r]) % m) as u32;
        }
    }
}

pub fn external_linear(state: &mut [u32; WIDTH]) {
    external_linear_ch(state, KOALA)
}

/// M_I = 1 1^T + diag(D) applied in place.
pub fn internal_linear_ch(state: &mut [u32; WIDTH], diag: &[u32; WIDTH], ch: usize) {
    let m = RNS_MODULI[ch] as u64;
    let sum = state.iter().map(|&x| x as u64).sum::<u64>() % m;
    for i in 0..WIDTH {
        state[i] = ((sum + diag[i] as u64 * state[i] as u64) % m) as u32;
    }
}

pub fn internal_linear(state: &mut [u32; WIDTH], diag: &[u32; WIDTH]) {
    internal_linear_ch(state, diag, KOALA)
}

pub fn permute_ch(state: &mut [u32; WIDTH], ch: usize) {
    let m = RNS_MODULI[ch];
    let prm = params_ch(ch);
    external_linear_ch(state, ch);
    for r in 0..FULL_ROUNDS / 2 {
        full_round(state, &prm.full_rc[r], ch);
    }
    for r in 0..PARTIAL_ROUNDS {
        state[0] = sbox_ch(add(state[0], prm.partial_rc[r], m), ch);
        internal_linear_ch(state, &prm.diag, ch);
    }
    for r in FULL_ROUNDS / 2..FULL_ROUNDS {
        full_round(state, &prm.full_rc[r], ch);
    }
}

pub fn permute(state: &mut [u32; WIDTH]) {
    permute_ch(state, KOALA)
}

fn full_round(state: &mut [u32; WIDTH], rc: &[u32; WIDTH], ch: usize) {
    let m = RNS_MODULI[ch];
    for i in 0..WIDTH {
        state[i] = sbox_ch(add(state[i], rc[i], m), ch);
    }
    external_linear_ch(state, ch);
}

/// 2-to-1 compression of 8-word digests: permute(l || r), keep the first 8 words, add l
/// (feed-forward, so the compression is not invertible).
pub fn compress_ch(l: &[u32; 8], r: &[u32; 8], ch: usize) -> [u32; 8] {
    let m = RNS_MODULI[ch];
    let mut s = [0u32; WIDTH];
    s[..8].copy_from_slice(l);
    s[8..].copy_from_slice(r);
    permute_ch(&mut s, ch);
    std::array::from_fn(|i| add(s[i], l[i], m))
}

pub fn compress(l: &[u32; 8], r: &[u32; 8]) -> [u32; 8] {
    compress_ch(l, r, KOALA)
}

/// Sponge hash (rate 8, capacity 8) of a sequence of field elements, length-separated.
pub fn hash_ch(values: &[u32], ch: usize) -> [u32; 8] {
    let m = RNS_MODULI[ch];
    let mut s = [0u32; WIDTH];
    s[15] = values.len() as u32 % m;
    for chunk in values.chunks(8) {
        for (i, &v) in chunk.iter().enumerate() {
            s[i] = add(s[i], v % m, m);
        }
        permute_ch(&mut s, ch);
    }
    if values.is_empty() {
        permute_ch(&mut s, ch);
    }
    std::array::from_fn(|i| s[i])
}

pub fn hash(values: &[u32]) -> [u32; 8] {
    hash_ch(values, KOALA)
}

// ---- parameter checks: characteristic polynomial of M_I and irreducibility over F_p

fn pow_mod(mut b: u64, mut e: u64, p: u64) -> u64 {
    let mut r = 1u64;
    b %= p;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % p;
        }
        b = b * b % p;
        e >>= 1;
    }
    r
}

fn inv(a: u64, p: u64) -> u64 {
    pow_mod(a, p - 2, p)
}

fn det(mut a: Vec<Vec<u64>>, p: u64) -> u64 {
    let n = a.len();
    let mut d = 1u64;
    for c in 0..n {
        let Some(piv) = (c..n).find(|&r| a[r][c] != 0) else { return 0 };
        if piv != c {
            a.swap(piv, c);
            d = (p - d) % p;
        }
        d = d * a[c][c] % p;
        let iv = inv(a[c][c], p);
        for r in c + 1..n {
            let f = a[r][c] * iv % p;
            if f != 0 {
                for k in c..n {
                    a[r][k] = (a[r][k] + p - f * a[c][k] % p) % p;
                }
            }
        }
    }
    d
}

/// Characteristic polynomial det(xI - M) (coefficients, low degree first), by interpolation.
fn char_poly(m: &[Vec<u64>], p: u64) -> Vec<u64> {
    let n = m.len();
    let xs: Vec<u64> = (0..=n as u64).collect();
    let ys: Vec<u64> = xs
        .iter()
        .map(|&x| {
            let a: Vec<Vec<u64>> = (0..n).map(|i| (0..n).map(|j| ((if i == j { x } else { 0 }) + p - m[i][j]) % p).collect()).collect();
            det(a, p)
        })
        .collect();
    // Lagrange interpolation into coefficient form.
    let mut coeffs = vec![0u64; n + 1];
    for i in 0..=n {
        let mut basis = vec![1u64];
        let mut denom = 1u64;
        for j in 0..=n {
            if i == j {
                continue;
            }
            let mut nb = vec![0u64; basis.len() + 1];
            for (k, &c) in basis.iter().enumerate() {
                nb[k + 1] = (nb[k + 1] + c) % p;
                nb[k] = (nb[k] + p - c * xs[j] % p) % p;
            }
            basis = nb;
            denom = denom * ((xs[i] + p - xs[j]) % p) % p;
        }
        let f = ys[i] * inv(denom, p) % p;
        for k in 0..=n {
            coeffs[k] = (coeffs[k] + basis[k] * f) % p;
        }
    }
    coeffs
}

fn poly_mulmod(a: &[u64], b: &[u64], f: &[u64], p: u64) -> Vec<u64> {
    let n = f.len() - 1; // f monic, degree n
    let mut prod = vec![0u64; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            prod[i + j] = (prod[i + j] + x * y) % p;
        }
    }
    for k in (n..prod.len()).rev() {
        let c = prod[k];
        if c != 0 {
            for i in 0..n {
                prod[k - n + i] = (prod[k - n + i] + p - c * f[i] % p) % p;
            }
            prod[k] = 0;
        }
    }
    prod.truncate(n);
    prod.resize(n, 0);
    prod
}

fn frobenius(g: &[u64], f: &[u64], p: u64) -> Vec<u64> {
    // g^p mod f
    let mut result = vec![0u64; f.len() - 1];
    result[0] = 1;
    let mut base = g.to_vec();
    let mut e = p;
    while e > 0 {
        if e & 1 == 1 {
            result = poly_mulmod(&result, &base, f, p);
        }
        base = poly_mulmod(&base, &base, f, p);
        e >>= 1;
    }
    result
}

fn poly_gcd_is_one(mut a: Vec<u64>, mut b: Vec<u64>, p: u64) -> bool {
    let trim = |v: &mut Vec<u64>| {
        while v.len() > 1 && *v.last().unwrap() == 0 {
            v.pop();
        }
    };
    trim(&mut a);
    trim(&mut b);
    while !(b.len() == 1 && b[0] == 0) {
        // a mod b
        let lb = inv(*b.last().unwrap(), p);
        while a.len() >= b.len() && !(a.len() == 1 && a[0] == 0) {
            let c = a.last().unwrap() * lb % p;
            let sh = a.len() - b.len();
            for i in 0..b.len() {
                a[sh + i] = (a[sh + i] + p - c * b[i] % p) % p;
            }
            a.pop();
            trim(&mut a);
            if a.is_empty() {
                a.push(0);
            }
        }
        std::mem::swap(&mut a, &mut b);
    }
    a.len() == 1 && a[0] != 0
}

/// Rabin's test for a monic polynomial f of degree 16 = 2^4: irreducible iff
/// x^(p^16) = x mod f and gcd(x^(p^8) - x, f) = 1.
fn irreducible_deg16(f: &[u64], p: u64) -> bool {
    let n = f.len() - 1;
    assert_eq!(n, 16);
    let mut x = vec![0u64; n];
    x[1] = 1;
    let mut g = x.clone();
    let mut at8 = Vec::new();
    for k in 1..=16 {
        g = frobenius(&g, f, p);
        if k == 8 {
            at8 = g.clone();
        }
    }
    if g != x {
        return false;
    }
    let mut h = at8;
    h[1] = (h[1] + p - 1) % p;
    poly_gcd_is_one(f.to_vec(), h, p)
}

fn internal_matrix_ok(d: &[u32; WIDTH], p: u64) -> bool {
    let m: Vec<Vec<u64>> = (0..WIDTH).map(|i| (0..WIDTH).map(|j| 1 + if i == j { d[i] as u64 } else { 0 }).collect()).collect();
    if det(m.clone(), p) == 0 {
        return false;
    }
    irreducible_deg16(&char_poly(&m, p), p)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sbox_is_a_permutation_exponent() {
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let d = SBOX_DEGREE[ch];
            assert_ne!((RNS_MODULI[ch] - 1) % d, 0, "channel {ch}");
            // and it is the smallest odd choice
            for smaller in (3..d).step_by(2) {
                assert_eq!((RNS_MODULI[ch] - 1) % smaller, 0, "channel {ch} could use {smaller}");
            }
        }
    }

    #[test]
    fn internal_matrix_has_irreducible_char_poly() {
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let p = RNS_MODULI[ch] as u64;
            assert!(internal_matrix_ok(&params_ch(ch).diag, p), "channel {ch}");
            // Sanity of the test itself: the all-ones-plus-identity matrix is not irreducible.
            assert!(!internal_matrix_ok(&[1; WIDTH], p));
        }
    }

    #[test]
    fn external_matrix_is_invertible() {
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let m: Vec<Vec<u64>> = (0..WIDTH)
                .map(|i| {
                    let mut e = [0u32; WIDTH];
                    e[i] = 1;
                    external_linear_ch(&mut e, ch);
                    e.iter().map(|&x| x as u64).collect()
                })
                .collect();
            assert_ne!(det(m, RNS_MODULI[ch] as u64), 0, "channel {ch}");
        }
    }

    #[test]
    fn every_channel_permutation_diffuses() {
        for ch in 0..DEFAULT_RNS_CHANNELS {
            let (mut a, mut b) = ([0u32; WIDTH], [0u32; WIDTH]);
            b[3] = 1;
            permute_ch(&mut a, ch);
            permute_ch(&mut b, ch);
            assert!(a.iter().zip(&b).all(|(x, y)| x != y), "channel {ch}");
        }
    }

    #[test]
    fn permutation_is_deterministic_and_diffuses() {
        let mut a = [0u32; WIDTH];
        let mut b = [0u32; WIDTH];
        b[7] = 1;
        permute(&mut a);
        permute(&mut b);
        assert!(a.iter().zip(&b).all(|(x, y)| x != y), "one input word changes every output word");
        let mut a2 = [0u32; WIDTH];
        permute(&mut a2);
        assert_eq!(a, a2);
    }

    #[test]
    fn hash_is_length_separated() {
        assert_ne!(hash(&[1, 2, 3]), hash(&[1, 2, 3, 0]));
        assert_ne!(hash(&[]), hash(&[0]));
        assert_ne!(compress(&[1; 8], &[2; 8]), compress(&[2; 8], &[1; 8]));
    }
}

#[cfg(test)]
mod speed {
    #[test]
    fn report_params_and_speed() {
        let p = super::params();
        eprintln!("diag = {:?}", p.diag.map(|x| if x > super::P / 2 { -((super::P - x) as i64) } else { x as i64 }));
        let t = std::time::Instant::now();
        let mut s = [1u32; super::WIDTH];
        for _ in 0..100_000 {
            super::permute(&mut s);
        }
        eprintln!("permutation: {:.2} us", t.elapsed().as_secs_f64() * 10.0);
    }
}
