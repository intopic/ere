//! Fiat-Shamir transcript over Blake3.
//!
//! Every verifier challenge (LogUp `alpha`, FRI folding challenges, query indices) is derived by
//! hashing everything the prover has committed so far. A prover therefore has to fix its
//! commitments (trace, multiplicities, FRI layers) *before* it learns the challenge, which is
//! what makes LogUp and FRI sound in the non-interactive setting. The PDF (f.3, §2.2) assumes
//! "the same Fiat-Shamir challenger alpha"; v2.0 used a hard-coded constant instead.

//!
//! With `HashMode::Poseidon` the same API runs a Poseidon duplex sponge over BN254, so that a
//! BN254 circuit can re-derive every challenge: messages are absorbed as (tag, length, 16-byte
//! chunks) field elements, and each challenge takes the low 64 bits of one squeezed element
//! (reduced mod m for field challenges: statistical distance < 2^-32 per challenge).

use crate::hash::{poseidon_config, tag_fr, HashMode};
use crate::{Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};
use ark_bn254::Fr;
use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ff::{BigInteger, PrimeField};
use blake3::Hasher;

#[derive(Clone)]
pub struct Transcript {
    state: [u8; 32],
    counter: u64,
    sponge: Option<PoseidonSponge<Fr>>,
    p2: Option<Poseidon2Duplex>,
}

/// Duplex sponge over Poseidon2-KoalaBear: rate 8, capacity 8. Absorbing overwrites rate words
/// and permutes per block of 8; squeezing permutes and reads the rate.
#[derive(Clone)]
pub struct Poseidon2Duplex {
    pub state: [u32; crate::poseidon2::WIDTH],
    pending: Vec<u32>,
    out: Vec<u32>,
    /// Every permutation as (rate block written, full output state): what the sponge AIR proves.
    pub log: Vec<([u32; 8], [u32; crate::poseidon2::WIDTH])>,
}

impl Poseidon2Duplex {
    pub fn new(domain: &[u32]) -> Self {
        let mut d = Self { state: [0; crate::poseidon2::WIDTH], pending: Vec::new(), out: Vec::new(), log: Vec::new() };
        d.absorb(domain);
        d
    }
    pub fn absorb(&mut self, words: &[u32]) {
        self.out.clear();
        self.pending.extend_from_slice(words);
        while self.pending.len() >= 8 {
            let block: Vec<u32> = self.pending.drain(..8).collect();
            self.permute_with(&block);
        }
    }
    fn permute_with(&mut self, block: &[u32]) {
        self.state[..8].copy_from_slice(block);
        crate::poseidon2::permute(&mut self.state);
        self.log.push((block.try_into().unwrap(), self.state));
    }

    pub fn squeeze(&mut self) -> u32 {
        if self.out.is_empty() {
            // pad the pending block with its length marker and permute
            let mut block = std::mem::take(&mut self.pending);
            block.push(1);
            block.resize(8, 0);
            self.permute_with(&block);
            self.out = self.state[..8].iter().rev().copied().collect();
        }
        self.out.pop().unwrap()
    }
}

/// KoalaBear words a Poseidon2 transcript absorbs for one byte message: tag, length and the
/// data in 3-byte chunks (each < 2^24 < p).
pub fn poseidon2_message(label: &[u8], data: &[u8]) -> Vec<u32> {
    let mut v = vec![crate::hash::tag_word(label), data.len() as u32];
    v.extend(data.chunks(3).map(|c| c.iter().rev().fold(0u32, |a, &b| (a << 8) | b as u32)));
    v
}

/// Words for an absorbed digest: tag, the marker 2^30 (never a byte-message length here), 8 words.
pub fn poseidon2_digest(label: &[u8], d: &[u32; 8]) -> Vec<u32> {
    let mut v = vec![crate::hash::tag_word(label), 1 << 30];
    v.extend_from_slice(d);
    v
}

/// Field elements a Poseidon transcript absorbs for one message (shared with the circuit).
pub fn poseidon_message(label: &[u8], data: &[u8]) -> Vec<Fr> {
    let mut v = vec![tag_fr(label), Fr::from(data.len() as u64)];
    v.extend(data.chunks(16).map(Fr::from_le_bytes_mod_order));
    v
}

impl Transcript {
    /// Domain-separated start. Different protocols must use different labels.
    pub fn new(label: &[u8]) -> Self {
        Self::with_mode(label, HashMode::Blake3)
    }

    pub fn with_mode(label: &[u8], mode: HashMode) -> Self {
        let mut h = Hasher::new();
        h.update(b"SS-RAP/v2/transcript");
        h.update(&(label.len() as u64).to_le_bytes());
        h.update(label);
        let sponge = (mode == HashMode::Poseidon).then(|| {
            let mut s = PoseidonSponge::new(poseidon_config());
            s.absorb(&poseidon_message(b"SS-RAP/v2/transcript", label));
            s
        });
        let p2 = (mode == HashMode::Poseidon2).then(|| Poseidon2Duplex::new(&poseidon2_message(b"SS-RAP/v2/transcript", label)));
        Self { state: *h.finalize().as_bytes(), counter: 0, sponge, p2 }
    }

    /// The Poseidon2 duplex, when in that mode (the recursion layer reads its permutation log).
    pub fn poseidon2_duplex(&self) -> Option<&Poseidon2Duplex> {
        self.p2.as_ref()
    }

    pub fn mode(&self) -> HashMode {
        if self.sponge.is_some() {
            HashMode::Poseidon
        } else if self.p2.is_some() {
            HashMode::Poseidon2
        } else {
            HashMode::Blake3
        }
    }

    /// Absorbs a commitment root. Same as `absorb` except in Poseidon2 mode, where the digest
    /// goes in as its 8 field words (what the recursion AIR sees).
    pub fn absorb_digest(&mut self, label: &[u8], h: &crate::hash::Hash) {
        if let Some(d) = self.p2.as_mut() {
            d.absorb(&poseidon2_digest(label, &crate::hash::hash_to_words(h)));
            return;
        }
        self.absorb(label, h);
    }

    fn squeeze_u64(&mut self) -> Option<u64> {
        if let Some(d) = self.p2.as_mut() {
            // two words: w1 * p + w2 is uniform on [0, p^2), p^2 > 2^61
            let (w1, w2) = (d.squeeze() as u64, d.squeeze() as u64);
            return Some(w1 * crate::poseidon2::P as u64 + w2);
        }
        let s = self.sponge.as_mut()?;
        let x = s.squeeze_field_elements::<Fr>(1)[0];
        Some(u64::from_le_bytes(x.into_bigint().to_bytes_le()[..8].try_into().unwrap()))
    }

    /// Absorb a labelled message. Length-prefixed so that messages cannot be re-split.
    pub fn absorb(&mut self, label: &[u8], data: &[u8]) {
        if let Some(d) = self.p2.as_mut() {
            d.absorb(&poseidon2_message(label, data));
            return;
        }
        if let Some(s) = self.sponge.as_mut() {
            s.absorb(&poseidon_message(label, data));
            return;
        }
        let mut h = Hasher::new();
        h.update(&self.state);
        h.update(&(label.len() as u64).to_le_bytes());
        h.update(label);
        h.update(&(data.len() as u64).to_le_bytes());
        h.update(data);
        self.state = *h.finalize().as_bytes();
        self.counter = 0;
    }

    pub fn absorb_u32s(&mut self, label: &[u8], data: &[u32]) {
        let bytes: Vec<u8> = data.iter().flat_map(|x| x.to_le_bytes()).collect();
        self.absorb(label, &bytes);
    }

    fn squeeze_block(&mut self, label: &[u8]) -> [u8; 32] {
        let mut h = Hasher::new();
        h.update(&self.state);
        h.update(b"squeeze");
        h.update(label);
        h.update(&self.counter.to_le_bytes());
        self.counter += 1;
        *h.finalize().as_bytes()
    }

    /// Uniform element of F_m (rejection sampling on 32-bit words, no modulo bias).
    pub fn challenge_base(&mut self, label: &[u8], ch: usize) -> u32 {
        let m = RNS_MODULI[ch];
        if let Some(x) = self.squeeze_u64() {
            return (x % m as u64) as u32;
        }
        loop {
            let block = self.squeeze_block(label);
            for w in block.chunks_exact(4) {
                let v = u32::from_le_bytes([w[0], w[1], w[2], w[3]]) & 0x7fff_ffff; // m < 2^31
                if v < m {
                    return v;
                }
            }
        }
    }

    /// Uniform element of the quartic extension F_m[u]/(u^4 - beta) for channel `ch`.
    pub fn challenge_ext4(&mut self, label: &[u8], ch: usize) -> Extension4 {
        Extension4::new(
            self.challenge_base(label, ch),
            self.challenge_base(label, ch),
            self.challenge_base(label, ch),
            self.challenge_base(label, ch),
        )
    }

    /// One independent extension challenge per RNS channel.
    pub fn challenge_ext4_all(&mut self, label: &[u8]) -> [Extension4; DEFAULT_RNS_CHANNELS] {
        std::array::from_fn(|ch| self.challenge_ext4(label, ch))
    }

    /// Uniform index in [0, bound), bound a power of two (FRI query positions).
    pub fn challenge_index(&mut self, label: &[u8], bound: usize) -> usize {
        assert!(bound.is_power_of_two());
        if let Some(x) = self.squeeze_u64() {
            return x as usize & (bound - 1);
        }
        let block = self.squeeze_block(label);
        (u64::from_le_bytes(block[0..8].try_into().unwrap()) as usize) & (bound - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_and_binding() {
        let mut t1 = Transcript::new(b"test");
        let mut t2 = Transcript::new(b"test");
        t1.absorb(b"x", b"hello");
        t2.absorb(b"x", b"hello");
        assert_eq!(t1.challenge_ext4(b"a", 0), t2.challenge_ext4(b"a", 0));

        let mut t3 = Transcript::new(b"test");
        t3.absorb(b"x", b"hellp");
        let mut t4 = Transcript::new(b"test");
        t4.absorb(b"x", b"hello");
        assert_ne!(t3.challenge_ext4(b"a", 0), t4.challenge_ext4(b"a", 0));

        // Re-splitting the same bytes across messages must change the challenge.
        let mut t5 = Transcript::new(b"test");
        t5.absorb(b"x", b"hel");
        t5.absorb(b"x", b"lo");
        let mut t6 = Transcript::new(b"test");
        t6.absorb(b"x", b"hello");
        assert_ne!(t5.challenge_base(b"a", 1), t6.challenge_base(b"a", 1));
    }

    #[test]
    fn challenges_are_in_field() {
        let mut t = Transcript::new(b"range");
        for ch in 0..DEFAULT_RNS_CHANNELS {
            for _ in 0..100 {
                assert!(t.challenge_base(b"c", ch) < RNS_MODULI[ch]);
            }
        }
    }
}
