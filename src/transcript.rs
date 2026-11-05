//! Fiat-Shamir transcript over Blake3.
//!
//! Every verifier challenge (LogUp `alpha`, FRI folding challenges, query indices) is derived by
//! hashing everything the prover has committed so far. A prover therefore has to fix its
//! commitments (trace, multiplicities, FRI layers) *before* it learns the challenge, which is
//! what makes LogUp and FRI sound in the non-interactive setting. The PDF (f.3, §2.2) assumes
//! "the same Fiat-Shamir challenger alpha"; v2.0 used a hard-coded constant instead.

use crate::{Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};
use blake3::Hasher;

#[derive(Clone)]
pub struct Transcript {
    state: [u8; 32],
    counter: u64,
}

impl Transcript {
    /// Domain-separated start. Different protocols must use different labels.
    pub fn new(label: &[u8]) -> Self {
        let mut h = Hasher::new();
        h.update(b"SS-RAP/v2/transcript");
        h.update(&(label.len() as u64).to_le_bytes());
        h.update(label);
        Self { state: *h.finalize().as_bytes(), counter: 0 }
    }

    /// Absorb a labelled message. Length-prefixed so that messages cannot be re-split.
    pub fn absorb(&mut self, label: &[u8], data: &[u8]) {
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
