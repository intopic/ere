//! Plonky3's `MultiField32Challenger<BabyBear, Bn254, Poseidon2Bn254<3>, 3, 2>` in R1CS (and
//! natively). It replays a Fiat-Shamir schedule (`Op`s): the order of observations and samples
//! is fixed by the proof shape, which `ss_rap_p3::record` records from Plonky3's own verifier.
//!
//! The state machine (as `multi_field_challenger.rs` and `duplex_challenger.rs`):
//! - observe(v): pushes v into a buffer; at 16 values (8 per BN254 word, RATE 2) it flushes;
//! - flush: packs the buffer 8 values per word (radix 2^31, little-endian, no shift), writes
//!   the words into the rate, zeroes the rest of the rate, adds the value count to the capacity
//!   element, permutes, and the rate becomes the output buffer;
//! - observe(digest): flush, then absorb the digest as one word with count 1;
//! - sample: flush; if nothing is left to squeeze, permute when the output is empty (duplexing
//!   without input), then split every output word into 7 base-p digits; values are popped from
//!   the end;
//! - sample_bits(b): the low b bits of a sampled value.

use super::poseidon2_var::{permute, permute_var};
use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use num_bigint::BigUint;

pub const P: u64 = 2013265921;
/// BabyBear values per absorbed word (`max_absorb_injective_limbs`).
pub const ABSORB: usize = 8;
/// Base-p digits per squeezed word (`squeeze_field_order_num_limbs`).
pub const SQUEEZE: usize = 7;
const RATE: usize = 2;

/// One step of the schedule, with the values the circuit absorbs.
#[derive(Clone, Debug)]
pub enum Step<V> {
    Observe(V),
    ObserveDigest(V),
    Sample,
    SampleBits(usize),
}

// ---------------------------------------------------------------------------------------------
// native
// ---------------------------------------------------------------------------------------------

#[derive(Clone)]
pub struct Native {
    state: [Fr; 3],
    output: Vec<Fr>,
    fbuf: Vec<u32>,
    squeeze: Vec<u32>,
}

impl Default for Native {
    fn default() -> Self {
        Self { state: [Fr::from(0u64); 3], output: vec![], fbuf: vec![], squeeze: vec![] }
    }
}

impl Native {
    fn absorb_with_tag(&mut self, words: &[Fr], tag: u64) {
        for i in 0..RATE {
            self.state[i] = words.get(i).copied().unwrap_or(Fr::from(0u64));
        }
        self.state[RATE] += Fr::from(tag);
        self.state = permute(self.state);
        self.output = self.state[..RATE].to_vec();
    }
    fn flush(&mut self) {
        if self.fbuf.is_empty() {
            return;
        }
        let base = Fr::from(1u64 << 31);
        let words: Vec<Fr> = self.fbuf.chunks(ABSORB).map(|c| c.iter().rev().fold(Fr::from(0u64), |a, &v| a * base + Fr::from(v as u64))).collect();
        let n = self.fbuf.len() as u64;
        self.absorb_with_tag(&words, n);
        self.fbuf.clear();
        self.squeeze.clear();
    }
    pub fn observe(&mut self, v: u32) {
        self.output.clear();
        self.squeeze.clear();
        self.fbuf.push(v);
        if self.fbuf.len() == ABSORB * RATE {
            self.flush();
        }
    }
    pub fn observe_digest(&mut self, d: Fr) {
        self.output.clear();
        self.squeeze.clear();
        self.flush();
        self.absorb_with_tag(&[d], 1);
        self.squeeze.clear();
    }
    pub fn sample(&mut self) -> u32 {
        self.flush();
        if self.squeeze.is_empty() {
            if self.output.is_empty() {
                self.state = permute(self.state);
                self.output = self.state[..RATE].to_vec();
            }
            for w in self.output.drain(..) {
                let mut rem: BigUint = w.into();
                for _ in 0..SQUEEZE {
                    self.squeeze.push((&rem % P).try_into().unwrap());
                    rem /= P;
                }
            }
        }
        self.squeeze.pop().unwrap()
    }
    pub fn sample_bits(&mut self, bits: usize) -> usize {
        (self.sample() as usize) & ((1 << bits) - 1)
    }
}

// ---------------------------------------------------------------------------------------------
// in circuit
// ---------------------------------------------------------------------------------------------

/// A sampled BabyBear value with its 31 bits (LSB first).
#[derive(Clone)]
pub struct SampledVar {
    pub value: FpVar<Fr>,
    pub bits: Vec<Boolean<Fr>>,
}

pub struct ChallengerVar {
    cs: ConstraintSystemRef<Fr>,
    state: [FpVar<Fr>; 3],
    output: Vec<FpVar<Fr>>,
    fbuf: Vec<FpVar<Fr>>,
    squeeze: Vec<SampledVar>,
}

/// A canonical BabyBear value (< p) from its 31 witnessed bits.
fn babybear_from_bits(bits: &[Boolean<Fr>]) -> Result<FpVar<Fr>, SynthesisError> {
    assert_eq!(bits.len(), 31);
    // p - 1 = 15 * 2^27: value <= p - 1 iff (bits 27..31 all set) => bits 0..27 are zero.
    let top = &(&(&bits[27] & &bits[28]) & &bits[29]) & &bits[30];
    let low = Boolean::le_bits_to_fp(&bits[..27])?;
    (FpVar::from(top) * &low).enforce_equal(&FpVar::zero())?;
    Boolean::le_bits_to_fp(bits)
}

impl ChallengerVar {
    pub fn new(cs: ConstraintSystemRef<Fr>) -> Self {
        Self { cs, state: std::array::from_fn(|_| FpVar::zero()), output: vec![], fbuf: vec![], squeeze: vec![] }
    }
    fn absorb_with_tag(&mut self, words: &[FpVar<Fr>], tag: u64) -> Result<(), SynthesisError> {
        for i in 0..RATE {
            self.state[i] = words.get(i).cloned().unwrap_or(FpVar::zero());
        }
        self.state[RATE] += Fr::from(tag);
        self.state = permute_var(self.state.clone())?;
        self.output = self.state[..RATE].to_vec();
        Ok(())
    }
    fn flush(&mut self) -> Result<(), SynthesisError> {
        if self.fbuf.is_empty() {
            return Ok(());
        }
        let base = Fr::from(1u64 << 31);
        let words: Vec<FpVar<Fr>> = self.fbuf.chunks(ABSORB).map(|c| c.iter().rev().fold(FpVar::zero(), |a, v| a * base + v)).collect();
        let n = self.fbuf.len() as u64;
        self.absorb_with_tag(&words, n)?;
        self.fbuf.clear();
        self.squeeze.clear();
        Ok(())
    }
    /// `v` must be a canonical BabyBear value (the caller range-checks what it absorbs).
    pub fn observe(&mut self, v: &FpVar<Fr>) -> Result<(), SynthesisError> {
        self.output.clear();
        self.squeeze.clear();
        self.fbuf.push(v.clone());
        if self.fbuf.len() == ABSORB * RATE {
            self.flush()?;
        }
        Ok(())
    }
    pub fn observe_digest(&mut self, d: &FpVar<Fr>) -> Result<(), SynthesisError> {
        self.output.clear();
        self.squeeze.clear();
        self.flush()?;
        self.absorb_with_tag(std::slice::from_ref(d), 1)?;
        self.squeeze.clear();
        Ok(())
    }
    /// w = sum_i l_i p^i + hi p^7 with every l_i < p and the integer < r (unique digits).
    fn split(&self, w: &FpVar<Fr>) -> Result<Vec<SampledVar>, SynthesisError> {
        let r: BigUint = Fr::MODULUS.into();
        let pk = BigUint::from(P).pow(SQUEEZE as u32);
        let h_max = (&r - 1u32) / &pk; // largest hi
        let c = &r - &h_max * &pk; // when hi = h_max, low must be < c
        let wv: Option<BigUint> = w.value().ok().map(|x| x.into());
        let mut limbs = Vec::with_capacity(SQUEEZE);
        let mut low = FpVar::zero();
        let mut pw = Fr::from(1u64);
        for i in 0..SQUEEZE {
            let li: Option<u64> = wv.as_ref().map(|w| ((w / BigUint::from(P).pow(i as u32)) % P).try_into().unwrap());
            let bits: Vec<Boolean<Fr>> = (0..31).map(|b| Boolean::new_witness(self.cs.clone(), || li.map(|l| (l >> b) & 1 == 1).ok_or(SynthesisError::AssignmentMissing))).collect::<Result<_, _>>()?;
            let value = babybear_from_bits(&bits)?;
            low += &value * pw;
            pw *= Fr::from(P);
            limbs.push(SampledVar { value, bits });
        }
        let hb = h_max.bits() as usize;
        let hi_val: Option<BigUint> = wv.as_ref().map(|w| w / &pk);
        let hi_bits: Vec<Boolean<Fr>> = (0..hb).map(|b| Boolean::new_witness(self.cs.clone(), || hi_val.as_ref().map(|h| h.bit(b as u64)).ok_or(SynthesisError::AssignmentMissing))).collect::<Result<_, _>>()?;
        let hi = Boolean::le_bits_to_fp(&hi_bits)?;
        // hi <= h_max
        let hm = FpVar::constant(Fr::from(h_max.clone()));
        range_bits(&self.cs, &(&hm - &hi), hb)?;
        (&low + &hi * Fr::from(pk.clone())).enforce_equal(w)?;
        // if hi == h_max then low < c
        let is_max = hi.is_eq(&hm)?;
        let cm1 = FpVar::constant(Fr::from(&c - 1u32));
        let t = FpVar::conditionally_select(&is_max, &(&cm1 - &low), &low)?;
        let low_bits = (pk.bits() as usize).max(c.bits() as usize);
        range_bits(&self.cs, &t, low_bits)?;
        Ok(limbs)
    }
    pub fn sample(&mut self) -> Result<SampledVar, SynthesisError> {
        self.flush()?;
        if self.squeeze.is_empty() {
            if self.output.is_empty() {
                self.state = permute_var(self.state.clone())?;
                self.output = self.state[..RATE].to_vec();
            }
            let out = std::mem::take(&mut self.output);
            for w in &out {
                let limbs = self.split(w)?;
                self.squeeze.extend(limbs);
            }
        }
        Ok(self.squeeze.pop().unwrap())
    }
    /// The low `bits` bits of a sample (LSB first).
    pub fn sample_bits(&mut self, bits: usize) -> Result<Vec<Boolean<Fr>>, SynthesisError> {
        Ok(self.sample()?.bits[..bits].to_vec())
    }
}

use ark_r1cs_std::select::CondSelectGadget;

/// Enforces 0 <= x < 2^n.
pub fn range_bits(cs: &ConstraintSystemRef<Fr>, x: &FpVar<Fr>, n: usize) -> Result<Vec<Boolean<Fr>>, SynthesisError> {
    let v = x.value().ok().map(|v| v.into_bigint().to_bits_le());
    let bits: Vec<Boolean<Fr>> = (0..n).map(|i| Boolean::new_witness(cs.clone(), || v.as_ref().map(|b| b[i]).ok_or(SynthesisError::AssignmentMissing))).collect::<Result<_, _>>()?;
    Boolean::le_bits_to_fp(&bits)?.enforce_equal(x)?;
    Ok(bits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeField as _;
    use ss_rap_p3::record::Op;

    fn to_fr(x: p3_bn254::Bn254) -> Fr {
        Fr::from(BigUint::from_bytes_le(&x.as_canonical_biguint().to_bytes_le()))
    }

    #[test]
    fn replays_plonky3_verifier_transcript() {
        assert_eq!(p3_field::max_absorb_injective_limbs::<BabyBear, p3_bn254::Bn254>(), ABSORB);
        assert_eq!(p3_field::squeeze_field_order_num_limbs::<p3_bn254::Bn254, BabyBear>(), SQUEEZE);
        let (st, traces) = ss_rap_p3::state::tests_case(600, 8);
        let p = ss_rap_p3::state::Params { log_rows: 8, log_blowup: 1, queries: 20, budget: 3, query_pow: 0 };
        let proof = ss_rap_p3::record::prove_one(&st, &traces, &p);
        let (ok, ops) = ss_rap_p3::record::verify_one(&st, &proof, &p);
        assert!(ok);
        // native replay
        let mut n = Native::default();
        for op in &ops {
            match *op {
                Op::Observe(v) => n.observe(v),
                Op::ObserveDigest(d) => n.observe_digest(to_fr(d)),
                Op::Sample(v) => assert_eq!(n.sample(), v),
                Op::SampleBits(b, v) => assert_eq!(n.sample_bits(b), v),
            }
        }
        // in-circuit replay
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut c = ChallengerVar::new(cs.clone());
        let mut samples = 0;
        for op in &ops {
            match *op {
                Op::Observe(v) => c.observe(&FpVar::new_witness(cs.clone(), || Ok(Fr::from(v as u64))).unwrap()).unwrap(),
                Op::ObserveDigest(d) => c.observe_digest(&FpVar::new_witness(cs.clone(), || Ok(to_fr(d))).unwrap()).unwrap(),
                Op::Sample(v) => {
                    assert_eq!(c.sample().unwrap().value.value().unwrap(), Fr::from(v as u64));
                    samples += 1;
                }
                Op::SampleBits(b, v) => {
                    let bits = c.sample_bits(b).unwrap();
                    let got = bits.iter().enumerate().map(|(i, x)| (x.value().unwrap() as usize) << i).sum::<usize>();
                    assert_eq!(got, v);
                    samples += 1;
                }
            }
        }
        assert!(cs.is_satisfied().unwrap());
        eprintln!("challenger replay: {} ops, {} samples, {} constraints", ops.len(), samples, cs.num_constraints());
    }
}
