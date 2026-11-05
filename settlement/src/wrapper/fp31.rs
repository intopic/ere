//! Arithmetic of F_m (m one of the five 31-bit RNS primes) and F_m^4 inside a BN254 circuit.
//!
//! A value is a native variable v with a known integer bound B (0 <= v < B < r_BN254). It
//! represents v mod m. Addition and multiplication are native (no constraint for addition, one
//! for multiplication) as long as the bound stays below 2^240; `reduce` then brings it back
//! below 2^31 with one witness quotient, i.e. v = q*m + rem with q, rem range-checked.
//! Equality is only ever needed as "x = 0 mod m", which costs one quotient witness.

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
use ss_rap_v2::{EXTENSION_BETA, RNS_MODULI};

const MAX_BOUND_BITS: u64 = 240;

fn to_big(x: &Fr) -> BigUint {
    BigUint::from_bytes_le(&x.into_bigint().to_bytes_le())
}

fn from_big(x: &BigUint) -> Fr {
    Fr::from_le_bytes_mod_order(&x.to_bytes_le())
}

/// Allocates a witness of `bits` bits and returns it as a field variable (n + 1 constraints).
pub fn range_witness(cs: &ConstraintSystemRef<Fr>, value: Option<BigUint>, bits: u64) -> Result<FpVar<Fr>, SynthesisError> {
    let mut bs = Vec::with_capacity(bits as usize);
    for i in 0..bits {
        bs.push(Boolean::new_witness(cs.clone(), || value.as_ref().map(|v| v.bit(i)).ok_or(SynthesisError::AssignmentMissing))?);
    }
    Boolean::le_bits_to_fp(&bs)
}

#[derive(Clone)]
pub struct M31 {
    pub v: FpVar<Fr>,
    pub bound: BigUint,
    pub ch: usize,
}

impl M31 {
    pub fn m(&self) -> u32 {
        RNS_MODULI[self.ch]
    }

    pub fn constant(x: u32, ch: usize) -> Self {
        Self { v: FpVar::constant(Fr::from(x)), bound: BigUint::from(x) + 1u32, ch }
    }

    /// A witness in [0, 2^32) (opened values are canonical, < m < 2^31; 32 bits is enough to keep
    /// bounds honest and costs 33 constraints).
    pub fn witness(cs: &ConstraintSystemRef<Fr>, x: Option<u32>, ch: usize) -> Result<Self, SynthesisError> {
        let v = range_witness(cs, x.map(BigUint::from), 32)?;
        Ok(Self { v, bound: BigUint::from(1u64 << 32), ch })
    }

    /// The integer value (only available while proving).
    pub fn value_big(&self) -> Option<BigUint> {
        self.v.value().ok().map(|x| to_big(&x))
    }

    pub fn value(&self) -> Option<u32> {
        self.value_big().map(|x| (x % self.m()).to_u32_digits().first().copied().unwrap_or(0))
    }

    fn checked(self) -> Self {
        if self.bound.bits() > MAX_BOUND_BITS {
            panic!("bound overflow: call reduce earlier");
        }
        self
    }

    pub fn add(&self, o: &Self) -> Self {
        Self { v: &self.v + &o.v, bound: &self.bound + &o.bound, ch: self.ch }.checked()
    }

    /// self - o, kept non-negative by adding a multiple of m above o's bound.
    pub fn sub(&self, o: &Self) -> Self {
        let m = BigUint::from(self.m());
        let k = (&o.bound + &m - 1u32) / &m * &m;
        Self { v: &self.v - &o.v + FpVar::constant(from_big(&k)), bound: &self.bound + &k, ch: self.ch }.checked()
    }

    pub fn mul(&self, o: &Self) -> Self {
        Self { v: &self.v * &o.v, bound: &self.bound * &o.bound, ch: self.ch }.checked()
    }

    pub fn mul_const(&self, c: u32) -> Self {
        Self { v: &self.v * Fr::from(c), bound: &self.bound * c, ch: self.ch }.checked()
    }

    /// Brings the value below 2^31: v = q*m + r.
    pub fn reduce(&self, cs: &ConstraintSystemRef<Fr>) -> Result<Self, SynthesisError> {
        let m = BigUint::from(self.m());
        let val = self.value_big();
        let qb = (&self.bound / &m).bits() + 1;
        let q = range_witness(cs, val.as_ref().map(|v| v / &m), qb)?;
        let r = range_witness(cs, val.as_ref().map(|v| v % &m), 31)?;
        (q * Fr::from(self.m()) + &r).enforce_equal(&self.v)?;
        Ok(Self { v: r, bound: BigUint::from(1u64 << 31), ch: self.ch })
    }

    /// Enforces self = 0 mod m.
    pub fn assert_zero(&self, cs: &ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let m = BigUint::from(self.m());
        let val = self.value_big();
        let kb = (&self.bound / &m).bits() + 1;
        let k = range_witness(cs, val.as_ref().map(|v| v / &m), kb)?;
        (k * Fr::from(self.m())).enforce_equal(&self.v)
    }

    pub fn assert_eq(&self, cs: &ConstraintSystemRef<Fr>, o: &Self) -> Result<(), SynthesisError> {
        self.sub(o).assert_zero(cs)
    }
}

/// Element of F_m[u] / (u^4 - beta_m).
#[derive(Clone)]
pub struct E4 {
    pub c: [M31; 4],
}

impl E4 {
    pub fn witness(cs: &ConstraintSystemRef<Fr>, x: Option<[u32; 4]>, ch: usize) -> Result<Self, SynthesisError> {
        let c = [0, 1, 2, 3].map(|k| M31::witness(cs, x.map(|v| v[k]), ch));
        let [a, b, c2, d] = c;
        Ok(Self { c: [a?, b?, c2?, d?] })
    }

    pub fn from_base(x: &M31) -> Self {
        let z = M31::constant(0, x.ch);
        Self { c: [x.clone(), z.clone(), z.clone(), z] }
    }

    pub fn add(&self, o: &Self) -> Self {
        Self { c: std::array::from_fn(|k| self.c[k].add(&o.c[k])) }
    }

    pub fn sub(&self, o: &Self) -> Self {
        Self { c: std::array::from_fn(|k| self.c[k].sub(&o.c[k])) }
    }

    pub fn mul_base(&self, s: &M31) -> Self {
        Self { c: std::array::from_fn(|k| self.c[k].mul(s)) }
    }

    /// Schoolbook product, unreduced (16 native multiplications).
    pub fn mul(&self, o: &Self) -> Self {
        let ch = self.c[0].ch;
        let beta = EXTENSION_BETA[ch];
        let mut out: Vec<Option<M31>> = vec![None, None, None, None];
        for i in 0..4 {
            for j in 0..4 {
                let mut p = self.c[i].mul(&o.c[j]);
                if i + j >= 4 {
                    p = p.mul_const(beta);
                }
                let k = (i + j) % 4;
                out[k] = Some(match out[k].take() {
                    None => p,
                    Some(acc) => acc.add(&p),
                });
            }
        }
        Self { c: std::array::from_fn(|k| out[k].clone().unwrap()) }
    }

    pub fn reduce(&self, cs: &ConstraintSystemRef<Fr>) -> Result<Self, SynthesisError> {
        let [a, b, c, d] = [0, 1, 2, 3].map(|k| self.c[k].reduce(cs));
        Ok(Self { c: [a?, b?, c?, d?] })
    }

    pub fn assert_zero(&self, cs: &ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        for x in &self.c {
            x.assert_zero(cs)?;
        }
        Ok(())
    }

    pub fn value(&self) -> Option<[u32; 4]> {
        let v: Option<Vec<u32>> = self.c.iter().map(|x| x.value()).collect();
        v.map(|v| [v[0], v[1], v[2], v[3]])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use ss_rap_v2::Extension4;

    #[test]
    fn ext4_mul_matches_native_in_every_channel() {
        for ch in 0..5 {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let (a, b) = (Extension4::new(123456789, 2, 3_000_000_000 % RNS_MODULI[ch], 77), Extension4::new(5, 1_999_999_999, 42, 9));
            let want = a.mul(&b, ch);
            let ga = E4::witness(&cs, Some(a.c), ch).unwrap();
            let gb = E4::witness(&cs, Some(b.c), ch).unwrap();
            let got = ga.mul(&gb).reduce(&cs).unwrap();
            assert_eq!(got.value().unwrap(), want.c);
            // got - want = 0 holds; got - want - 1 = 0 does not.
            let gw = E4::witness(&cs, Some(want.c), ch).unwrap();
            got.sub(&gw).assert_zero(&cs).unwrap();
            assert!(cs.is_satisfied().unwrap());
            let one = M31::constant(1, ch);
            got.c[0].sub(&gw.c[0]).sub(&one).assert_zero(&cs).unwrap();
            assert!(!cs.is_satisfied().unwrap());
        }
    }

    #[test]
    fn lazy_sums_of_many_products_stay_sound() {
        let ch = 4;
        let m = RNS_MODULI[ch] as u64;
        let cs = ConstraintSystem::<Fr>::new_ref();
        let xs: Vec<u32> = (0..100).map(|i| (m - 1 - i) as u32).collect();
        let mut acc = M31::constant(0, ch);
        let mut native = 0u64;
        for &x in &xs {
            let g = M31::witness(&cs, Some(x), ch).unwrap();
            acc = acc.add(&g.mul(&g));
            native = (native + (x as u64 * x as u64) % m) % m;
        }
        let r = acc.reduce(&cs).unwrap();
        assert_eq!(r.value().unwrap() as u64, native);
        assert!(cs.is_satisfied().unwrap());
    }
}
