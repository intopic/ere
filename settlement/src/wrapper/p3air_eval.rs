//! Evaluation of Plonky3 AIR constraints (incl. the LogUp constraints p3-lookup adds) at the
//! out-of-domain point, from p3's own symbolic constraint lists, over any arithmetic (`Ctx`):
//! natively (to check against Plonky3) or in R1CS (`E4`). The constraint DAG is shared through
//! `Arc`s, so every node is evaluated once (memoised by address).
//!
//! The verifier's accumulator is Horner in call order: acc = acc * alpha + c. Plonky3 evaluates
//! the AIR (base constraints) and then the lookups (extension constraints), so the order is all
//! base constraints, then all extension constraints (checked against real proofs in the tests).

use ark_relations::r1cs::SynthesisError;
use p3_air::symbolic::{BaseEntry, BaseLeaf, ExtEntry, ExtLeaf, SymbolicExpr, SymbolicExpression, SymbolicExpressionExt};
use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeField32};
use std::collections::HashMap;

pub type F = BabyBear;
pub type EF = BinomialExtensionField<BabyBear, 4>;

pub type R<T> = Result<T, SynthesisError>;

/// Arithmetic in the quartic extension of BabyBear.
pub trait Ctx {
    type E: Clone;
    fn add(&mut self, a: &Self::E, b: &Self::E) -> R<Self::E>;
    fn sub(&mut self, a: &Self::E, b: &Self::E) -> R<Self::E>;
    fn neg(&mut self, a: &Self::E) -> R<Self::E>;
    fn mul(&mut self, a: &Self::E, b: &Self::E) -> R<Self::E>;
    /// a * c for a small constant (no reduction needed in circuit)
    fn scale(&mut self, a: &Self::E, c: u32) -> R<Self::E>;
    fn inv(&mut self, a: &Self::E) -> R<Self::E>;
    fn base(&mut self, c: u32) -> Self::E;
    fn ext(&mut self, c: [u32; 4]) -> Self::E;
    /// a * X (X the extension generator, X^4 = 11)
    fn mul_x(&mut self, a: &Self::E) -> R<Self::E>;
    /// a * b where the result may stay unreduced (in circuit)
    fn mul_lazy(&mut self, a: &Self::E, b: &Self::E) -> R<Self::E> {
        self.mul(a, b)
    }
    /// a computed value about to be multiplied (in circuit: reduced if wide)
    fn prep(&mut self, a: &Self::E) -> R<Self::E> {
        Ok(a.clone())
    }
    /// sum_i a_i * b_i (in circuit: one reduction for the whole sum)
    fn dot(&mut self, a: &[Self::E], b: &[Self::E]) -> R<Self::E> {
        let mut acc = self.base(0);
        for (x, y) in a.iter().zip(b) {
            let p = self.mul(x, y)?;
            acc = self.add(&acc, &p)?;
        }
        Ok(acc)
    }
}

/// Everything the constraints read at the out-of-domain point (one instance).
pub struct Point<E> {
    pub main_local: Vec<E>,
    pub main_next: Vec<E>,
    pub pre_local: Vec<E>,
    pub pre_next: Vec<E>,
    /// permutation columns as extension elements (already recomposed)
    pub perm_local: Vec<E>,
    pub perm_next: Vec<E>,
    pub challenges: Vec<E>,
    pub perm_values: Vec<E>,
    pub periodic: Vec<E>,
    /// the instance's public values (base field)
    pub public: Vec<E>,
    pub is_first_row: E,
    pub is_last_row: E,
    pub is_transition: E,
}

pub struct Eval<'a, C: Ctx> {
    pub ctx: &'a mut C,
    pt: &'a Point<C::E>,
    base_memo: HashMap<usize, C::E>,
    ext_memo: HashMap<usize, C::E>,
    /// base expressions as linear forms over "atoms" (opened values and products)
    atoms: Vec<C::E>,
    leaf_atoms: HashMap<(u8, usize, usize), usize>,
    lin_memo: HashMap<usize, Lin>,
    /// operands of products, by linear form (computed and prepared once)
    operands: HashMap<(Vec<(usize, u32)>, u32), C::E>,
}

const P_BB: u64 = 2013265921;

/// sum_j c_j * atom_j + k over BabyBear (terms sorted by atom). Additions and constant
/// multiples of base expressions stay linear forms, so a chain of linear layers (Poseidon2's
/// partial rounds) costs nothing in R1CS until a product needs its value.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct Lin {
    terms: Vec<(usize, u32)>,
    k: u32,
}

impl Lin {
    fn atom(i: usize) -> Self {
        Self { terms: vec![(i, 1)], k: 0 }
    }
    fn constant(c: u32) -> Self {
        Self { terms: vec![], k: c }
    }
    fn is_const(&self) -> Option<u32> {
        self.terms.is_empty().then_some(self.k)
    }
    /// self + s * o
    fn axpy(&self, s: u32, o: &Self) -> Self {
        let mul = |c: u32| (c as u64 * s as u64 % P_BB) as u32;
        let add = |a: u32, b: u32| ((a as u64 + b as u64) % P_BB) as u32;
        let (mut i, mut j) = (0, 0);
        let mut t = Vec::with_capacity(self.terms.len() + o.terms.len());
        while i < self.terms.len() || j < o.terms.len() {
            let x = self.terms.get(i).map(|x| x.0).unwrap_or(usize::MAX);
            let y = o.terms.get(j).map(|y| y.0).unwrap_or(usize::MAX);
            let (id, c) = if x < y {
                i += 1;
                (x, self.terms[i - 1].1)
            } else if y < x {
                j += 1;
                (y, mul(o.terms[j - 1].1))
            } else {
                i += 1;
                j += 1;
                (x, add(self.terms[i - 1].1, mul(o.terms[j - 1].1)))
            };
            if c != 0 {
                t.push((id, c));
            }
        }
        Self { terms: t, k: add(self.k, mul(o.k)) }
    }
    fn scale(&self, s: u32) -> Self {
        Self::default().axpy(s, self)
    }
}

fn addr<T>(x: &T) -> usize {
    x as *const T as usize
}

impl<'a, C: Ctx> Eval<'a, C> {
    pub fn new(ctx: &'a mut C, pt: &'a Point<C::E>) -> Self {
        Self { ctx, pt, base_memo: HashMap::new(), ext_memo: HashMap::new(), atoms: vec![], leaf_atoms: HashMap::new(), lin_memo: HashMap::new(), operands: HashMap::new() }
    }

    pub fn base(&mut self, e: &SymbolicExpression<F>) -> R<C::E> {
        if let Some(v) = self.base_memo.get(&addr(e)) {
            return Ok(v.clone());
        }
        let l = self.lin(e)?;
        let v = self.materialize(&l)?;
        self.base_memo.insert(addr(e), v.clone());
        Ok(v)
    }

    fn new_atom(&mut self, v: C::E) -> usize {
        self.atoms.push(v);
        self.atoms.len() - 1
    }

    /// The value of a linear form: free in R1CS (constant multiples and sums of variables).
    fn materialize(&mut self, l: &Lin) -> R<C::E> {
        if l.k == 0 && l.terms.len() == 1 && l.terms[0].1 == 1 {
            return Ok(self.atoms[l.terms[0].0].clone());
        }
        let mut acc = self.ctx.base(l.k);
        for &(i, c) in &l.terms {
            let a = self.atoms[i].clone();
            let t = if c == 1 { a } else { self.ctx.scale(&a, c)? };
            acc = self.ctx.add(&acc, &t)?;
        }
        Ok(acc)
    }

    /// A factor of a product: an atom as it is, a combination computed and prepared once.
    fn operand(&mut self, l: &Lin) -> R<C::E> {
        if l.k == 0 && l.terms.len() == 1 && l.terms[0].1 == 1 {
            return Ok(self.atoms[l.terms[0].0].clone());
        }
        let key = (l.terms.clone(), l.k);
        if let Some(v) = self.operands.get(&key) {
            return Ok(v.clone());
        }
        let v = self.materialize(l)?;
        let v = self.ctx.prep(&v)?;
        self.operands.insert(key, v.clone());
        Ok(v)
    }

    fn lin(&mut self, e: &SymbolicExpression<F>) -> R<Lin> {
        if let Some(l) = self.lin_memo.get(&addr(e)) {
            return Ok(l.clone());
        }
        let l = match e {
            SymbolicExpr::Leaf(BaseLeaf::Constant(c)) => Lin::constant(c.as_canonical_u32()),
            SymbolicExpr::Leaf(leaf) => {
                let key = match leaf {
                    BaseLeaf::Variable(v) => {
                        let k = match v.entry {
                            BaseEntry::Main { offset } => offset as u8,
                            BaseEntry::Preprocessed { offset } => 2 + offset as u8,
                            BaseEntry::Periodic => 4,
                            BaseEntry::Public => 5,
                        };
                        (k, v.index, 0)
                    }
                    BaseLeaf::IsFirstRow => (6, 0, 0),
                    BaseLeaf::IsLastRow => (7, 0, 0),
                    BaseLeaf::IsTransition => (8, 0, 0),
                    BaseLeaf::Constant(_) => unreachable!(),
                };
                match self.leaf_atoms.get(&key) {
                    Some(&i) => Lin::atom(i),
                    None => {
                        let v = self.leaf(e);
                        let i = self.new_atom(v);
                        self.leaf_atoms.insert(key, i);
                        Lin::atom(i)
                    }
                }
            }
            SymbolicExpr::Add { x, y, .. } => {
                let (a, b) = (self.lin(x)?, self.lin(y)?);
                a.axpy(1, &b)
            }
            SymbolicExpr::Sub { x, y, .. } => {
                let (a, b) = (self.lin(x)?, self.lin(y)?);
                a.axpy((P_BB - 1) as u32, &b)
            }
            SymbolicExpr::Neg { x, .. } => self.lin(x)?.scale((P_BB - 1) as u32),
            SymbolicExpr::Mul { x, y, .. } => {
                let (a, b) = (self.lin(x)?, self.lin(y)?);
                if let Some(c) = a.is_const() {
                    b.scale(c)
                } else if let Some(c) = b.is_const() {
                    a.scale(c)
                } else {
                    let (va, vb) = (self.operand(&a)?, self.operand(&b)?);
                    let p = self.ctx.mul_lazy(&va, &vb)?;
                    Lin::atom(self.new_atom(p))
                }
            }
        };
        self.lin_memo.insert(addr(e), l.clone());
        Ok(l)
    }

    fn leaf(&mut self, e: &SymbolicExpression<F>) -> C::E {
        let SymbolicExpr::Leaf(l) = e else { unreachable!() };
        match l {
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Main { offset: 0 } => self.pt.main_local[v.index].clone(),
                BaseEntry::Main { offset: 1 } => self.pt.main_next[v.index].clone(),
                BaseEntry::Preprocessed { offset: 0 } => self.pt.pre_local[v.index].clone(),
                BaseEntry::Preprocessed { offset: 1 } => self.pt.pre_next[v.index].clone(),
                BaseEntry::Periodic => self.pt.periodic[v.index].clone(),
                BaseEntry::Public => self.pt.public[v.index].clone(),
                other => panic!("unsupported base entry {other:?}"),
            },
            BaseLeaf::IsFirstRow => self.pt.is_first_row.clone(),
            BaseLeaf::IsLastRow => self.pt.is_last_row.clone(),
            BaseLeaf::IsTransition => self.pt.is_transition.clone(),
            BaseLeaf::Constant(c) => self.ctx.base(c.as_canonical_u32()),
        }
    }

    pub fn ext(&mut self, e: &SymbolicExpressionExt<F, EF>) -> R<C::E> {
        if let Some(v) = self.ext_memo.get(&addr(e)) {
            return Ok(v.clone());
        }
        let v = match e {
            SymbolicExpr::Leaf(l) => match l {
                ExtLeaf::Base(b) => self.base(b)?,
                ExtLeaf::ExtVariable(v) => match v.entry {
                    ExtEntry::Permutation { offset: 0 } => self.pt.perm_local[v.index].clone(),
                    ExtEntry::Permutation { offset: 1 } => self.pt.perm_next[v.index].clone(),
                    ExtEntry::Challenge => self.pt.challenges[v.index].clone(),
                    ExtEntry::PermutationValue => self.pt.perm_values[v.index].clone(),
                    other => panic!("unsupported ext entry {other:?}"),
                },
                ExtLeaf::ExtConstant(c) => {
                    let s: &[F] = c.as_basis_coefficients_slice();
                    self.ctx.ext([0, 1, 2, 3].map(|i| s[i].as_canonical_u32()))
                }
            },
            SymbolicExpr::Add { x, y, .. } => {
                let (a, b) = (self.ext(x)?, self.ext(y)?);
                self.ctx.add(&a, &b)?
            }
            SymbolicExpr::Sub { x, y, .. } => {
                let (a, b) = (self.ext(x)?, self.ext(y)?);
                self.ctx.sub(&a, &b)?
            }
            SymbolicExpr::Neg { x, .. } => {
                let a = self.ext(x)?;
                self.ctx.neg(&a)?
            }
            SymbolicExpr::Mul { x, y, .. } => {
                let small = |e: &SymbolicExpressionExt<F, EF>| match e {
                    SymbolicExpr::Leaf(ExtLeaf::Base(SymbolicExpr::Leaf(BaseLeaf::Constant(c)))) => Some(c.as_canonical_u32()),
                    _ => None,
                };
                if let Some(c) = small(x) {
                    let b = self.ext(y)?;
                    self.ctx.scale(&b, c)?
                } else if let Some(c) = small(y) {
                    let a = self.ext(x)?;
                    self.ctx.scale(&a, c)?
                } else {
                    let (a, b) = (self.ext(x)?, self.ext(y)?);
                    self.ctx.mul_lazy(&a, &b)?
                }
            }
        };
        self.ext_memo.insert(addr(e), v.clone());
        Ok(v)
    }

    /// The fold of all constraints (base first, then extension) that Plonky3's Horner loop
    /// `acc = acc * alpha + c` computes, i.e. sum_i c_i * alpha^(n-1-i), evaluated as
    /// sum_a alpha^(K a) * (sum_b c_(K a + b) * alpha^b): two levels of dot products, so the
    /// circuit reduces once per group of K constraints instead of once per constraint.
    pub fn fold(&mut self, base: &[SymbolicExpression<F>], ext: &[SymbolicExpressionExt<F, EF>], alpha: &C::E) -> R<C::E> {
        const K: usize = 32;
        let mut cs = Vec::with_capacity(base.len() + ext.len());
        for c in base {
            cs.push(self.base(c)?);
        }
        for c in ext {
            cs.push(self.ext(c)?);
        }
        cs.reverse(); // cs[e] has weight alpha^e
        let n = cs.len();
        if n == 0 {
            return Ok(self.ctx.base(0));
        }
        let mut low = vec![self.ctx.base(1)];
        while low.len() < K.min(n) {
            let x = self.ctx.mul(low.last().unwrap(), alpha)?;
            low.push(self.ctx.prep(&x)?);
        }
        let groups = n.div_ceil(K);
        let mut high = vec![self.ctx.base(1)];
        if groups > 1 {
            let step = self.ctx.mul(low.last().unwrap(), alpha)?; // alpha^K
            let step = self.ctx.prep(&step)?;
            while high.len() < groups {
                let x = self.ctx.mul(high.last().unwrap(), &step)?;
                high.push(self.ctx.prep(&x)?);
            }
        }
        let sums: Vec<C::E> = cs.chunks(K).map(|g| self.ctx.dot(g, &low[..g.len()])).collect::<R<_>>()?;
        self.ctx.dot(&sums, &high)
    }
}

/// Native arithmetic with Plonky3's own extension field.
pub struct Native;

impl Ctx for Native {
    type E = EF;
    fn add(&mut self, a: &EF, b: &EF) -> R<EF> {
        Ok(*a + *b)
    }
    fn sub(&mut self, a: &EF, b: &EF) -> R<EF> {
        Ok(*a - *b)
    }
    fn neg(&mut self, a: &EF) -> R<EF> {
        Ok(-*a)
    }
    fn mul(&mut self, a: &EF, b: &EF) -> R<EF> {
        Ok(*a * *b)
    }
    fn scale(&mut self, a: &EF, c: u32) -> R<EF> {
        use p3_field::PrimeCharacteristicRing;
        Ok(*a * F::from_u32(c))
    }
    fn inv(&mut self, a: &EF) -> R<EF> {
        use p3_field::Field;
        Ok(a.inverse())
    }
    fn base(&mut self, c: u32) -> EF {
        use p3_field::PrimeCharacteristicRing;
        EF::from(F::from_u32(c))
    }
    fn ext(&mut self, c: [u32; 4]) -> EF {
        use p3_field::PrimeCharacteristicRing;
        EF::from_basis_coefficients_slice(&c.map(F::from_u32)).unwrap()
    }
    fn mul_x(&mut self, a: &EF) -> R<EF> {
        use p3_field::PrimeCharacteristicRing;
        Ok(*a * EF::from_basis_coefficients_slice(&[F::ZERO, F::ONE, F::ZERO, F::ZERO]).unwrap())
    }
}

/// Selectors of the natural trace domain of size 2^log_n at `z`:
/// (is_first_row, is_last_row, is_transition, 1 / Z_H(z)).
pub fn selectors<C: Ctx>(ctx: &mut C, z: &C::E, log_n: usize) -> R<[C::E; 4]> {
    let mut zn = z.clone();
    for _ in 0..log_n {
        zn = ctx.mul(&zn, &zn)?;
    }
    let one = ctx.base(1);
    let z_h = ctx.sub(&zn, &one)?;
    let g_inv = pow_u32(super::p3fri_var::TWO_ADIC_GENERATORS[log_n], (super::challenger_var::P - 2) as u64);
    let gi = ctx.base(g_inv);
    let zm1 = ctx.sub(z, &one)?;
    let zmg = ctx.sub(z, &gi)?;
    let i1 = ctx.inv(&zm1)?;
    let i2 = ctx.inv(&zmg)?;
    let first = ctx.mul(&z_h, &i1)?;
    let last = ctx.mul(&z_h, &i2)?;
    let inv_van = ctx.inv(&z_h)?;
    Ok([first, last, zmg, inv_van])
}

pub fn pow_u32(mut a: u32, mut e: u64) -> u32 {
    let p = super::challenger_var::P;
    let mut r = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            r = r * a as u64 % p;
        }
        a = (a as u64 * a as u64 % p) as u32;
        e >>= 1;
    }
    r as u32
}

/// The periodic column `col` (one period, a power of two dividing 2^log_n) at `z`, by the
/// barycentric formula over the subgroup of size p: P(w) = (w^p - 1)/p * sum_i v_i g^i/(w - g^i)
/// with w = z^(n/p).
pub fn periodic_at<C: Ctx>(ctx: &mut C, cols: &[Vec<u32>], z: &C::E, log_n: usize) -> R<Vec<C::E>> {
    if cols.is_empty() {
        return Ok(vec![]);
    }
    let p = cols[0].len();
    assert!(cols.iter().all(|c| c.len() == p) && p.is_power_of_two());
    let log_p = p.trailing_zeros() as usize;
    let mut w = z.clone();
    for _ in log_p..log_n {
        w = ctx.mul(&w, &w)?;
    }
    let mut wp = w.clone();
    for _ in 0..log_p {
        wp = ctx.mul(&wp, &wp)?;
    }
    let one = ctx.base(1);
    let num = ctx.sub(&wp, &one)?;
    let inv_p = pow_u32(p as u32, (super::challenger_var::P - 2) as u64);
    let factor = ctx.scale(&num, inv_p)?;
    let g = super::p3fri_var::TWO_ADIC_GENERATORS[log_p];
    // weights g^i / (w - g^i), shared by all columns
    let mut weights = Vec::with_capacity(p);
    let mut gi = 1u32;
    for _ in 0..p {
        let c = ctx.base(gi);
        let d = ctx.sub(&w, &c)?;
        let inv = ctx.inv(&d)?;
        weights.push(ctx.scale(&inv, gi)?);
        gi = ((gi as u64 * g as u64) % super::challenger_var::P) as u32;
    }
    let mut out = Vec::with_capacity(cols.len());
    for col in cols {
        let mut acc = ctx.base(0);
        for (v, wt) in col.iter().zip(&weights) {
            if *v != 0 {
                let t = ctx.scale(wt, *v)?;
                acc = ctx.add(&acc, &t)?;
            }
        }
        out.push(ctx.mul(&acc, &factor)?);
    }
    Ok(out)
}

/// sum_k c[k] X^k for opened basis-coefficient columns (Plonky3's `from_ext_basis_coefficients`).
pub fn recompose<C: Ctx>(ctx: &mut C, c: &[C::E]) -> R<C::E> {
    assert_eq!(c.len(), 4);
    let mut acc = c[3].clone();
    for k in (0..3).rev() {
        let t = ctx.mul_x(&acc)?;
        acc = ctx.add(&t, &c[k])?;
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_air::symbolic::AirLayout;
    use p3_air::BaseAir;
    use p3_batch_stark::{ProverData, StarkGenericConfig};
    use p3_commit::{Pcs, PolynomialSpace};
    use p3_field::{Field, PrimeCharacteristicRing};
    use p3_lookup::logup::LogUpGadget;
    use ss_rap_p3::record::{self, Op};
    use ss_rap_p3::state::{all_airs, Params};

    /// Recomputes, for every instance of a real batch proof, sum alpha^k C_k(zeta) / Z_H(zeta)
    /// with our interpreter and compares it with the quotient recomposed from the opened chunks.
    #[test]
    fn constraints_at_zeta_match_the_quotient() {
        let _heavy = crate::heavy_test_lock();
        let (st, traces) = ss_rap_p3::state::tests_case(600, 8);
        let p = Params { log_rows: 8, log_blowup: 1, queries: 20, budget: 3, query_pow: 0 };
        let blobs = ss_rap_p3::state::tests_blobs();
        let claim = blobs.claim();
        let proof = record::prove_one(&st, &traces, &blobs, &p);
        let (ok, ops) = record::verify_one(&st, &proof, &claim, &p);
        assert!(ok);
        let s: Vec<u32> = ops.iter().filter_map(|o| if let Op::Sample(v) = o { Some(*v) } else { None }).collect();
        let e = |k: usize| EF::from_basis_coefficients_slice(&s[k..k + 4].iter().map(|&v| F::from_u32(v)).collect::<Vec<_>>()).unwrap();
        let (la, lb, alpha, zeta) = (e(0), e(4), e(8), e(12));

        let (cfg, _) = record::config(p.log_blowup, p.queries, p.query_pow);
        let airs = all_airs::<F>(&st, claim.slots());
        let pvs = ss_rap_p3::state::all_public_values::<F>(&st, &airs, &claim);
        let degs: Vec<usize> = proof.degree_bits.clone();
        let pd = ProverData::<record::Config>::from_airs_and_degrees_with_lookup_budgets(&cfg, &airs, &degs, &vec![p.budget; airs.len()], p.log_blowup).unwrap();
        let lookups = &pd.common.lookups;
        // bus ids and max width, as lay_out_lookup_challenges
        let mut names: Vec<String> = vec![];
        let mut next = 0usize;
        let mut width = 1usize;
        let bus: Vec<Vec<usize>> = lookups
            .iter()
            .map(|ls| {
                ls.iter()
                    .map(|l| {
                        width = width.max(l.elements[0].len());
                        match &l.kind {
                            p3_lookup::Kind::Global(n) => {
                                if let Some(i) = names.iter().position(|x| x == n) {
                                    i
                                } else {
                                    names.push(n.clone());
                                    next += 1;
                                    next - 1
                                }
                            }
                            p3_lookup::Kind::Local => {
                                next += 1;
                                next - 1
                            }
                        }
                    })
                    .collect()
            })
            .collect();
        let gamma = lb.exp_u64(width as u64);
        let prefix = |b: usize| la + gamma * F::from_usize(b + 1);
        let mut terminal_sum = EF::ZERO;
        let pcs = cfg.pcs();
        for (i, air) in airs.iter().enumerate() {
            let ov = &proof.opened_values.instances[i];
            let pre_w = air.preprocessed_width();
            let layout = AirLayout { preprocessed_width: pre_w, main_width: air.width(), num_public_values: air.num_public_values(), num_periodic_columns: air.num_periodic_columns(), ..Default::default() };
            let (base, ext) = p3_batch_stark::symbolic::get_symbolic_constraints::<F, EF, _, _>(air, layout, &lookups[i], &LogUpGadget::new());
            let log_n = degs[i];
            let mut c = Native;
            let [first, last, trans, inv_van] = selectors(&mut c, &zeta, log_n).unwrap();
            let periodic_cols: Vec<Vec<u32>> = air.periodic_columns().iter().map(|col| col.iter().map(|v| v.as_canonical_u32()).collect()).collect();
            let periodic = periodic_at(&mut c, &periodic_cols, &zeta, log_n).unwrap();
            let rec = |c: &mut Native, flat: &[EF]| flat.chunks(4).map(|ch| recompose(c, ch).unwrap()).collect::<Vec<_>>();
            let challenges: Vec<EF> = bus[i].iter().flat_map(|&b| [prefix(b), lb]).collect();
            let pt = Point {
                main_local: ov.base_opened_values.trace_local.clone(),
                main_next: ov.base_opened_values.trace_next.clone().unwrap_or_else(|| vec![EF::ZERO; air.width()]),
                pre_local: ov.base_opened_values.preprocessed.as_ref().map(|p| p.local.clone()).unwrap_or_default(),
                pre_next: ov.base_opened_values.preprocessed.as_ref().and_then(|p| p.next.clone()).unwrap_or_else(|| vec![EF::ZERO; pre_w]),
                perm_local: rec(&mut c, &ov.permutation_local),
                perm_next: rec(&mut c, &ov.permutation_next),
                challenges,
                perm_values: proof.lookup_terminals[i].iter().map(|t| t.0).collect(),
                periodic,
                public: pvs[i].iter().map(|&v| EF::from(v)).collect(),
                is_first_row: first,
                is_last_row: last,
                is_transition: trans,
            };
            if let Some(t) = &proof.lookup_terminals[i] {
                terminal_sum += t.0;
            }
            let mut ev = Eval::new(&mut c, &pt);
            let acc = ev.fold(&base, &ext, &alpha).unwrap();
            // quotient from chunks (Plonky3's own domains)
            let n_chunks = ov.base_opened_values.quotient_chunks.len();
            let ext_dom = <_ as Pcs<EF, record::Recording>>::natural_domain_for_degree(pcs, 1 << log_n);
            let qdom = ext_dom.try_create_disjoint_domain(n_chunks << log_n).unwrap();
            let doms = qdom.split_domains(n_chunks);
            let mut quotient = EF::ZERO;
            for (k, ch) in ov.base_opened_values.quotient_chunks.iter().enumerate() {
                let mut zp = EF::ONE;
                for (j, d) in doms.iter().enumerate() {
                    if j != k {
                        zp *= d.vanishing_poly_at_point(zeta) * d.vanishing_poly_at_point(doms[k].first_point()).inverse();
                    }
                }
                quotient += zp * recompose(&mut Native, ch).unwrap();
            }
            assert_eq!(acc * inv_van, quotient, "instance {i}: {} base + {} ext constraints", base.len(), ext.len());
            eprintln!("instance {i}: {} base + {} ext constraints, {} chunks, ok", base.len(), ext.len(), n_chunks);
        }
        assert_eq!(terminal_sum, EF::ZERO);
    }
}
