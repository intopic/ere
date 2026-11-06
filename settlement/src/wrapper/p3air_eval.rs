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
    pub is_first_row: E,
    pub is_last_row: E,
    pub is_transition: E,
}

pub struct Eval<'a, C: Ctx> {
    pub ctx: &'a mut C,
    pt: &'a Point<C::E>,
    base_memo: HashMap<usize, C::E>,
    ext_memo: HashMap<usize, C::E>,
}

fn addr<T>(x: &T) -> usize {
    x as *const T as usize
}

impl<'a, C: Ctx> Eval<'a, C> {
    pub fn new(ctx: &'a mut C, pt: &'a Point<C::E>) -> Self {
        Self { ctx, pt, base_memo: HashMap::new(), ext_memo: HashMap::new() }
    }

    pub fn base(&mut self, e: &SymbolicExpression<F>) -> R<C::E> {
        if let Some(v) = self.base_memo.get(&addr(e)) {
            return Ok(v.clone());
        }
        let v = match e {
            SymbolicExpr::Leaf(l) => match l {
                BaseLeaf::Variable(v) => match v.entry {
                    BaseEntry::Main { offset: 0 } => self.pt.main_local[v.index].clone(),
                    BaseEntry::Main { offset: 1 } => self.pt.main_next[v.index].clone(),
                    BaseEntry::Preprocessed { offset: 0 } => self.pt.pre_local[v.index].clone(),
                    BaseEntry::Preprocessed { offset: 1 } => self.pt.pre_next[v.index].clone(),
                    BaseEntry::Periodic => self.pt.periodic[v.index].clone(),
                    other => panic!("unsupported base entry {other:?}"),
                },
                BaseLeaf::IsFirstRow => self.pt.is_first_row.clone(),
                BaseLeaf::IsLastRow => self.pt.is_last_row.clone(),
                BaseLeaf::IsTransition => self.pt.is_transition.clone(),
                BaseLeaf::Constant(c) => self.ctx.base(c.as_canonical_u32()),
            },
            SymbolicExpr::Add { x, y, .. } => {
                let (a, b) = (self.base(x)?, self.base(y)?);
                self.ctx.add(&a, &b)?
            }
            SymbolicExpr::Sub { x, y, .. } => {
                let (a, b) = (self.base(x)?, self.base(y)?);
                self.ctx.sub(&a, &b)?
            }
            SymbolicExpr::Neg { x, .. } => {
                let a = self.base(x)?;
                self.ctx.neg(&a)?
            }
            SymbolicExpr::Mul { x, y, .. } => self.mul_base(x, y)?,
        };
        self.base_memo.insert(addr(e), v.clone());
        Ok(v)
    }

    /// x * y, as a scaling when one side is a small constant.
    fn mul_base(&mut self, x: &SymbolicExpression<F>, y: &SymbolicExpression<F>) -> R<C::E> {
        let small = |e: &SymbolicExpression<F>| match e {
            SymbolicExpr::Leaf(BaseLeaf::Constant(c)) => Some(c.as_canonical_u32()),
            _ => None,
        };
        if let Some(c) = small(x) {
            let b = self.base(y)?;
            return self.ctx.scale(&b, c);
        }
        if let Some(c) = small(y) {
            let a = self.base(x)?;
            return self.ctx.scale(&a, c);
        }
        let (a, b) = (self.base(x)?, self.base(y)?);
        self.ctx.mul(&a, &b)
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
                    self.ctx.mul(&a, &b)?
                }
            }
        };
        self.ext_memo.insert(addr(e), v.clone());
        Ok(v)
    }

    /// Horner fold of all constraints: base first, then extension.
    pub fn fold(&mut self, base: &[SymbolicExpression<F>], ext: &[SymbolicExpressionExt<F, EF>], alpha: &C::E) -> R<C::E> {
        let mut acc = self.ctx.base(0);
        for c in base {
            let v = self.base(c)?;
            let t = self.ctx.mul(&acc, alpha)?;
            acc = self.ctx.add(&t, &v)?;
        }
        for c in ext {
            let v = self.ext(c)?;
            let t = self.ctx.mul(&acc, alpha)?;
            acc = self.ctx.add(&t, &v)?;
        }
        Ok(acc)
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
        let (st, traces) = ss_rap_p3::state::tests_case(600, 8);
        let p = Params { log_rows: 8, log_blowup: 1, queries: 20, budget: 3 };
        let proof = record::prove_one(&st, &traces, &p);
        let (ok, ops) = record::verify_one(&st, &proof, &p);
        assert!(ok);
        let s: Vec<u32> = ops.iter().filter_map(|o| if let Op::Sample(v) = o { Some(*v) } else { None }).collect();
        let e = |k: usize| EF::from_basis_coefficients_slice(&s[k..k + 4].iter().map(|&v| F::from_u32(v)).collect::<Vec<_>>()).unwrap();
        let (la, lb, alpha, zeta) = (e(0), e(4), e(8), e(12));

        let (cfg, _) = record::config(p.log_blowup, p.queries);
        let airs = all_airs::<F>(&st);
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
            let layout = AirLayout { preprocessed_width: pre_w, main_width: air.width(), num_public_values: 0, num_periodic_columns: air.num_periodic_columns(), ..Default::default() };
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
