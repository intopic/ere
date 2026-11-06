//! Parallel synthesis.
//!
//! arkworks builds a circuit through one `ConstraintSystemRef` (an `Rc<RefCell<..>>`), so a
//! circuit is synthesised on one thread. Here a circuit is a *parent* constraint system plus
//! independent *children*, each synthesised in its own constraint system on its own thread, and
//! merged afterwards into one R1CS:
//!
//! - a child **imports** parent values: it allocates a fresh witness with the parent's value and
//!   records a link (child witness, parent variable);
//! - a child **exports** a value to a parent variable the parent allocated beforehand (from a
//!   value it computed natively): again a link;
//! - `merge` gives every linked child witness the column of its parent variable and every other
//!   child witness a fresh column after the parent's, and concatenates the constraints.
//!
//! A link identifies two variables, so it is exactly an equality constraint, for free. The same
//! body runs sequentially with `Par::Inline` (one constraint system; imports are the parent
//! variables themselves and exports are equality constraints), which is what the
//! `ConstraintSynthesizer` impls and the tests use.

use super::fp31::{E4, M31};
use ark_bn254::Fr;
use ark_ff::Zero;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::{AllocatedFp, FpVar};
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, LinearCombination, OptimizationGoal, SynthesisError, SynthesisMode, Variable};
use num_bigint::BigUint;
use rayon::prelude::*;
use std::cell::RefCell;

pub type R<T> = Result<T, SynthesisError>;
pub type Cs = ConstraintSystemRef<Fr>;

/// A parent value that can cross threads: a constant, or a variable with its value (None
/// during setup).
#[derive(Clone, Debug)]
pub enum H {
    Const(Fr),
    Var(Variable, Option<Fr>),
}

#[derive(Clone, Debug)]
pub struct HM31 {
    pub h: H,
    pub bound: BigUint,
}

pub type HE4 = [HM31; 4];

/// A fresh constraint system configured as arkworks' Groth16 configures its own.
pub fn new_cs(setup: bool) -> Cs {
    let cs = ConstraintSystem::<Fr>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(if setup { SynthesisMode::Setup } else { SynthesisMode::Prove { construct_matrices: true } });
    cs
}

/// `x` as a plain variable (a symbolic linear combination gets its own witness).
pub fn materialize(cs: &Cs, x: &FpVar<Fr>) -> R<FpVar<Fr>> {
    match x {
        FpVar::Constant(_) => Ok(x.clone()),
        FpVar::Var(a) if matches!(a.variable, Variable::Witness(_) | Variable::Instance(_) | Variable::One) => Ok(x.clone()),
        FpVar::Var(_) => {
            let w = FpVar::new_witness(cs.clone(), || x.value())?;
            w.enforce_equal(x)?;
            Ok(w)
        }
    }
}

/// Parent side: a handle on `x` for a child.
pub fn h(cs: &Cs, x: &FpVar<Fr>) -> R<H> {
    Ok(match materialize(cs, x)? {
        FpVar::Constant(c) => H::Const(c),
        FpVar::Var(a) => H::Var(a.variable, a.value().ok()),
    })
}

pub fn hm31(cs: &Cs, x: &M31) -> R<HM31> {
    assert_eq!(x.ch, 0, "BabyBear values only");
    Ok(HM31 { h: h(cs, &x.v)?, bound: x.bound.clone() })
}

pub fn he4(cs: &Cs, x: &E4) -> R<HE4> {
    let [a, b, c, d] = [0, 1, 2, 3].map(|k| hm31(cs, &x.c[k]));
    Ok([a?, b?, c?, d?])
}

pub fn hbool(cs: &Cs, b: &Boolean<Fr>) -> R<H> {
    h(cs, &FpVar::from(b.clone()))
}

/// Parent side: a new parent variable for a value a child will export (`value` computed
/// natively; None during setup). No constraint: the child's link constrains it.
pub fn slot(cs: &Cs, value: Option<Fr>) -> R<FpVar<Fr>> {
    FpVar::new_witness(cs.clone(), || value.ok_or(SynthesisError::AssignmentMissing))
}

pub fn slot_m31(cs: &Cs, value: Option<u32>, bound: BigUint) -> R<M31> {
    Ok(M31 { v: slot(cs, value.map(|v| Fr::from(v as u64)))?, bound, ch: 0 })
}

pub fn slot_e4(cs: &Cs, value: Option<[u32; 4]>, bound: BigUint) -> R<E4> {
    let c: Vec<M31> = (0..4).map(|k| slot_m31(cs, value.map(|v| v[k]), bound.clone())).collect::<R<_>>()?;
    Ok(E4 { c: [c[0].clone(), c[1].clone(), c[2].clone(), c[3].clone()] })
}

enum Mode {
    Inline,
    Child,
}

/// What a child body works with.
pub struct Io {
    pub cs: Cs,
    mode: Mode,
    links: Vec<(usize, Variable)>,
    linked: std::collections::HashSet<usize>,
}

impl Io {
    pub fn import(&mut self, x: &H) -> R<FpVar<Fr>> {
        match (x, &self.mode) {
            (H::Const(c), _) => Ok(FpVar::Constant(*c)),
            (H::Var(v, val), Mode::Inline) => Ok(FpVar::Var(AllocatedFp::new(*val, *v, self.cs.clone()))),
            (H::Var(v, val), Mode::Child) => {
                let w = FpVar::new_witness(self.cs.clone(), || val.ok_or(SynthesisError::AssignmentMissing))?;
                let FpVar::Var(a) = &w else { unreachable!() };
                let Variable::Witness(j) = a.variable else { unreachable!() };
                self.links.push((j, *v));
                self.linked.insert(j);
                Ok(w)
            }
        }
    }

    pub fn import_m31(&mut self, x: &HM31) -> R<M31> {
        Ok(M31 { v: self.import(&x.h)?, bound: x.bound.clone(), ch: 0 })
    }

    pub fn import_e4(&mut self, x: &HE4) -> R<E4> {
        let c: Vec<M31> = x.iter().map(|m| self.import_m31(m)).collect::<R<_>>()?;
        Ok(E4 { c: [c[0].clone(), c[1].clone(), c[2].clone(), c[3].clone()] })
    }

    /// A parent bit (the child re-checks booleanity: one constraint).
    pub fn import_bool(&mut self, x: &H) -> R<Boolean<Fr>> {
        let val = match x {
            H::Const(c) => Some(*c),
            H::Var(_, v) => *v,
        };
        let b = Boolean::new_witness(self.cs.clone(), || val.map(|v| !v.is_zero()).ok_or(SynthesisError::AssignmentMissing))?;
        let p = self.import(x)?;
        FpVar::from(b.clone()).enforce_equal(&p)?;
        Ok(b)
    }

    /// Makes the parent slot `to` equal to the child value `x`.
    pub fn export(&mut self, x: &FpVar<Fr>, to: &H) -> R<()> {
        match &self.mode {
            Mode::Inline => {
                let p = self.import(to)?;
                x.enforce_equal(&p)
            }
            Mode::Child => {
                let H::Var(pv, _) = to else { panic!("export to a constant") };
                let mut m = materialize(&self.cs, x)?;
                let needs_fresh = match &m {
                    FpVar::Var(a) => match a.variable {
                        Variable::Witness(j) => self.linked.contains(&j),
                        _ => true,
                    },
                    FpVar::Constant(_) => true,
                };
                if needs_fresh {
                    let w = FpVar::new_witness(self.cs.clone(), || m.value())?;
                    w.enforce_equal(&m)?;
                    m = w;
                }
                let FpVar::Var(a) = &m else { unreachable!() };
                let Variable::Witness(j) = a.variable else { unreachable!() };
                self.links.push((j, *pv));
                self.linked.insert(j);
                Ok(())
            }
        }
    }

    pub fn export_m31(&mut self, x: &M31, to: &HM31) -> R<()> {
        self.export(&x.v, &to.h)
    }

    pub fn export_e4(&mut self, x: &E4, to: &HE4) -> R<()> {
        for k in 0..4 {
            self.export_m31(&x.c[k], &to[k])?;
        }
        Ok(())
    }
}

/// A synthesised child (or parent) constraint system.
pub struct Part {
    pub matrices: ConstraintMatrices<Fr>,
    pub instance: Vec<Fr>,
    pub witness: Vec<Fr>,
    pub links: Vec<(usize, Variable)>,
}

fn finish(cs: Cs, links: Vec<(usize, Variable)>) -> Part {
    cs.finalize();
    let matrices = cs.to_matrices().expect("matrices");
    let b = cs.borrow().unwrap();
    Part { matrices, instance: b.instance_assignment.clone(), witness: b.witness_assignment.clone(), links }
}

/// Where child bodies run.
pub enum Par<'s, 'e: 's> {
    /// in the parent's constraint system, now
    Inline(Cs),
    /// on their own threads (scoped: joined before `synthesize` returns), merged afterwards
    Threads { scope: &'s std::thread::Scope<'s, 'e>, setup: bool, out: std::sync::Arc<std::sync::Mutex<Vec<(usize, R<Part>)>>>, next: RefCell<usize> },
}

impl<'s, 'e: 's> Par<'s, 'e> {
    pub fn spawn<F>(&self, f: F) -> R<()>
    where
        F: FnOnce(&mut Io) -> R<()> + Send + 's,
    {
        match self {
            Par::Inline(cs) => {
                let mut io = Io { cs: cs.clone(), mode: Mode::Inline, links: vec![], linked: Default::default() };
                f(&mut io)
            }
            Par::Threads { scope, setup, out, next } => {
                let setup = *setup;
                let id = {
                    let mut n = next.borrow_mut();
                    *n += 1;
                    *n - 1
                };
                let out = out.clone();
                std::thread::Builder::new()
                    .stack_size(64 << 20)
                    .spawn_scoped(scope, move || {
                        let cs = new_cs(setup);
                        let mut io = Io { cs: cs.clone(), mode: Mode::Child, links: vec![], linked: Default::default() };
                        let t0 = std::time::Instant::now();
                        let r = f(&mut io).map(|_| {
                            let t1 = t0.elapsed();
                            let p = finish(cs, io.links);
                            if std::env::var("P3_STAGES").is_ok() {
                                eprintln!("  par: child {id}: {} constraints, body {:.2} s + finalize {:.2} s", p.matrices.num_constraints, t1.as_secs_f64(), (t0.elapsed() - t1).as_secs_f64());
                            }
                            p
                        });
                        out.lock().unwrap().push((id, r));
                    })
                    .expect("spawn");
                Ok(())
            }
        }
    }

    pub fn is_inline(&self) -> bool {
        matches!(self, Par::Inline(_))
    }
}

/// One R1CS: matrices and (when proving) the full assignment [1, inputs, witnesses].
pub struct Merged {
    pub matrices: ConstraintMatrices<Fr>,
    pub assignment: Vec<Fr>,
}

/// Runs `body` on a parent constraint system and its children on their own threads, then
/// merges them into one R1CS.
pub fn synthesize<'e, F>(setup: bool, body: F) -> R<Merged>
where
    F: for<'s> FnOnce(&Cs, &Par<'s, 'e>) -> R<()>,
{
    let stages = std::env::var("P3_STAGES").is_ok();
    let t0 = std::time::Instant::now();
    let cs = new_cs(setup);
    let out: std::sync::Arc<std::sync::Mutex<Vec<(usize, R<Part>)>>> = Default::default();
    // the parent is finalized while the children still run
    let parent = std::thread::scope(|scope| {
        let par = Par::Threads { scope, setup, out: out.clone(), next: RefCell::new(0) };
        body(&cs, &par)?;
        if stages {
            eprintln!("  par: parent body {:.2} s", t0.elapsed().as_secs_f64());
        }
        let p = finish(cs, vec![]);
        if stages {
            eprintln!("  par: parent finalized ({} constraints) {:.2} s", p.matrices.num_constraints, t0.elapsed().as_secs_f64());
        }
        Ok::<_, SynthesisError>(p)
    })?;
    if stages {
        eprintln!("  par: children joined {:.2} s", t0.elapsed().as_secs_f64());
    }
    let mut kids: Vec<(usize, R<Part>)> = std::mem::take(&mut *out.lock().unwrap());
    kids.sort_by_key(|k| k.0);
    let kids: Vec<Part> = kids.into_iter().map(|k| k.1).collect::<R<_>>()?;
    if stages {
        let sizes: Vec<usize> = kids.iter().map(|k| k.matrices.num_constraints).collect();
        eprintln!("  par: {} children, constraints {:?}", kids.len(), sizes);
    }
    let m = merge(parent, kids, setup);
    if stages {
        eprintln!("  par: merged {:.2} s", t0.elapsed().as_secs_f64());
    }
    Ok(m)
}

fn merge(parent: Part, kids: Vec<Part>, setup: bool) -> Merged {
    let ni = parent.matrices.num_instance_variables;
    let col = |v: &Variable| match v {
        Variable::One => 0,
        Variable::Instance(i) => *i,
        Variable::Witness(j) => ni + j,
        _ => panic!("link to a non-variable"),
    };
    // column of every child witness
    let mut next = ni + parent.matrices.num_witness_variables;
    let mut maps = Vec::with_capacity(kids.len());
    for k in &kids {
        assert_eq!(k.matrices.num_instance_variables, 1);
        let nw = k.matrices.num_witness_variables;
        let mut map = vec![usize::MAX; nw];
        for (j, v) in &k.links {
            map[*j] = col(v);
        }
        for m in map.iter_mut() {
            if *m == usize::MAX {
                *m = next;
                next += 1;
            }
        }
        maps.push(map);
    }
    let remap = |mut rows: Vec<Vec<(Fr, usize)>>, map: &[usize]| -> Vec<Vec<(Fr, usize)>> {
        rows.par_iter_mut().for_each(|r| r.iter_mut().for_each(|t| t.1 = if t.1 == 0 { 0 } else { map[t.1 - 1] }));
        rows
    };
    let mut a = parent.matrices.a;
    let mut b = parent.matrices.b;
    let mut c = parent.matrices.c;
    let mut assignment = if setup { vec![] } else { [parent.instance.clone(), parent.witness.clone()].concat() };
    // consume the parts one by one so each child's matrices are freed once copied
    for (k, map) in kids.into_iter().zip(&maps) {
        let km = k.matrices;
        a.extend(remap(km.a, map));
        b.extend(remap(km.b, map));
        c.extend(remap(km.c, map));
        if !setup {
            for (j, &m) in map.iter().enumerate() {
                if m >= assignment.len() {
                    assert_eq!(m, assignment.len());
                    assignment.push(k.witness[j]);
                }
            }
        }
    }
    let nnz = |m: &Vec<Vec<(Fr, usize)>>| m.iter().map(|r| r.len()).sum();
    let matrices = ConstraintMatrices {
        num_instance_variables: ni,
        num_witness_variables: next - ni,
        num_constraints: a.len(),
        a_num_non_zero: nnz(&a),
        b_num_non_zero: nnz(&b),
        c_num_non_zero: nnz(&c),
        a,
        b,
        c,
    };
    Merged { matrices, assignment }
}

impl Merged {
    /// A z o B z == C z for every row (parallel).
    pub fn is_satisfied(&self) -> bool {
        let z = &self.assignment;
        let dot = |r: &Vec<(Fr, usize)>| r.iter().fold(Fr::zero(), |acc, &(c, i)| acc + c * z[i]);
        let m = &self.matrices;
        (0..m.num_constraints).into_par_iter().all(|i| dot(&m.a[i]) * dot(&m.b[i]) == dot(&m.c[i]))
    }

    /// The first unsatisfied row, if any.
    pub fn first_unsatisfied(&self) -> Option<usize> {
        let z = &self.assignment;
        let dot = |r: &Vec<(Fr, usize)>| r.iter().fold(Fr::zero(), |acc, &(c, i)| acc + c * z[i]);
        let m = &self.matrices;
        (0..m.num_constraints).into_par_iter().find_first(|&i| dot(&m.a[i]) * dot(&m.b[i]) != dot(&m.c[i]))
    }
}

/// Replays merged matrices as a circuit (for the Groth16 setup).
pub struct MatrixCircuit<'a>(pub &'a ConstraintMatrices<Fr>);

impl ConstraintSynthesizer<Fr> for MatrixCircuit<'_> {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> R<()> {
        let m = self.0;
        let ins: Vec<Variable> = (1..m.num_instance_variables).map(|_| cs.new_input_variable(|| Ok(Fr::zero()))).collect::<R<_>>()?;
        let wit: Vec<Variable> = (0..m.num_witness_variables).map(|_| cs.new_witness_variable(|| Ok(Fr::zero()))).collect::<R<_>>()?;
        let var = |i: usize| if i == 0 { Variable::One } else if i < m.num_instance_variables { ins[i - 1] } else { wit[i - m.num_instance_variables] };
        let lc = |r: &Vec<(Fr, usize)>| LinearCombination(r.iter().map(|&(c, i)| (c, var(i))).collect());
        for i in 0..m.num_constraints {
            cs.enforce_constraint(lc(&m.a[i]), lc(&m.b[i]), lc(&m.c[i]))?;
        }
        Ok(())
    }
}
