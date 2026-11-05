//! R8.3: the STARK verifier (`ss_rap_v2::stark::verify_air`, HashMode::Poseidon, 5 lanes) as BN254
//! constraints, for an AIR given in circuit form (`AirCircuit`).
//!
//! Mirrors the native verifier step by step: the transcript (statement, shape, rows, roots,
//! alpha/beta/rho, gamma, delta), FRI, then per query the 4 openings authenticated in the 3 trees
//! and, per lane at x and -x, the composition C(x) = Q(x) (x^N - 1) and the FRI combination
//! f(x) = layer-0 value. The algebra is lazy: sums of products accumulate in the native field
//! with powers of gamma / delta precomputed once, and each check reduces once.
//!
//! The public bus sum S (initial and final account states, transactions) is computed here from
//! the public tuples under the circuit's beta and rho.

use super::fp31::{range_witness, E4, M31};
use super::fri_var::{verify_fri, FriProofVar, Lanes};
use super::hash_var::{digest_witness, leaf_hash, merkle_root, value31, TranscriptVar};
use super::statement_var::StatementVar;
use ark_bn254::Fr;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use num_bigint::BigUint;
use ss_rap_v2::ntt::root_of_unity;
use ss_rap_v2::stark::{shift, table_coeffs, StarkParams, StarkProof, TABLE};
use ss_rap_v2::{mod_inv_single, mul_mod_channel, Extension4, DEFAULT_RNS_CHANNELS, EXTENSION_BETA, RNS_MODULI};

type R<T> = Result<T, SynthesisError>;

/// A bus tuple in circuit form: (tag, values, weight).
pub type TupleVar = (u32, Vec<M31>, M31);

/// An AIR the circuit can evaluate (the in-circuit twin of `ss_rap_v2::stark::Air`).
pub trait AirCircuit {
    /// Absorbs the statement message (`stark/statement`) as the native transcript does.
    fn absorb_statement(&self, t: &mut TranscriptVar) -> R<()>;
    fn width(&self) -> usize;
    fn byte_cols(&self) -> usize;
    fn num_bus(&self) -> usize;
    /// Constraint values (lazy, reduced mod m only by the caller's final check).
    fn eval(&self, c: &[M31], nx: &[M31], first_row: &M31, not_last: &M31, ch: usize) -> Vec<M31>;
    fn bus_tuples(&self, c: &[M31], ch: usize) -> Vec<TupleVar>;
    /// The public tuples of lane `ch`, as the native `public_tuples`.
    fn public_tuples(&self, ch: usize) -> Vec<TupleVar>;
}

fn ext_witness(cs: &ConstraintSystemRef<Fr>, x: Option<[u32; 4]>, ch: usize) -> R<E4> {
    let [a, b, c, d] = [0, 1, 2, 3].map(|k| value31(cs, x.map(|v| v[k]), ch));
    Ok(E4 { c: [a?, b?, c?, d?] })
}

fn e4_const(x: Extension4, ch: usize) -> E4 {
    E4 { c: x.c.map(|v| M31::constant(v, ch)) }
}

fn e4_zero(ch: usize) -> E4 {
    e4_const(Extension4::ZERO, ch)
}

/// Reduces when the bound gets large (keeps later products under the 240-bit limit).
fn tame(x: &M31, cs: &ConstraintSystemRef<Fr>, bits: u64) -> R<M31> {
    if x.bound.bits() > bits {
        x.reduce(cs)
    } else {
        Ok(x.clone())
    }
}

fn tame_e4(x: &E4, cs: &ConstraintSystemRef<Fr>, bits: u64) -> R<E4> {
    let [a, b, c, d] = [0, 1, 2, 3].map(|k| tame(&x.c[k], cs, bits));
    Ok(E4 { c: [a?, b?, c?, d?] })
}

/// Powers p^1..p^n, reduced.
fn powers(cs: &ConstraintSystemRef<Fr>, p: &E4, n: usize) -> R<Vec<E4>> {
    let mut out = Vec::with_capacity(n);
    let mut acc = p.clone();
    for _ in 0..n {
        out.push(acc.clone());
        acc = acc.mul(p).reduce(cs)?;
    }
    Ok(out)
}

/// beta - tag rho - sum_i v_i rho^(i+2) (`Challenges::fingerprint`), lazy; `rho_pows[k]` = rho^(k+1).
fn fingerprint(beta: &E4, rho_pows: &[E4], tag: &M31, values: &[M31]) -> E4 {
    let mut acc = rho_pows[0].mul_base(tag);
    for (i, v) in values.iter().enumerate() {
        acc = acc.add(&rho_pows[i + 1].mul_base(v));
    }
    beta.sub(&acc)
}

pub struct OpeningVar {
    pub main: Lanes<Vec<M31>>,
    pub aux: Lanes<Vec<E4>>,
    pub q: Lanes<E4>,
    pub main_path: Vec<FpVar<Fr>>,
    pub aux_path: Vec<FpVar<Fr>>,
    pub q_path: Vec<FpVar<Fr>>,
}

pub struct StarkProofVar {
    pub main_root: FpVar<Fr>,
    pub aux_root: FpVar<Fr>,
    pub q_root: FpVar<Fr>,
    pub openings: Vec<[OpeningVar; 4]>,
    pub fri: FriProofVar,
}

fn lanes<T, F: FnMut(usize) -> R<T>>(mut f: F) -> R<Lanes<T>> {
    let v: Vec<T> = (0..DEFAULT_RNS_CHANNELS).map(&mut f).collect::<R<Vec<T>>>()?;
    Ok(v.try_into().unwrap_or_else(|_| unreachable!()))
}

impl StarkProofVar {
    pub fn witness<A: AirCircuit>(cs: &ConstraintSystemRef<Fr>, air: &A, proof: Option<&StarkProof>, params: &StarkParams) -> R<Self> {
        let main_cols = air.width() + 1;
        let aux_cols = air.byte_cols() + 1 + air.num_bus() + 1;
        let depth = (params.log_rows + params.log_blowup) as usize;
        let main_root = digest_witness(cs, proof.map(|p| &p.main_root))?;
        let aux_root = digest_witness(cs, proof.map(|p| &p.aux_root))?;
        let q_root = digest_witness(cs, proof.map(|p| &p.q_root))?;
        let mut openings = Vec::with_capacity(params.num_queries);
        for q in 0..params.num_queries {
            let mut four = Vec::with_capacity(4);
            for k in 0..4 {
                let o = proof.map(|p| &p.openings[q][k]);
                let main = lanes(|ch| (0..main_cols).map(|c| value31(cs, o.map(|o| o.main[ch][c]), ch)).collect())?;
                let aux = lanes(|ch| (0..aux_cols).map(|c| ext_witness(cs, o.map(|o| o.aux[ch][c].c), ch)).collect())?;
                let qv = lanes(|ch| ext_witness(cs, o.map(|o| o.quotient[ch].c), ch))?;
                let path = |f: fn(&ss_rap_v2::stark::Opening) -> &Vec<ss_rap_v2::hash::Hash>| -> R<Vec<FpVar<Fr>>> { (0..depth).map(|d| digest_witness(cs, o.map(|o| &f(o)[d]))).collect() };
                four.push(OpeningVar { main, aux, q: qv, main_path: path(|o| &o.main_path)?, aux_path: path(|o| &o.aux_path)?, q_path: path(|o| &o.q_path)? });
            }
            openings.push(four.try_into().unwrap_or_else(|_| unreachable!()));
        }
        let fri = FriProofVar::witness(cs, proof.map(|p| &p.fri), &params.fri())?;
        Ok(Self { main_root, aux_root, q_root, openings, fri })
    }
}

fn pow_const(b: u32, e: u64, ch: usize) -> u32 {
    let (mut b, mut e, mut r) = (b, e, 1u32);
    while e > 0 {
        if e & 1 == 1 {
            r = mul_mod_channel(r, b, ch);
        }
        b = mul_mod_channel(b, b, ch);
        e >>= 1;
    }
    r
}

/// x^(2^k), reduced.
fn pow2k(cs: &ConstraintSystemRef<Fr>, x: &M31, k: u32) -> R<M31> {
    let mut y = x.reduce(cs)?;
    for _ in 0..k {
        y = y.mul(&y).reduce(cs)?;
    }
    Ok(y)
}

/// The verifier. `rows` is the public work count; `label` the transcript label.
pub fn verify_stark<A: AirCircuit>(cs: &ConstraintSystemRef<Fr>, air: &A, p: &StarkProofVar, params: &StarkParams, rows: usize, label: &[u8]) -> R<()> {
    let n_rows = 1usize << params.log_rows;
    let blowup = 1usize << params.log_blowup;
    let n = n_rows * blowup;
    let (w, bytes, nbus) = (air.width(), air.byte_cols(), air.num_bus());
    let (main_cols, aux_cols) = (w + 1, bytes + 1 + nbus + 1);
    let (inv_t, bus0, sum_col) = (bytes, bytes + 1, bytes + 1 + nbus);

    let mut t = TranscriptVar::new(cs, label)?;
    air.absorb_statement(&mut t)?;
    t.absorb_const(b"stark/shape", &[params.log_rows as u8, params.log_blowup as u8, params.num_queries as u8])?;
    t.absorb_const(b"stark/rows", &(rows as u64).to_le_bytes())?;
    t.absorb_root(b"stark/main", &p.main_root)?;
    let alpha = t.challenge_ext4_all()?;
    let beta = t.challenge_ext4_all()?;
    let rho = t.challenge_ext4_all()?;
    t.absorb_root(b"stark/aux", &p.aux_root)?;
    let gamma = t.challenge_ext4_all()?;
    t.absorb_root(b"stark/quotient", &p.q_root)?;
    let delta = t.challenge_ext4_all()?;
    let shifts: Lanes<u32> = std::array::from_fn(shift);
    let fri = verify_fri(cs, &mut t, &p.fri, &params.fri(), &shifts)?;

    // ---- per lane, once: powers, S / N
    let max_len = 16;
    let n_terms = air.eval(&vec![M31::constant(0, 0); main_cols], &vec![M31::constant(0, 0); main_cols], &M31::constant(0, 0), &M31::constant(0, 0), 0).len() + bytes + 1 + nbus + 1;
    let mut gam = Vec::new();
    let mut del = Vec::new();
    let mut rhos = Vec::new();
    let mut s_over_n = Vec::new();
    for ch in 0..DEFAULT_RNS_CHANNELS {
        gam.push(powers(cs, &gamma[ch], n_terms)?); // gam[k] = gamma^(k+1)
        del.push(powers(cs, &delta[ch], main_cols + aux_cols)?);
        let rp = powers(cs, &rho[ch], max_len + 1)?;
        // S = sum_t w_t / fp_t over the public tuples
        let mut s = e4_zero(ch);
        for (tag, vs, wt) in air.public_tuples(ch) {
            let fp = fingerprint(&beta[ch], &rp, &M31::constant(tag, ch), &vs);
            let fv = fp.value().map(|c| Extension4::new(c[0], c[1], c[2], c[3]));
            let inv = ext_witness(cs, fv.map(|f| f.inverse(ch).c), ch)?;
            inv.mul(&fp).sub(&e4_const(Extension4::ONE, ch)).assert_zero(cs)?;
            s = tame_e4(&s.add(&inv.mul_base(&wt)), cs, 200)?;
        }
        let n_inv = mod_inv_single(n_rows as u32 % RNS_MODULI[ch], RNS_MODULI[ch]);
        s_over_n.push(E4 { c: std::array::from_fn(|k| s.c[k].mul_const(n_inv)) }.reduce(cs)?);
        rhos.push(rp);
    }

    let log_n = (n.trailing_zeros()) as usize;
    let k_bits = log_n - 1;
    for (q, opens) in p.openings.iter().enumerate() {
        let ib = &fri.index_bits[q];
        // positions: i, j = i + n/2, (i + blowup) mod n, (j + blowup) mod n
        let ival = ib.iter().enumerate().fold(None::<usize>, |a, (k, b)| b.value().ok().map(|v| a.unwrap_or(0) | ((v as usize) << k)));
        let s_val = ival.map(|i| i + blowup);
        let sb: Vec<Boolean<Fr>> = (0..log_n).map(|k| Boolean::new_witness(cs.clone(), || s_val.map(|s| (s >> k) & 1 == 1).ok_or(SynthesisError::AssignmentMissing))).collect::<R<_>>()?;
        let lhs = Boolean::le_bits_to_fp(&sb)?;
        let rhs = Boolean::le_bits_to_fp(ib)? + FpVar::constant(Fr::from(blowup as u64));
        lhs.enforce_equal(&rhs)?;
        let mut pos: Vec<Vec<Boolean<Fr>>> = Vec::new();
        pos.push([ib.clone(), vec![Boolean::FALSE]].concat());
        pos.push([ib.clone(), vec![Boolean::TRUE]].concat());
        pos.push(sb.clone());
        pos.push([sb[..k_bits].to_vec(), vec![!sb[k_bits].clone()]].concat());
        for (o, bits) in opens.iter().zip(&pos) {
            let mv: Vec<FpVar<Fr>> = o.main.iter().flatten().map(|x| x.v.clone()).collect();
            let av: Vec<FpVar<Fr>> = o.aux.iter().flatten().flat_map(|e| e.c.iter().map(|x| x.v.clone())).collect();
            let qv: Vec<FpVar<Fr>> = o.q.iter().flat_map(|e| e.c.iter().map(|x| x.v.clone())).collect();
            merkle_root(cs, &leaf_hash(cs, b"SS-RAP/v2/main", &mv)?, bits, &o.main_path)?.enforce_equal(&p.main_root)?;
            merkle_root(cs, &leaf_hash(cs, b"SS-RAP/v2/aux", &av)?, bits, &o.aux_path)?.enforce_equal(&p.aux_root)?;
            merkle_root(cs, &leaf_hash(cs, b"SS-RAP/v2/quotient", &qv)?, bits, &o.q_path)?.enforce_equal(&p.q_root)?;
        }
        for slot in 0..2 {
            let (here, next) = (&opens[slot], &opens[slot + 2]);
            for ch in 0..DEFAULT_RNS_CHANNELS {
                let m = RNS_MODULI[ch];
                let x0 = &fri.x0[q][ch];
                let x = if slot == 0 { x0.clone() } else { M31::constant(0, ch).sub(x0) };
                // x^N, the table value t(x^(N/256)), first_row, not_last
                let xn = pow2k(cs, &x, params.log_rows)?;
                let y = pow2k(cs, &x, params.log_rows - TABLE.trailing_zeros())?;
                let tc = table_coeffs(ch);
                let mut tv = M31::constant(0, ch);
                for &c in tc.iter().rev() {
                    tv = tame(&tv.mul(&y).add(&M31::constant(c, ch)), cs, 190)?;
                }
                let xr = x.reduce(cs)?;
                let one = M31::constant(1, ch);
                let xn1 = xn.sub(&one);
                let fr_val = match (xr.value(), xn1.value()) {
                    (Some(xv), Some(a)) => Some(mul_mod_channel(a, mod_inv_single((xv + m - 1) % m, m), ch)),
                    _ => None,
                };
                let first_row = M31 { v: range_witness(cs, fr_val.map(BigUint::from), 31)?, bound: BigUint::from(1u64 << 31), ch };
                first_row.mul(&xr.sub(&one)).sub(&xn1).assert_zero(cs)?;
                let last = pow_const(root_of_unity(n_rows, ch), (n_rows - 1) as u64, ch);
                let not_last = xr.sub(&M31::constant(last, ch));

                let (mn, mx) = (&here.main[ch], &next.main[ch]);
                let aux = &here.aux[ch];
                let mut terms: Vec<E4> = air.eval(mn, mx, &first_row, &not_last, ch).iter().map(E4::from_base).collect();
                let a = &alpha[ch];
                let one4 = e4_const(Extension4::ONE, ch);
                let mut sum = e4_zero(ch);
                for c in 0..bytes {
                    terms.push(aux[c].mul(&a.sub(&E4::from_base(&mn[c]))).sub(&one4));
                    sum = sum.add(&aux[c]);
                }
                terms.push(aux[inv_t].mul(&a.sub(&E4::from_base(&tv))).sub(&one4));
                sum = sum.sub(&aux[inv_t].mul_base(&mn[w]));
                for (k, (tag, vals, wt)) in air.bus_tuples(mn, ch).into_iter().enumerate() {
                    let den = tame_e4(&fingerprint(&beta[ch], &rhos[ch], &M31::constant(tag, ch), &vals), cs, 100)?;
                    terms.push(aux[bus0 + k].mul(&den).sub(&one4));
                    sum = sum.add(&aux[bus0 + k].mul_base(&wt));
                }
                let sum = tame_e4(&sum, cs, 100)?;
                terms.push(next.aux[ch][sum_col].sub(&aux[sum_col]).sub(&sum).add(&s_over_n[ch]));
                assert_eq!(terms.len(), n_terms);
                // C = sum_k v_k gamma^(T-1-k)
                let mut c_acc = terms[n_terms - 1].clone();
                for (k, v) in terms.iter().enumerate().take(n_terms - 1) {
                    let v = tame_e4(v, cs, 120)?;
                    c_acc = tame_e4(&c_acc.add(&v.mul(&gam[ch][n_terms - 2 - k])), cs, 200)?;
                }
                let qx = here.q[ch].mul_base(&xn1);
                c_acc.sub(&qx).assert_zero(cs)?;
                // f = Q + sum_i main_i delta^(i+1) + sum_i aux_i delta^(main_cols+i+1)
                let mut f = here.q[ch].clone();
                for (i, v) in mn.iter().enumerate() {
                    f = tame_e4(&f.add(&del[ch][i].mul_base(v)), cs, 200)?;
                }
                for (i, v) in aux.iter().enumerate() {
                    f = tame_e4(&f.add(&del[ch][main_cols + i].mul(v)), cs, 200)?;
                }
                let layer0 = &p.fri.queries[q][0].pair[ch][slot];
                f.sub(layer0).assert_zero(cs)?;
                let _ = EXTENSION_BETA;
            }
        }
    }
    Ok(())
}

// ---- the state AIR in circuit form -------------------------------------------------------------

pub struct StateCircuit {
    pub stmt: StatementVar,
}

impl AirCircuit for StateCircuit {
    fn absorb_statement(&self, t: &mut TranscriptVar) -> R<()> {
        t.absorb_prefixed_digest(b"stark/statement", b"state-transfer-2", &self.stmt.digest)
    }
    fn width(&self) -> usize {
        ss_rap_v2::state::WIDTH
    }
    fn byte_cols(&self) -> usize {
        ss_rap_v2::state::BYTE_COLS
    }
    fn num_bus(&self) -> usize {
        5
    }
    fn eval(&self, c: &[M31], nx: &[M31], first_row: &M31, not_last: &M31, ch: usize) -> Vec<M31> {
        use ss_rap_v2::state::*;
        let k = |v: u32| M31::constant(v, ch);
        let one = k(1);
        let mut out = Vec::with_capacity(CONSTRAINTS);
        let two_t = c[T].add(&c[T]);
        out.push(c[ACTIVE].mul(&c[ACTIVE].sub(&one)));
        out.push(c[T].sub(&one).mul(first_row));
        out.push(nx[T].sub(&c[T]).sub(&one).mul(not_last));
        let d1 = c[D1].add(&c[D1 + 1].mul_const(256));
        out.push(d1.sub(&two_t.sub(&c[TR1]).sub(&one)));
        let d2 = c[D2].add(&c[D2 + 1].mul_const(256));
        out.push(d2.sub(&two_t.sub(&c[TR2])));
        for (lhs, rhs, carry) in [(FROM_NEW, FROM_OLD, CF), (TO_OLD, TO_NEW, CT)] {
            for b in 0..8 {
                let mut v = c[lhs + b].add(&c[AMT + b]);
                if b > 0 {
                    v = v.add(&c[carry + b - 1]);
                }
                v = v.sub(&c[rhs + b]);
                if b < 7 {
                    v = v.sub(&c[carry + b].mul_const(256));
                }
                out.push(v);
            }
            for b in 0..7 {
                out.push(c[carry + b].mul(&c[carry + b].sub(&one)));
            }
        }
        out
    }
    fn bus_tuples(&self, c: &[M31], ch: usize) -> Vec<TupleVar> {
        use ss_rap_v2::state::*;
        let k = |v: u32| M31::constant(v, ch);
        let two_t = c[T].add(&c[T]);
        let act = c[ACTIVE].clone();
        let neg = k(0).sub(&act);
        let mem = |id: &M31, nonce: M31, ts: M31, bal: &[M31]| -> Vec<M31> { [vec![id.clone(), nonce, ts], bal.to_vec()].concat() };
        let mut tx = vec![c[T].clone(), c[FROM_ID].clone(), c[TO_ID].clone(), c[NONCE].clone()];
        tx.extend_from_slice(&c[AMT..AMT + 8]);
        vec![
            (TAG_MEM, mem(&c[FROM_ID], c[NONCE].clone(), c[TR1].clone(), &c[FROM_OLD..FROM_OLD + 8]), act.clone()),
            (TAG_MEM, mem(&c[FROM_ID], c[NONCE].add(&k(1)), two_t.clone(), &c[FROM_NEW..FROM_NEW + 8]), neg.clone()),
            (TAG_MEM, mem(&c[TO_ID], c[TO_NONCE].clone(), c[TR2].clone(), &c[TO_OLD..TO_OLD + 8]), act),
            (TAG_MEM, mem(&c[TO_ID], c[TO_NONCE].clone(), two_t.add(&k(1)), &c[TO_NEW..TO_NEW + 8]), neg.clone()),
            (TAG_TX, tx, neg),
        ]
    }
    fn public_tuples(&self, ch: usize) -> Vec<TupleVar> {
        self.stmt.public_tuples(ch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wrapper::statement_var::StatementShape;
    use ark_relations::r1cs::ConstraintSystem;
    use ss_rap_v2::hash::HashMode;
    use ss_rap_v2::state::{self, AccountState, Transfer};
    use ss_rap_v2::transcript::Transcript;

    const P: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 2 };

    fn case() -> state::StateStatement {
        let accounts = 12usize;
        let addrs: Vec<[u8; 20]> = (0..accounts).map(|i| [i as u8 + 1; 20]).collect();
        let old: Vec<AccountState> = (0..accounts).map(|i| AccountState { balance: 1_000_000 + i as u64, nonce: 0 }).collect();
        let mut nonces = vec![0u32; accounts];
        let txs: Vec<Transfer> = (0..20u32)
            .map(|k| {
                let from = (k * 5 + 1) % accounts as u32;
                let tx = Transfer { from, to: (k * 7 + 3) % accounts as u32, amount: 10 + k as u64, nonce: nonces[from as usize] };
                nonces[from as usize] += 1;
                tx
            })
            .collect();
        state::build(&addrs, &old, &txs, P.log_rows, true).unwrap().0
    }

    fn run(st: &state::StateStatement, proof: &StarkProof) -> (bool, usize) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let air = StateCircuit { stmt: StatementVar::witness(&cs, Some(st), StatementShape::of(st, P.log_rows)).unwrap() };
        let pv = StarkProofVar::witness(&cs, &air, Some(proof), &P).unwrap();
        verify_stark(&cs, &air, &pv, &P, st.num_txs(), b"r8-stark").unwrap();
        (cs.is_satisfied().unwrap(), cs.num_constraints())
    }

    #[test]
    fn state_proof_verifies_in_circuit_and_forgeries_do_not() {
        let accounts = 12usize;
        let addrs: Vec<[u8; 20]> = (0..accounts).map(|i| [i as u8 + 1; 20]).collect();
        let old: Vec<AccountState> = (0..accounts).map(|i| AccountState { balance: 1_000_000 + i as u64, nonce: 0 }).collect();
        let st = case();
        let mut nonces = vec![0u32; accounts];
        let txs: Vec<Transfer> = (0..20u32)
            .map(|k| {
                let from = (k * 5 + 1) % accounts as u32;
                let tx = Transfer { from, to: (k * 7 + 3) % accounts as u32, amount: 10 + k as u64, nonce: nonces[from as usize] };
                nonces[from as usize] += 1;
                tx
            })
            .collect();
        let (_, traces) = state::build(&addrs, &old, &txs, P.log_rows, true).unwrap();
        let t = || Transcript::with_mode(b"r8-stark", HashMode::Poseidon);
        let proof = state::prove(&st, &traces, &P, &mut t());
        assert!(state::verify(&st, &st.old_root(), &st.new_root(), &proof, &P, &mut t()), "native");
        let (ok, n) = run(&st, &proof);
        assert!(ok, "honest proof in circuit");
        eprintln!("state STARK verifier: {n} constraints ({} queries, blowup {})", P.num_queries, 1 << P.log_blowup);

        // an opened value changed (and its leaf no longer matches)
        let mut bad = proof.clone();
        bad.openings[1][0].main[2][7] = (bad.openings[1][0].main[2][7] + 1) % RNS_MODULI[2];
        assert!(!run(&st, &bad).0, "opened value");
        // a quotient value changed
        let mut bad = proof.clone();
        bad.openings[0][1].quotient[4] = bad.openings[0][1].quotient[4].add(&Extension4::ONE, 4);
        assert!(!run(&st, &bad).0, "quotient");
        // another statement (a different final balance)
        let mut st2 = st.clone();
        st2.states[DEFAULT_RNS_CHANNELS][3].balance += 1;
        assert!(!run(&st2, &proof).0, "other statement");
    }
}
