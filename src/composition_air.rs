//! AIR of the composition checks of one lane (docs/REKURSIONI.md, R6.2b).
//!
//! The second half of the STARK verifier's algebra. For every FRI query q and slot (x, -x) the
//! verifier of an inner proof checks, in the lane's field F_{m_j}:
//!
//!   1. C(x) = Q(x) * (x^N - 1), where C = sum_k gamma^k * constraint_k is the composition of
//!      the inner AIR's constraints (its own `eval`), the LogUp byte range check, the bus
//!      inverses and the running-sum step, all at the opened values;
//!   2. f(x) = Q(x) + sum_k delta^(k+1) * column_k(x) is the value FRI opened at layer 0.
//!
//! This AIR does exactly that, one row per (query, slot), for any inner AIR whose bus terms
//! are linear tuples (`Air::bus_tuples`). Every derived quantity gets columns so that every
//! constraint has degree <= 2:
//!   - x^(2^k) up to x^N, the first-row selector (x^N - 1) / (x - 1) and x - w^(N-1);
//!   - the byte table T(x) = t(x^(N/256)) by Horner over t's 256 coefficients;
//!   - every bus fingerprint beta - sum rho^(i+1) v_i by Horner over rho;
//!   - the composition by Horner over gamma, and the FRI combination by Horner over delta.
//!
//! The row's opened values (here: main + aux + quotient, next: main + running sum) are the
//! witness; in R7 they are tied to the Merkle AIR's leaves. The public claim goes on one LogUp
//! bus, one tuple per row: (q, slot, x, f, alpha, beta, rho, gamma, delta, S/N).

use crate::stark::{shift, table_coeffs, Air, BusTerm, BusTuple, Challenges, Point, StarkParams, TABLE};
use crate::{add_mod, mul_mod_channel, sub_mod, Extension4, DEFAULT_RNS_CHANNELS, RNS_MODULI};

const TAG: u32 = 9;

/// One opening the inner verifier checks.
#[derive(Clone, Debug)]
pub struct OpeningClaim {
    pub q: usize,
    pub slot: usize,
    /// Position in the inner LDE domain.
    pub pos: usize,
    /// FRI layer-0 value at this position.
    pub f: Extension4,
}

/// The opened values of one row (witness).
#[derive(Clone, Debug)]
pub struct OpenedRow {
    pub main: Vec<u32>,
    pub main_next: Vec<u32>,
    pub aux: Vec<Extension4>,
    pub aux_next: Vec<Extension4>,
    pub quotient: Extension4,
    pub quotient_next: Extension4,
}

/// Leaves of one composition row, in the order of their leaf ids: the three trees at x, then
/// the three trees at the next row's point.
pub const LEAVES_PER_ROW: usize = 6;
const LEAF_TAGS: [&[u8]; 3] = [b"SS-RAP/v2/main", b"SS-RAP/v2/aux", b"SS-RAP/v2/quotient"];

/// Leaf id of (row = 2 q + slot, kind).
pub fn leaf_id(row: usize, kind: usize) -> usize {
    LEAVES_PER_ROW * row + kind
}

pub struct CompositionAir<'a, A: Air> {
    pub inner: &'a A,
    pub lane: usize,
    pub inner_params: StarkParams,
    pub chals: Challenges,
    pub gamma: Extension4,
    pub delta: Extension4,
    pub s_over_n: Extension4,
    pub claims: Vec<OpeningClaim>,
    /// Send (q, slot, x, f) to the FRI fold AIR in the same stack instead of to the public
    /// claim (R7): then x and f need not be public.
    pub link_fri: bool,
    /// Send every opened leaf, in 8-word chunks, to the leaf hash AIR (R7): `leaf_air`.
    pub link_leaves: bool,
    lay: Lay,
    table: Vec<u32>,
}

/// Column offsets.
#[derive(Clone, Debug)]
struct Lay {
    // inner shape
    w: usize,
    bytes: usize,
    nbus: usize,
    mc: usize,
    ac: usize,
    log_rows: usize,
    bus_len: Vec<usize>,
    // outer columns
    act: usize,
    qs: usize,
    x: usize,
    xp: usize,
    fr: usize,
    tacc: usize,
    hm: usize,
    nm: usize,
    ha: usize,
    na: usize,
    qc: usize,
    nq: usize,
    chal: usize, // alpha, beta, rho, gamma, delta, s/n: 6 x 4
    bh: Vec<usize>,
    ga: usize,
    nterms: usize,
    da: usize,
    f: usize,
    width: usize,
}

impl Lay {
    fn new<A: Air>(inner: &A, p: &StarkParams, ch: usize) -> Self {
        let (w, bytes, nbus) = (inner.width(), inner.byte_cols(), inner.num_bus());
        let mc = w + 1;
        let ac = bytes + 1 + nbus + 1;
        let log_rows = p.log_rows as usize;
        let mut tuples = Vec::new();
        inner.bus_tuples(&vec![0u32; w], ch, &mut tuples);
        assert_eq!(tuples.len(), nbus);
        let bus_len: Vec<usize> = tuples.iter().map(|t| t.values.len()).collect();
        let mut at = 0usize;
        let mut take = |k: usize| {
            let s = at;
            at += k;
            s
        };
        let act = take(1);
        let qs = take(2);
        let x = take(1);
        let xp = take(log_rows);
        let fr = take(1);
        let tacc = take(TABLE - 1);
        let hm = take(mc);
        let nm = take(mc);
        let ha = take(4 * ac);
        let na = take(4 * ac);
        let qc = take(4);
        let nq = take(4);
        let chal = take(24);
        let bh: Vec<usize> = bus_len.iter().map(|&k| take(4 * (k + 1))).collect();
        let nterms = inner.num_constraints() + bytes + 1 + nbus + 1;
        let ga = take(4 * (nterms - 1));
        let da = take(4 * (ac + mc));
        let f = take(4);
        Self { w, bytes, nbus, mc, ac, log_rows, bus_len, act, qs, x, xp, fr, tacc, hm, nm, ha, na, qc, nq, chal, bh, ga, nterms, da, f, width: at }
    }
}

fn ext(row: &[u32], at: usize) -> Extension4 {
    Extension4::new(row[at], row[at + 1], row[at + 2], row[at + 3])
}

/// Fill-or-check helper: in fill mode writes the expected value into the column, in check mode
/// pushes column - expected.
struct Walk<'r> {
    row: &'r mut [u32],
    out: Option<&'r mut Vec<u32>>,
    ch: usize,
}

impl Walk<'_> {
    fn base(&mut self, col: usize, expect: u32) {
        match self.out.as_deref_mut() {
            Some(o) => o.push(sub_mod(self.row[col], expect, RNS_MODULI[self.ch])),
            None => self.row[col] = expect,
        }
    }
    fn ext(&mut self, col: usize, expect: Extension4) {
        match self.out.as_deref_mut() {
            Some(o) => o.extend(ext(self.row, col).sub(&expect, self.ch).c),
            None => self.row[col..col + 4].copy_from_slice(&expect.c),
        }
    }
    /// A constraint with no column (checked only).
    fn zero(&mut self, v: Extension4) {
        if let Some(o) = self.out.as_deref_mut() {
            o.extend(v.c);
        }
    }
    fn zero_base(&mut self, v: u32) {
        if let Some(o) = self.out.as_deref_mut() {
            o.push(v);
        }
    }
}

impl<'a, A: Air> CompositionAir<'a, A> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(inner: &'a A, lane: usize, inner_params: StarkParams, chals: Challenges, gamma: Extension4, delta: Extension4, s_over_n: Extension4, claims: Vec<OpeningClaim>) -> Self {
        let lay = Lay::new(inner, &inner_params, lane);
        Self { inner, lane, inner_params, chals, gamma, delta, s_over_n, claims, link_fri: false, link_leaves: false, lay, table: table_coeffs(lane) }
    }

    fn n_lde(&self) -> usize {
        1usize << (self.inner_params.log_rows + self.inner_params.log_blowup)
    }

    fn x_of(&self, pos: usize) -> u32 {
        let ch = self.lane;
        mul_mod_channel(shift(ch), crate::stark::pow(crate::ntt::root_of_unity(self.n_lde(), ch), pos as u64, ch), ch)
    }

    fn public_tuple(&self, c: &OpeningClaim) -> Vec<u32> {
        let mut v = vec![c.q as u32, c.slot as u32];
        for e in [self.chals.alpha, self.chals.beta, self.chals.rho, self.gamma, self.delta, self.s_over_n] {
            v.extend(e.c);
        }
        v
    }

    fn row_tuple(&self, row: &[u32]) -> Vec<u32> {
        let l = &self.lay;
        let mut v = vec![row[l.qs], row[l.qs + 1]];
        v.extend_from_slice(&row[l.chal..l.chal + 24]);
        v
    }

    /// (q, slot, x, f): to the FRI fold AIR, or to the public claim.
    fn layer0_tuple(&self, row: &[u32]) -> Vec<u32> {
        let l = &self.lay;
        let mut v = vec![row[l.qs], row[l.qs + 1], row[l.x]];
        v.extend_from_slice(&row[l.f..l.f + 4]);
        v
    }

    /// The leaf values of the 6 opened leaves of a row: (kind, tag word + values).
    fn leaf_values(&self, row: &[u32]) -> [Vec<u32>; LEAVES_PER_ROW] {
        let l = &self.lay;
        let ch = self.lane;
        let with_tag = |kind: usize, vals: &[u32]| -> Vec<u32> {
            let mut v = vec![crate::hash::tag_word_ch(LEAF_TAGS[kind % 3], ch)];
            v.extend_from_slice(vals);
            v
        };
        [
            with_tag(0, &row[l.hm..l.hm + l.mc]),
            with_tag(1, &row[l.ha..l.ha + 4 * l.ac]),
            with_tag(2, &row[l.qc..l.qc + 4]),
            with_tag(3, &row[l.nm..l.nm + l.mc]),
            with_tag(4, &row[l.na..l.na + 4 * l.ac]),
            with_tag(5, &row[l.nq..l.nq + 4]),
        ]
    }

    /// The 6 leaf word lists of an opened row (what `leaf_values` reads from the trace row).
    pub fn leaf_words(&self, o: &OpenedRow) -> [Vec<u32>; LEAVES_PER_ROW] {
        let ch = self.lane;
        let flat = |v: &[Extension4]| -> Vec<u32> { v.iter().flat_map(|e| e.c).collect() };
        let vals: [Vec<u32>; LEAVES_PER_ROW] = [o.main.clone(), flat(&o.aux), o.quotient.c.to_vec(), o.main_next.clone(), flat(&o.aux_next), o.quotient_next.c.to_vec()];
        std::array::from_fn(|kind| {
            let mut v = vec![crate::hash::tag_word_ch(LEAF_TAGS[kind % 3], ch)];
            v.extend_from_slice(&vals[kind]);
            v
        })
    }

    /// Number of 8-word chunks of each leaf kind.
    pub fn leaf_chunks(&self) -> [usize; LEAVES_PER_ROW] {
        let l = &self.lay;
        let c = |n: usize| (n + 1).div_ceil(8);
        [c(l.mc), c(4 * l.ac), c(4), c(l.mc), c(4 * l.ac), c(4)]
    }

    /// Leaf lengths (tag + values) of each kind.
    pub fn leaf_lens(&self) -> [usize; LEAVES_PER_ROW] {
        let l = &self.lay;
        [l.mc + 1, 4 * l.ac + 1, 5, l.mc + 1, 4 * l.ac + 1, 5]
    }

    fn public_layer0(&self, c: &OpeningClaim) -> Vec<u32> {
        let mut v = vec![c.q as u32, c.slot as u32, self.x_of(c.pos)];
        v.extend(c.f.c);
        v
    }

    /// Fills (`out` = None) or checks every derived column of a row.
    fn walk(&self, row: &mut [u32], out: Option<&mut Vec<u32>>) {
        let ch = self.lane;
        let m = RNS_MODULI[ch];
        let l = &self.lay;
        let mut wk = Walk { row, out, ch };
        let mul = |a: u32, b: u32| mul_mod_channel(a, b, ch);
        let checking = wk.out.is_some();
        if checking {
            let a = wk.row[l.act];
            wk.zero_base(mul(a, sub_mod(a, 1, m)));
        }
        // powers of x, first-row selector, table value
        let x = wk.row[l.x];
        let mut prev = x;
        for k in 0..l.log_rows {
            wk.base(l.xp + k, mul(prev, prev));
            prev = wk.row[l.xp + k];
        }
        let xn1 = sub_mod(wk.row[l.xp + l.log_rows - 1], 1, m);
        // fr * (x - 1) = x^N - 1  <=>  fr = (x^N - 1) / (x - 1)
        if checking {
            let fr = wk.row[l.fr];
            wk.zero_base(sub_mod(mul(fr, sub_mod(x, 1, m)), xn1, m));
        } else {
            wk.row[l.fr] = mul(xn1, crate::mod_inv_single(sub_mod(x, 1, m), m));
        }
        let y = if l.log_rows == 8 { x } else { wk.row[l.xp + l.log_rows - 9] };
        let mut acc = self.table[TABLE - 1];
        for k in 1..TABLE {
            wk.base(l.tacc + k - 1, add_mod(mul(acc, y), self.table[TABLE - 1 - k], m));
            acc = wk.row[l.tacc + k - 1];
        }
        let tv = acc;
        let last = crate::stark::pow(crate::ntt::root_of_unity(1 << l.log_rows, ch), (1u64 << l.log_rows) - 1, ch);
        let pt = Point { first_row: wk.row[l.fr], not_last: sub_mod(x, last, m) };

        let main: Vec<u32> = wk.row[l.hm..l.hm + l.mc].to_vec();
        let main_next: Vec<u32> = wk.row[l.nm..l.nm + l.mc].to_vec();
        let aux: Vec<Extension4> = (0..l.ac).map(|k| ext(wk.row, l.ha + 4 * k)).collect();
        let h_next = ext(wk.row, l.na + 4 * (l.ac - 1));
        let q = ext(wk.row, l.qc);
        let [alpha, beta, rho, gamma, delta, s_over_n] = std::array::from_fn(|k| ext(wk.row, l.chal + 4 * k));

        // bus fingerprints
        let mut tuples = Vec::with_capacity(l.nbus);
        self.inner.bus_tuples(&main[..l.w], ch, &mut tuples);
        let mut dens = Vec::with_capacity(l.nbus);
        for (b, tup) in tuples.iter().enumerate() {
            debug_assert_eq!(tup.values.len(), l.bus_len[b]);
            let mut acc = Extension4::ZERO;
            let seq = tup.values.iter().rev().copied().chain(std::iter::once(tup.tag));
            for (s, v) in seq.enumerate() {
                let col = l.bh[b] + 4 * s;
                wk.ext(col, acc.add(&Extension4::from_base(v), ch).mul(&rho, ch));
                acc = ext(wk.row, col);
            }
            dens.push(beta.sub(&acc, ch));
        }

        // composition terms (same order as `stark::composition`)
        let mut terms: Vec<Extension4> = Vec::with_capacity(l.nterms);
        let mut base = Vec::with_capacity(self.inner.num_constraints());
        self.inner.eval(&main[..l.w], &main_next[..l.w], &pt, ch, &mut base);
        terms.extend(base.iter().map(|&c| Extension4::from_base(c)));
        let mut sum = Extension4::ZERO;
        for c in 0..l.bytes {
            terms.push(aux[c].mul(&alpha.sub(&Extension4::from_base(main[c]), ch), ch).sub(&Extension4::ONE, ch));
            sum = sum.add(&aux[c], ch);
        }
        let inv_t = l.bytes;
        terms.push(aux[inv_t].mul(&alpha.sub(&Extension4::from_base(tv), ch), ch).sub(&Extension4::ONE, ch));
        sum = sum.sub(&aux[inv_t].mul_scalar(main[l.w], ch), ch);
        for (k, tup) in tuples.iter().enumerate() {
            let inv = &aux[l.bytes + 1 + k];
            terms.push(inv.mul(&dens[k], ch).sub(&Extension4::ONE, ch));
            sum = sum.add(&inv.mul_scalar(tup.weight, ch), ch);
        }
        terms.push(h_next.sub(&aux[l.ac - 1], ch).sub(&sum, ch).add(&s_over_n, ch));
        debug_assert_eq!(terms.len(), l.nterms);
        let mut acc = Extension4::ZERO;
        for (k, term) in terms.iter().enumerate() {
            let v = acc.mul(&gamma, ch).add(term, ch);
            if k + 1 < terms.len() {
                wk.ext(l.ga + 4 * k, v);
                acc = ext(wk.row, l.ga + 4 * k);
            } else {
                // C(x) = Q(x) (x^N - 1)
                wk.zero(v.sub(&q.mul_scalar(xn1, ch), ch));
            }
        }

        // FRI combination
        let mut acc = Extension4::ZERO;
        let vals = aux.iter().rev().copied().chain(main.iter().rev().map(|&v| Extension4::from_base(v)));
        for (k, v) in vals.enumerate() {
            wk.ext(l.da + 4 * k, acc.mul(&delta, ch).add(&v, ch));
            acc = ext(wk.row, l.da + 4 * k);
        }
        wk.ext(l.f, q.add(&acc.mul(&delta, ch), ch));
    }

    /// Trace of the lane from the opened rows (same order as `claims`).
    pub fn traces(&self, opened: &[OpenedRow], log_rows: u32) -> [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] {
        let l = &self.lay;
        let n = 1usize << log_rows;
        assert_eq!(opened.len(), self.claims.len());
        assert!(!opened.is_empty() && opened.len() <= n);
        let mut rows: Vec<Vec<u32>> = self
            .claims
            .iter()
            .zip(opened)
            .map(|(c, o)| {
                let mut r = vec![0u32; l.width];
                r[l.act] = 1;
                r[l.qs] = c.q as u32;
                r[l.qs + 1] = c.slot as u32;
                r[l.x] = self.x_of(c.pos);
                r[l.hm..l.hm + l.mc].copy_from_slice(&o.main);
                r[l.nm..l.nm + l.mc].copy_from_slice(&o.main_next);
                for (k, a) in o.aux.iter().enumerate() {
                    r[l.ha + 4 * k..l.ha + 4 * k + 4].copy_from_slice(&a.c);
                }
                for (k, a) in o.aux_next.iter().enumerate() {
                    r[l.na + 4 * k..l.na + 4 * k + 4].copy_from_slice(&a.c);
                }
                r[l.qc..l.qc + 4].copy_from_slice(&o.quotient.c);
                r[l.nq..l.nq + 4].copy_from_slice(&o.quotient_next.c);
                for (k, e) in [self.chals.alpha, self.chals.beta, self.chals.rho, self.gamma, self.delta, self.s_over_n].iter().enumerate() {
                    r[l.chal + 4 * k..l.chal + 4 * k + 4].copy_from_slice(&e.c);
                }
                self.walk(&mut r, None);
                r
            })
            .collect();
        let mut pad = rows[0].clone();
        pad[l.act] = 0;
        rows.resize(n, pad);
        std::array::from_fn(|c| if c == self.lane { rows.clone() } else { Vec::new() })
    }
}

impl<A: Air> Air for CompositionAir<'_, A> {
    fn statement(&self) -> Vec<u8> {
        let mut v = b"composition-v1".to_vec();
        v.extend(self.inner.statement());
        for x in [self.lane as u32, self.inner_params.log_rows, self.inner_params.log_blowup, self.claims.len() as u32] {
            v.extend_from_slice(&x.to_le_bytes());
        }
        v.push(self.link_fri as u8);
        for c in &self.claims {
            v.extend(self.public_tuple(c).iter().flat_map(|x| x.to_le_bytes()));
            if !self.link_fri {
                v.extend(self.public_layer0(c).iter().flat_map(|x| x.to_le_bytes()));
            }
        }
        v
    }
    fn width(&self) -> usize {
        self.lay.width
    }
    fn byte_cols(&self) -> usize {
        0
    }
    fn num_constraints(&self) -> usize {
        let mut row = vec![0u32; self.lay.width];
        row[self.lay.x] = 2;
        let mut out = Vec::new();
        self.walk(&mut row.clone(), Some(&mut out));
        out.len()
    }
    fn eval(&self, cur: &[u32], _next: &[u32], _pt: &Point, ch: usize, out: &mut Vec<u32>) {
        assert_eq!(ch, self.lane, "the composition AIR runs in per-lane mode");
        let mut row = cur.to_vec();
        self.walk(&mut row, Some(out));
    }
    fn num_bus(&self) -> usize {
        2 + self.leaf_chunks().iter().sum::<usize>()
    }
    fn bus(&self, cur: &[u32], c: &Challenges, ch: usize, out: &mut Vec<BusTerm>) {
        let mut t = Vec::with_capacity(2);
        self.bus_tuples(cur, ch, &mut t);
        crate::stark::bus_from_tuples(&t, c, ch, out);
    }
    fn bus_tuples(&self, cur: &[u32], ch: usize, out: &mut Vec<BusTuple>) {
        let neg = sub_mod(0, cur[self.lay.act], RNS_MODULI[ch]);
        out.push(BusTuple { tag: TAG, values: self.row_tuple(cur), weight: neg });
        out.push(BusTuple { tag: crate::fri_air::LINK_LAYER0, values: self.layer0_tuple(cur), weight: neg });
        // leaf chunks: (leaf id, chunk index, 8 words), sent to the leaf hash AIR
        let l = &self.lay;
        let m = RNS_MODULI[ch];
        let w = if self.link_leaves { neg } else { 0 };
        let row_id = add_mod(add_mod(cur[l.qs], cur[l.qs], m), cur[l.qs + 1], m);
        for (kind, vals) in self.leaf_values(cur).iter().enumerate() {
            let lid = add_mod(mul_mod_channel(row_id, LEAVES_PER_ROW as u32, ch), kind as u32, m);
            for (k, chunk) in vals.chunks(8).enumerate() {
                out.push(BusTuple { tag: crate::leaf_air::TAG_CHUNK, values: crate::leaf_air::chunk_tuple(lid, k as u32, chunk), weight: w });
            }
        }
    }
    fn bus_sum(&self, c: &Challenges, ch: usize) -> Extension4 {
        let mut dens: Vec<Extension4> = self.claims.iter().map(|cl| c.fingerprint(TAG, &self.public_tuple(cl), ch)).collect();
        if !self.link_fri {
            dens.extend(self.claims.iter().map(|cl| c.fingerprint(crate::fri_air::LINK_LAYER0, &self.public_layer0(cl), ch)));
        }
        match crate::logup::batch_inverse_ext4(&dens, ch) {
            Some(inv) => inv.iter().fold(Extension4::ZERO, |a, x| a.sub(x, ch)),
            None => Extension4::ONE,
        }
    }
}

/// Builds the claim and the witness of lane `j` from an inner per-lane proof and its view.
pub fn from_proof<'a, A: Air>(inner: &'a A, proof: &crate::stark::StarkProof, view: &crate::stark::StarkView, params: StarkParams) -> (CompositionAir<'a, A>, Vec<OpenedRow>) {
    let j = (0..DEFAULT_RNS_CHANNELS).find(|&ch| !proof.openings[0][0].main[ch].is_empty()).expect("per-lane proof");
    let n = 1usize << (params.log_rows + params.log_blowup);
    let mut claims = Vec::new();
    let mut opened = Vec::new();
    for (q, (&i, opens)) in view.indices.iter().zip(&proof.openings).enumerate() {
        for slot in 0..2 {
            let pos = if slot == 0 { i } else { i + n / 2 };
            let (here, next) = (&opens[slot], &opens[slot + 2]);
            claims.push(OpeningClaim { q, slot, pos, f: proof.fri.queries[q][0].pair[j][slot] });
            opened.push(OpenedRow {
                main: here.main[j].clone(),
                main_next: next.main[j].clone(),
                aux: here.aux[j].clone(),
                aux_next: next.aux[j].clone(),
                quotient: here.quotient[j],
                quotient_next: next.quotient[j],
            });
        }
    }
    let air = CompositionAir::new(inner, j, params, view.chals[j], view.gammas[j], view.deltas[j], view.s_over_n[j], claims);
    (air, opened)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::HashMode;
    use crate::stark::{prove_air, prove_air_lanes, verify_air, verify_air_view, MulModAir};
    use crate::transcript::Transcript;

    const INNER: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 8 };
    const OUTER: StarkParams = StarkParams { log_rows: 8, log_blowup: 2, num_queries: 16 };

    fn check<A: Air>(air: &CompositionAir<A>, opened: &[OpenedRow]) -> bool {
        let traces = air.traces(opened, OUTER.log_rows);
        let t = || Transcript::with_mode(b"composition", HashMode::Lane(air.lane as u8));
        let proof = prove_air(air, &traces, air.claims.len(), &OUTER, &mut t());
        verify_air(air, &proof, 1 << OUTER.log_rows, &OUTER, &mut t())
    }

    fn row_holds<A: Air>(air: &CompositionAir<A>, opened: &[OpenedRow]) -> bool {
        let traces = air.traces(opened, OUTER.log_rows);
        let mut out = Vec::new();
        for r in &traces[air.lane][..opened.len()] {
            air.eval(r, r, &Point { first_row: 0, not_last: 1 }, air.lane, &mut out);
        }
        out.iter().all(|&v| v == 0)
    }

    fn state_case() -> (crate::state::StateStatement, [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS]) {
        use crate::state::{build, AccountState, Transfer};
        let addrs: Vec<[u8; 20]> = (0..40u8).map(|i| [i; 20]).collect();
        let old: Vec<AccountState> = (0..40).map(|i| AccountState { balance: 1_000_000 + i as u64, nonce: 0 }).collect();
        let mut nonces = vec![0u32; 40];
        let txs: Vec<Transfer> = (0..120u32)
            .map(|k| {
                let from = (k * 7) % 40;
                let tx = Transfer { from, to: (k * 13 + 1) % 40, amount: 100 + k as u64, nonce: nonces[from as usize] };
                nonces[from as usize] += 1;
                tx
            })
            .collect();
        build(&addrs, &old, &txs, INNER.log_rows, true).unwrap()
    }

    #[test]
    fn state_air_composition_verifies_in_every_lane() {
        let (st, traces) = state_case();
        let inner = crate::state::StateAir { st: &st };
        let proofs = prove_air_lanes(&inner, &traces, st.num_txs(), &INNER, b"inner");
        for j in 0..DEFAULT_RNS_CHANNELS {
            let view = verify_air_view(&inner, &proofs[j], 5 << INNER.log_rows, &INNER, &mut Transcript::with_mode(b"inner", HashMode::Lane(j as u8))).unwrap();
            let (air, opened) = from_proof(&inner, &proofs[j], &view, INNER);
            assert!(row_holds(&air, &opened), "lane {j}: honest openings violate a constraint");
            let t0 = std::time::Instant::now();
            assert!(check(&air, &opened), "lane {j}");
            if j == 0 {
                eprintln!("composition AIR (state): width {}, {} constraints, prove+verify {:?}", air.width(), air.num_constraints(), t0.elapsed());
            }
        }
    }

    #[test]
    fn forged_openings_and_claims_are_rejected() {
        let (st, traces) = state_case();
        let inner = crate::state::StateAir { st: &st };
        let j = 4;
        let t = || Transcript::with_mode(b"inner", HashMode::Lane(j as u8));
        let proof = prove_air(&inner, &traces, st.num_txs(), &INNER, &mut t());
        let view = verify_air_view(&inner, &proof, 5 << INNER.log_rows, &INNER, &mut t()).unwrap();
        let (air, opened) = from_proof(&inner, &proof, &view, INNER);
        assert!(check(&air, &opened));

        // An opened main value that breaks a state constraint (e.g. a balance byte).
        let mut bad = opened.clone();
        bad[5].main[20] = add_mod(bad[5].main[20], 1, RNS_MODULI[j]);
        assert!(!row_holds(&air, &bad));
        assert!(!check(&air, &bad), "forged main value");

        // A quotient value that does not match the composition.
        let mut bad = opened.clone();
        bad[3].quotient = bad[3].quotient.add(&Extension4::ONE, j);
        assert!(!check(&air, &bad), "forged quotient");

        // A running-sum value of the next row.
        let mut bad = opened.clone();
        let h = bad[0].aux_next.last_mut().unwrap();
        *h = h.add(&Extension4::ONE, j);
        assert!(!check(&air, &bad), "forged running sum");

        // Wrong public claims with the honest witness.
        let mut claims = air.claims.clone();
        claims[2].f = claims[2].f.add(&Extension4::ONE, j);
        let wrong = CompositionAir::new(&inner, j, INNER, air.chals, air.gamma, air.delta, air.s_over_n, claims);
        assert!(!check(&wrong, &opened), "wrong FRI value");
        let mut c2 = air.chals;
        c2.alpha = c2.alpha.add(&Extension4::ONE, j);
        let wrong = CompositionAir::new(&inner, j, INNER, c2, air.gamma, air.delta, air.s_over_n, air.claims.clone());
        assert!(!check(&wrong, &opened), "wrong alpha");
        let wrong = CompositionAir::new(&inner, j, INNER, air.chals, air.gamma, air.delta, air.s_over_n.add(&Extension4::ONE, j), air.claims.clone());
        assert!(!check(&wrong, &opened), "wrong public bus sum");
        let mut claims = air.claims.clone();
        claims[1].pos ^= 1;
        let wrong = CompositionAir::new(&inner, j, INNER, air.chals, air.gamma, air.delta, air.s_over_n, claims);
        assert!(!check(&wrong, &opened), "wrong position");
    }

    #[test]
    fn works_for_an_air_without_buses() {
        // MULMOD (bytes only, no bus) as the inner AIR.
        let p = crate::uint256::Modulus256::secp256k1();
        let pad = crate::uint256::MulModRow::generate(&3u32.into(), &5u32.into(), &p);
        let trace: Vec<Vec<u32>> = vec![pad.limbs(); 1 << INNER.log_rows];
        let traces: [Vec<Vec<u32>>; DEFAULT_RNS_CHANNELS] = std::array::from_fn(|_| trace.clone());
        let inner = MulModAir { p: &p };
        let j = 0;
        let t = || Transcript::with_mode(b"inner", HashMode::Lane(j as u8));
        let proof = prove_air(&inner, &traces, 256, &INNER, &mut t());
        let view = verify_air_view(&inner, &proof, 5 << INNER.log_rows, &INNER, &mut t()).unwrap();
        let (air, opened) = from_proof(&inner, &proof, &view, INNER);
        assert!(check(&air, &opened));
    }
}
