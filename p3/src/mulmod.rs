//! EVM uint256 MULMOD (r = a*b mod P) on Plonky3: the same AIR as `ss_rap_v2::uint256`
//! (byte limbs, carries, "verify, don't compute"), every byte range-checked with LogUp
//! against a preprocessed byte table.
use p3_air::{Air, AirBuilder, BaseAir, PermutationAirBuilder, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;
use ss_rap_v2::uint256::{Modulus256, MulModRow, BYTES, CARRY_BYTES, CARRY_OFFSET_BITS, NUM_COLUMNS, PRODUCT_COLUMNS};

const COL_A: usize = 0;
const COL_B: usize = BYTES;
const COL_Q: usize = 2 * BYTES;
const COL_R: usize = 3 * BYTES;
const COL_S: usize = 4 * BYTES;
const COL_C: usize = 5 * BYTES;
const COL_D: usize = COL_C + (PRODUCT_COLUMNS - 1) * CARRY_BYTES;
/// Byte columns per LogUp group (each group has its own multiplicity column: p3-lookup's cost
/// grows faster than linearly in the tuples of one interaction, see docs/PLONKY3.md).
pub const GROUP: usize = 8;
pub const GROUPS: usize = NUM_COLUMNS.div_ceil(GROUP);
/// Byte columns, then one multiplicity column per group.
pub const WIDTH: usize = NUM_COLUMNS + GROUPS;

#[derive(Clone, Debug)]
pub struct MulModAir {
    pub p: [u8; 32],
    pub log_rows: usize,
}

impl MulModAir {
    pub fn new(p: &Modulus256, log_rows: usize) -> Self {
        assert!(log_rows >= 8, "the byte table needs 256 rows");
        Self { p: p.bytes, log_rows }
    }

    pub fn trace<F: Field>(&self, rows: &[MulModRow]) -> RowMajorMatrix<F> {
        let n = 1usize << self.log_rows;
        assert!(rows.len() <= n);
        let pad = MulModRow::generate(&0u32.into(), &0u32.into(), &Modulus256 { value: num_bigint::BigUint::from_bytes_le(&self.p), bytes: self.p });
        let mut mult = vec![[0u64; 256]; GROUPS];
        let mut v = F::zero_vec(n * WIDTH);
        for i in 0..n {
            let row = rows.get(i).unwrap_or(&pad);
            for (j, &b) in row.limbs().iter().enumerate() {
                v[i * WIDTH + j] = F::from_u32(b);
                mult[j / GROUP][b as usize] += 1;
            }
        }
        for (g, m) in mult.iter().enumerate() {
            for (b, &m) in m.iter().enumerate() {
                v[b * WIDTH + NUM_COLUMNS + g] = F::from_u64(m);
            }
        }
        RowMajorMatrix::new(v, WIDTH)
    }
}

impl<F: Field> BaseAir<F> for MulModAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let n = 1usize << self.log_rows;
        Some(RowMajorMatrix::new((0..n).map(|i| F::from_u32((i % 256) as u32)).collect(), 1))
    }
    fn preprocessed_width(&self) -> usize {
        1
    }
}

impl<AB> Air<AB> for MulModAir
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let c: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let byte = builder.preprocessed().current(0).unwrap().into();
        let k256 = AB::Expr::from_u32(256);
        let offset = AB::Expr::from_u32(1 << CARRY_OFFSET_BITS);
        let carry = |k: usize| c[COL_C + CARRY_BYTES * k].clone() + c[COL_C + CARRY_BYTES * k + 1].clone() * k256.clone() - offset.clone();
        for k in 0..PRODUCT_COLUMNS {
            let mut e = AB::Expr::ZERO;
            for i in k.saturating_sub(BYTES - 1)..=k.min(BYTES - 1) {
                e += c[COL_A + i].clone() * c[COL_B + k - i].clone() - c[COL_Q + i].clone() * AB::Expr::from_u32(self.p[k - i] as u32);
            }
            if k > 0 {
                e += carry(k - 1);
            }
            if k < BYTES {
                e -= c[COL_R + k].clone();
            }
            if k < PRODUCT_COLUMNS - 1 {
                e -= carry(k) * k256.clone();
            }
            builder.assert_zero(e);
        }
        for k in 0..BYTES {
            let mut e = c[COL_S + k].clone() + c[COL_R + k].clone() - AB::Expr::from_u32(self.p[k] as u32);
            e += if k == 0 { AB::Expr::ONE } else { c[COL_D + k - 1].clone() };
            if k < BYTES - 1 {
                e -= c[COL_D + k].clone() * k256.clone();
            }
            builder.assert_zero(e);
        }
        // LogUp: every byte column is in [0, 256); the table side is the preprocessed byte
        // column (first 256 rows hold 0..255, the rest repeat it) with its multiplicity.
        if std::env::var("GLOBAL").is_ok() {
            for j in 0..NUM_COLUMNS {
                builder.push_interaction("byte", [c[j].clone()], 1);
            }
        } else if std::env::var("NO_LOOKUP").is_err() {
            for g in 0..GROUPS {
                let mut tuples: Vec<(Vec<AB::Expr>, Count<AB::Expr>)> =
                    (g * GROUP..((g + 1) * GROUP).min(NUM_COLUMNS)).map(|j| (vec![c[j].clone()], Count::bounded(AB::Expr::ONE, 1))).collect();
                tuples.push((vec![byte.clone()], Count::provided(-c[NUM_COLUMNS + g].clone())));
                builder.push_local_interaction(tuples);
            }
        }
    }
}

/// The byte table for the global "byte" bus: preprocessed 0..255 and its multiplicity.
#[derive(Clone, Debug)]
pub struct ByteTableAir;

impl ByteTableAir {
    pub fn trace<F: Field>(rows: &[MulModRow], n_rows: usize, pad: &MulModRow) -> RowMajorMatrix<F> {
        let mut m = vec![0u64; 256];
        for i in 0..n_rows {
            for b in rows.get(i).unwrap_or(pad).limbs() {
                m[b as usize] += 1;
            }
        }
        RowMajorMatrix::new(m.into_iter().map(F::from_u64).collect(), 1)
    }
}

impl<F: Field> BaseAir<F> for ByteTableAir {
    fn width(&self) -> usize {
        1
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(RowMajorMatrix::new((0..256u32).map(F::from_u32).collect(), 1))
    }
    fn preprocessed_width(&self) -> usize {
        1
    }
}

impl<AB> Air<AB> for ByteTableAir
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let m: AB::Expr = builder.main().current_slice()[0].into();
        let t: AB::Expr = builder.preprocessed().current(0).unwrap().into();
        builder.push_interaction("byte", [t], Count::provided(-m));
    }
}

/// Either AIR, so both go into one batch proof.
#[derive(Clone, Debug)]
pub enum MulModAirs {
    MulMod(MulModAir),
    Table(ByteTableAir),
}

impl<F: Field> BaseAir<F> for MulModAirs {
    fn width(&self) -> usize {
        match self {
            Self::MulMod(a) => <MulModAir as BaseAir<F>>::width(a),
            Self::Table(a) => <ByteTableAir as BaseAir<F>>::width(a),
        }
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::MulMod(a) => a.preprocessed_trace(),
            Self::Table(a) => a.preprocessed_trace(),
        }
    }
    fn preprocessed_width(&self) -> usize {
        1
    }
}

impl<AB> Air<AB> for MulModAirs
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::MulMod(a) => a.eval(builder),
            Self::Table(a) => a.eval(builder),
        }
    }
}
