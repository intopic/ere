//! Poseidon2 over BabyBear, width 24, as AIR constraints: one permutation per row, inputs given
//! as expressions over the row (so the caller decides what is hashed), every round's state
//! committed. Same permutation as `p3_baby_bear::default_babybear_poseidon2_24` (8 full rounds,
//! 21 partial, S-box x^7 through one committed x^3), so the constraints have degree 3.
//!
//! Columns: for each full round 24 S-box registers then the 24-element state after the round;
//! for each partial round the S-box register and the S-box output. The permutation's output is
//! the state after the last full round, i.e. the last 24 columns.

use p3_air::AirBuilder;
use p3_baby_bear::{
    BabyBear, GenericPoseidon2LinearLayersBabyBear as Layers, BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS as HALF,
    BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_24 as PARTIAL, BABYBEAR_POSEIDON2_RC_24_EXTERNAL_FINAL as RC_FINAL,
    BABYBEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL as RC_INITIAL, BABYBEAR_POSEIDON2_RC_24_INTERNAL as RC_PARTIAL,
};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_poseidon2::GenericPoseidon2LinearLayers;

/// State width.
pub const T: usize = 24;
const FULL_COLS: usize = 2 * T;
/// Committed columns of one permutation.
pub const COLS: usize = 2 * HALF * FULL_COLS + 2 * PARTIAL;
/// Offset of the output (the last full round's state) inside the permutation's columns.
pub const OUTPUT: usize = COLS - T;

fn c<R: PrimeCharacteristicRing>(x: BabyBear) -> R {
    R::from_u32(x.as_canonical_u32())
}

/// The constraints of one permutation of `input`, with its columns `cols` (COLS of them).
/// Returns the output as expressions (the committed last state).
pub fn eval<AB: AirBuilder>(builder: &mut AB, input: [AB::Expr; T], cols: &[AB::Expr]) -> [AB::Expr; T] {
    assert_eq!(cols.len(), COLS);
    let mut state = input;
    Layers::external_linear_layer(&mut state);
    let mut at = 0;
    let full = |builder: &mut AB, state: &mut [AB::Expr; T], rc: &[BabyBear; T], at: &mut usize| {
        for i in 0..T {
            let x = state[i].clone() + c::<AB::Expr>(rc[i]);
            let x3 = cols[*at + i].clone();
            builder.assert_eq(x3.clone(), x.clone() * x.clone() * x.clone());
            state[i] = x3.clone() * x3 * x;
        }
        Layers::external_linear_layer(state);
        for i in 0..T {
            let post = cols[*at + T + i].clone();
            builder.assert_eq(state[i].clone(), post.clone());
            state[i] = post;
        }
        *at += FULL_COLS;
    };
    for rc in RC_INITIAL.iter() {
        full(builder, &mut state, rc, &mut at);
    }
    for rc in RC_PARTIAL.iter() {
        let x = state[0].clone() + c::<AB::Expr>(*rc);
        let (x3, out) = (cols[at].clone(), cols[at + 1].clone());
        builder.assert_eq(x3.clone(), x.clone() * x.clone() * x.clone());
        builder.assert_eq(out.clone(), x3.clone() * x3 * x);
        state[0] = out;
        Layers::internal_linear_layer(&mut state);
        at += 2;
    }
    for rc in RC_FINAL.iter() {
        full(builder, &mut state, rc, &mut at);
    }
    debug_assert_eq!(at, COLS);
    state
}

/// The columns of one permutation of `input` (written to `out`, COLS of them); returns the output.
pub fn generate<F: Field + PrimeField32>(input: [F; T], out: &mut [F]) -> [F; T] {
    assert_eq!(out.len(), COLS);
    let mut state = input;
    Layers::external_linear_layer(&mut state);
    let mut at = 0;
    let full = |state: &mut [F; T], rc: &[BabyBear; T], out: &mut [F], at: &mut usize| {
        for i in 0..T {
            let x = state[i] + c::<F>(rc[i]);
            let x3 = x * x * x;
            out[*at + i] = x3;
            state[i] = x3 * x3 * x;
        }
        Layers::external_linear_layer(state);
        out[*at + T..*at + 2 * T].copy_from_slice(state);
        *at += FULL_COLS;
    };
    for rc in RC_INITIAL.iter() {
        full(&mut state, rc, out, &mut at);
    }
    for rc in RC_PARTIAL.iter() {
        let x = state[0] + c::<F>(*rc);
        let x3 = x * x * x;
        state[0] = x3 * x3 * x;
        out[at] = x3;
        out[at + 1] = state[0];
        Layers::internal_linear_layer(&mut state);
        at += 2;
    }
    for rc in RC_FINAL.iter() {
        full(&mut state, rc, out, &mut at);
    }
    state
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_symmetric::Permutation;

    #[test]
    fn matches_the_native_permutation() {
        let perm = p3_baby_bear::default_babybear_poseidon2_24();
        for seed in 0..4u32 {
            let input: [BabyBear; T] = core::array::from_fn(|i| BabyBear::from_u32(seed * 1_000_003 + i as u32 * 7919));
            let mut cols = vec![BabyBear::ZERO; COLS];
            let out = generate(input, &mut cols);
            assert_eq!(out, perm.permute(input));
            assert_eq!(&cols[OUTPUT..], &out[..]);
        }
    }
}
