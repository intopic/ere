//! cargo run --release -p ss_rap_settlement --example wrapper_cost
//!
//! Measures the wrapper gadgets and projects the size of a BN254 circuit that verifies the
//! state-transition STARK directly, for a few parameter choices.

use ss_rap_settlement::wrapper::cost::{measure, project, state_shape};

fn main() {
    if let Some(n) = std::env::args().nth(1).and_then(|s| s.parse().ok()) {
        groth16_speed(n);
        return;
    }
    let g = measure();
    println!("gadgets (R1CS constraints): 31-bit value {} | F_m^4 mul+reduce {} | F_m^4 lazy mul {} | Poseidon 2->1 {}", g.value, g.ext_mul, g.ext_mul_lazy, g.hash2);
    println!("{:<44} {:>14} {:>14} {:>9}", "STARK verifier in Groth16 (1000-tx state proof)", "per query", "total", "hashing");
    for (q, lb, pack, lazy, note) in [
        (50, 2, 1, false, "today: 50 queries, blowup 4"),
        (50, 2, 7, false, "+ 7 values packed per hash input"),
        (50, 2, 7, true, "+ lazy algebra (one reduction per sum)"),
        (25, 4, 7, true, "+ blowup 16, 25 queries (~100 bits)"),
        (16, 6, 7, true, "+ blowup 64, 16 queries (~96 bits)"),
    ] {
        let p = project(&state_shape(q, lb, pack, lazy), &g);
        println!("{:<44} {:>14} {:>14} {:>8.0}%", note, p.per_query, p.total, 100.0 * p.hashing_share);
    }
}

/// Groth16 proving speed on this machine for a circuit of `n` multiplication constraints
/// (run with an argument: `wrapper_cost 262144`).
#[allow(dead_code)]
fn groth16_speed(n: usize) {
    use ark_bn254::{Bn254, Fr};
    use ark_groth16::Groth16;
    use ark_relations::lc;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    use ark_snark::SNARK;
    use rand_chacha::rand_core::SeedableRng;
    #[derive(Clone)]
    struct Chain(usize);
    impl ConstraintSynthesizer<Fr> for Chain {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
            let mut x = Fr::from(3u64);
            let mut v = cs.new_witness_variable(|| Ok(x))?;
            for _ in 0..self.0 {
                let y = x * x + Fr::from(1u64);
                let w = cs.new_witness_variable(|| Ok(y))?;
                cs.enforce_constraint(lc!() + v, lc!() + v, lc!() + w - (Fr::from(1u64), ark_relations::r1cs::Variable::One))?;
                x = y;
                v = w;
            }
            let out = cs.new_input_variable(|| Ok(x))?;
            cs.enforce_constraint(lc!() + v, lc!() + ark_relations::r1cs::Variable::One, lc!() + out)?;
            Ok(())
        }
    }
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(1);
    let t = std::time::Instant::now();
    let (pk, _vk) = Groth16::<Bn254>::circuit_specific_setup(Chain(n), &mut rng).unwrap();
    let setup = t.elapsed();
    let t = std::time::Instant::now();
    Groth16::<Bn254>::prove(&pk, Chain(n), &mut rng).unwrap();
    let prove = t.elapsed();
    println!("Groth16 on this machine, {n} constraints: setup {:.1} s, prove {:.1} s ({:.2} us/constraint, {} threads)",
        setup.as_secs_f64(), prove.as_secs_f64(), prove.as_secs_f64() * 1e6 / n as f64, std::thread::available_parallelism().map(|x| x.get()).unwrap_or(1));
}
