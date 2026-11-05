//! R8.4b: Keccak-256 (the original Keccak padding, as Solidity's `keccak256`) over bits.
//!
//! The settlement contract computes the public input as keccak256 of the batch header; doing the
//! same in the circuit keeps the contract and its single public input unchanged. Cost: about
//! 150k constraints per Keccak-f[1600] (theta and chi are one constraint per XOR / AND).

use ark_bn254::Fr;
use ark_r1cs_std::boolean::Boolean;
use ark_relations::r1cs::SynthesisError;

type R<T> = Result<T, SynthesisError>;

const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

const ROT: [[u32; 5]; 5] = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]];

type Lane = Vec<Boolean<Fr>>; // 64 bits, LSB first

fn xor(a: &Lane, b: &Lane) -> R<Lane> {
    Ok(a.iter().zip(b).map(|(x, y)| x ^ y).collect())
}

fn rotl(a: &Lane, r: u32) -> Lane {
    let r = r as usize % 64;
    (0..64).map(|i| a[(i + 64 - r) % 64].clone()).collect()
}

/// Keccak-f[1600] on state[x][y].
fn keccak_f(s: &mut [[Lane; 5]; 5]) -> R<()> {
    for rc in RC {
        // theta
        let mut c: Vec<Lane> = Vec::with_capacity(5);
        for x in 0..5 {
            let mut v = s[x][0].clone();
            for y in 1..5 {
                v = xor(&v, &s[x][y])?;
            }
            c.push(v);
        }
        for x in 0..5 {
            let d = xor(&c[(x + 4) % 5], &rotl(&c[(x + 1) % 5], 1))?;
            for y in 0..5 {
                s[x][y] = xor(&s[x][y], &d)?;
            }
        }
        // rho and pi
        let mut b: [[Lane; 5]; 5] = std::array::from_fn(|_| std::array::from_fn(|_| Vec::new()));
        for x in 0..5 {
            for y in 0..5 {
                b[y][(2 * x + 3 * y) % 5] = rotl(&s[x][y], ROT[x][y]);
            }
        }
        // chi
        for x in 0..5 {
            for y in 0..5 {
                let t: Lane = b[(x + 1) % 5][y].iter().zip(&b[(x + 2) % 5][y]).map(|(p, q)| !p & q).collect();
                s[x][y] = xor(&b[x][y], &t)?;
            }
        }
        // iota (constant bits: NOT where the round constant has a 1)
        s[0][0] = s[0][0].iter().enumerate().map(|(i, v)| if (rc >> i) & 1 == 1 { !v.clone() } else { v.clone() }).collect();
    }
    Ok(())
}

/// keccak256 of a byte string given as bits (8 per byte, LSB first within each byte).
pub fn keccak256(bits: &[Boolean<Fr>]) -> R<Vec<Boolean<Fr>>> {
    assert_eq!(bits.len() % 8, 0);
    let rate = 136 * 8;
    let mut msg = bits.to_vec();
    // pad10*1 with the Keccak domain bit: byte 0x01 first, 0x80 last
    msg.push(Boolean::TRUE);
    while (msg.len() + 1) % rate != 0 {
        msg.push(Boolean::FALSE);
    }
    msg.push(Boolean::TRUE);
    let mut s: [[Lane; 5]; 5] = std::array::from_fn(|_| std::array::from_fn(|_| vec![Boolean::FALSE; 64]));
    for block in msg.chunks(rate) {
        for (k, lane_bits) in block.chunks(64).enumerate() {
            let (x, y) = (k % 5, k / 5);
            s[x][y] = xor(&s[x][y], &lane_bits.to_vec())?;
        }
        keccak_f(&mut s)?;
    }
    let mut out = Vec::with_capacity(256);
    for k in 0..4 {
        out.extend(s[k % 5][k / 5].iter().cloned());
    }
    Ok(out)
}

/// Bits of bytes (LSB first per byte).
pub fn byte_bits(bytes: &[u8]) -> Vec<bool> {
    bytes.iter().flat_map(|b| (0..8).map(move |i| (b >> i) & 1 == 1)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;

    fn check(data: &[u8]) -> usize {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let bits: Vec<Boolean<Fr>> = byte_bits(data).into_iter().map(|b| Boolean::new_witness(cs.clone(), || Ok(b)).unwrap()).collect();
        let out = keccak256(&bits).unwrap();
        let got: Vec<u8> = out.chunks(8).map(|c| c.iter().enumerate().fold(0u8, |a, (i, b)| a | ((b.value().unwrap() as u8) << i))).collect();
        assert_eq!(got, crate::public_input::keccak256(data).to_vec(), "len {}", data.len());
        assert!(cs.is_satisfied().unwrap());
        cs.num_constraints()
    }

    #[test]
    fn matches_keccak256() {
        check(b"");
        check(b"abc");
        let n = check(&(0..192u32).map(|i| (i * 37 + 5) as u8).collect::<Vec<_>>());
        check(&[7u8; 135]);
        check(&[9u8; 136]);
        eprintln!("keccak256 of a 192-byte header: {n} constraints");
    }
}
