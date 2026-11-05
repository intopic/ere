//! The public input of a batch, bit-for-bit identical to `SSRapSettlementVerifierV2`:
//!
//! ```solidity
//! uint256(keccak256(abi.encodePacked(oldStateRoot, newStateRoot, vUmtMerkleRoot,
//!                                    blobhash(0), batchNumber, block.chainid))) % R_MOD
//! ```

use ark_bn254::Fr;
use ark_ff::PrimeField;
use tiny_keccak::{Hasher, Keccak};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchHeader {
    pub old_state_root: [u8; 32],
    pub new_state_root: [u8; 32],
    pub v_umt_root: [u8; 32],
    pub blob_versioned_hash: [u8; 32],
    pub batch_number: u64,
    pub chain_id: u64,
}

fn u256_be(x: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..].copy_from_slice(&x.to_be_bytes());
    out
}

pub fn keccak256(data: &[u8]) -> [u8; 32] {
    let mut k = Keccak::v256();
    k.update(data);
    let mut out = [0u8; 32];
    k.finalize(&mut out);
    out
}

impl BatchHeader {
    /// abi.encodePacked(bytes32 x 4, uint256 x 2): 192 bytes.
    pub fn encode_packed(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(192);
        v.extend_from_slice(&self.old_state_root);
        v.extend_from_slice(&self.new_state_root);
        v.extend_from_slice(&self.v_umt_root);
        v.extend_from_slice(&self.blob_versioned_hash);
        v.extend_from_slice(&u256_be(self.batch_number));
        v.extend_from_slice(&u256_be(self.chain_id));
        v
    }

    /// keccak256(encodePacked) interpreted as a big-endian uint256, reduced mod r (BN254 scalar).
    pub fn public_input(&self) -> Fr {
        Fr::from_be_bytes_mod_order(&keccak256(&self.encode_packed()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keccak_known_vector() {
        // keccak256("") = c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
        assert_eq!(
            keccak256(b"").to_vec(),
            hex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
        );
    }

    fn hex(s: &str) -> Vec<u8> {
        (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
    }

    #[test]
    fn encoding_layout() {
        let h = BatchHeader {
            old_state_root: [1; 32],
            new_state_root: [2; 32],
            v_umt_root: [3; 32],
            blob_versioned_hash: [4; 32],
            batch_number: 7,
            chain_id: 31337,
        };
        let e = h.encode_packed();
        assert_eq!(e.len(), 192);
        assert_eq!(e[159], 7);
        assert_eq!(&e[190..], &31337u16.to_be_bytes());
    }
}
