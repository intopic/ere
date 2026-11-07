//! The public input of a batch, bit-for-bit identical to `SSRapSettlementVerifierV2`:
//!
//! ```solidity
//! uint256(keccak256(abi.encodePacked(oldStateRoot, newStateRoot, vUmtMerkleRoot,
//!                                    blobsHash(), batchNumber, block.chainid,
//!                                    uint256(uint160(address(this)))))) % R_MOD
//! ```
//!
//! The settlement contract's own address is part of the statement (audit SET-06): a proof made
//! for one deployment does not verify on another one, even on the same chain with the same key,
//! state and batch counter (testnet and mainnet, or an old and a new version). The same
//! `Domain` (chain id + settlement address) separates the users' transaction signatures.

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
    /// Address of the settlement contract the batch is for (`address(this)` on L1).
    pub settlement: [u8; 20],
}

/// Where a batch settles: the chain and the settlement contract. Binds both the batch public
/// input and the transaction signatures to one deployment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Domain {
    pub chain_id: u64,
    pub settlement: [u8; 20],
}

/// Sender of every forge test (forge-std's default test contract address).
pub const FORGE_TEST_CONTRACT: [u8; 20] = hex20("7fa9385be102ac3eac297483dd6233d62b3e1496");

/// The settlement contract in the forge tests: the second contract the test contract creates
/// (`setUp` deploys the Groth16 verifier, then the settlement contract), CREATE nonce 2.
pub const FORGE_SETTLEMENT: [u8; 20] = hex20("2e234dae75c793f67a35089c9d99245e1c58470b");

impl Domain {
    /// Local chain (anvil / forge, chain id 31337) and the forge tests' settlement address:
    /// what the fixtures and the unit tests use.
    pub const DEV: Domain = Domain { chain_id: 31337, settlement: FORGE_SETTLEMENT };
}

const fn hex20(s: &str) -> [u8; 20] {
    let b = s.as_bytes();
    let mut out = [0u8; 20];
    let mut i = 0;
    while i < 20 {
        out[i] = (nib(b[2 * i]) << 4) | nib(b[2 * i + 1]);
        i += 1;
    }
    out
}

const fn nib(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        _ => panic!("lowercase hex"),
    }
}

/// The address a CREATE from `sender` with account nonce `nonce` deploys to:
/// keccak256(rlp([sender, nonce]))[12..].
pub fn create_address(sender: &[u8; 20], nonce: u64) -> [u8; 20] {
    let mut rlp = vec![0x94];
    rlp.extend_from_slice(sender);
    match nonce {
        0 => rlp.push(0x80),
        1..=0x7f => rlp.push(nonce as u8),
        _ => {
            let be = nonce.to_be_bytes();
            let n = be.iter().position(|&x| x != 0).unwrap();
            rlp.push(0x80 + (8 - n) as u8);
            rlp.extend_from_slice(&be[n..]);
        }
    }
    let mut list = vec![0xc0 + rlp.len() as u8];
    list.extend(rlp);
    keccak256(&list)[12..].try_into().unwrap()
}

/// EIP-55 mixed-case checksum spelling of an address (what solc requires for address literals).
pub fn checksum(a: &[u8; 20]) -> String {
    let lower: String = a.iter().map(|b| format!("{b:02x}")).collect();
    let h = keccak256(lower.as_bytes());
    let mut out = String::from("0x");
    for (i, c) in lower.chars().enumerate() {
        let nibble = (h[i / 2] >> if i % 2 == 0 { 4 } else { 0 }) & 0xf;
        out.push(if c.is_ascii_alphabetic() && nibble >= 8 { c.to_ascii_uppercase() } else { c });
    }
    out
}

/// `0x`-prefixed hex address (either case), as `cast compute-address` prints it.
pub fn parse_address(s: &str) -> Option<[u8; 20]> {
    let h = s.trim().strip_prefix("0x").unwrap_or(s.trim());
    if h.len() != 40 {
        return None;
    }
    let mut out = [0u8; 20];
    for (i, o) in out.iter_mut().enumerate() {
        *o = u8::from_str_radix(&h[2 * i..2 * i + 2], 16).ok()?;
    }
    Some(out)
}

fn u256_be(x: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..].copy_from_slice(&x.to_be_bytes());
    out
}

/// uint256(uint160(address)) as a big-endian 32-byte word.
pub fn address_word(a: &[u8; 20]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[12..].copy_from_slice(a);
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
    /// abi.encodePacked(bytes32 x 4, uint256 x 3): 224 bytes.
    pub fn encode_packed(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(224);
        v.extend_from_slice(&self.old_state_root);
        v.extend_from_slice(&self.new_state_root);
        v.extend_from_slice(&self.v_umt_root);
        v.extend_from_slice(&self.blob_versioned_hash);
        v.extend_from_slice(&u256_be(self.batch_number));
        v.extend_from_slice(&u256_be(self.chain_id));
        v.extend_from_slice(&address_word(&self.settlement));
        v
    }

    /// The header fields the contract supplies itself (chain id and its own address).
    pub fn domain(&self) -> Domain {
        Domain { chain_id: self.chain_id, settlement: self.settlement }
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
            settlement: [0xab; 20],
        };
        let e = h.encode_packed();
        assert_eq!(e.len(), 224);
        assert_eq!(e[159], 7);
        assert_eq!(&e[190..192], &31337u16.to_be_bytes());
        assert_eq!(&e[192..204], &[0u8; 12]);
        assert_eq!(&e[204..], &[0xab; 20]);
        // another settlement contract: another public input
        let other = BatchHeader { settlement: [0xac; 20], ..h.clone() };
        assert_ne!(other.public_input(), h.public_input());
    }

    #[test]
    fn create_addresses() {
        // forge-std: the test contract's first two CREATEs
        assert_eq!(create_address(&FORGE_TEST_CONTRACT, 1), hex20("5615deb798bb3e4dfa0139dfa1b3d433cc23b72f"));
        assert_eq!(create_address(&FORGE_TEST_CONTRACT, 2), FORGE_SETTLEMENT);
        // nonce 0 and a multi-byte nonce (well-known vectors for 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0)
        let s = hex20("6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0");
        assert_eq!(create_address(&s, 0), hex20("cd234a471b72ba2f1ccf0a70fcaba648a5eecd8d"));
        assert_eq!(create_address(&s, 1), hex20("343c43a37d37dff08ae8c4a11544c718abb4fcf8"));
        assert_eq!(parse_address("0x2e234DAe75C793f67A35089C9d99245E1C58470b"), Some(FORGE_SETTLEMENT));
        assert_eq!(checksum(&FORGE_SETTLEMENT), "0x2e234DAe75C793f67A35089C9d99245E1C58470b");
        assert_eq!(checksum(&FORGE_TEST_CONTRACT), "0x7FA9385bE102ac3EAc297483Dd6233D62b3e1496");
    }
}
