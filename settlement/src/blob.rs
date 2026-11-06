//! EIP-4844 blobs: how a batch's transactions are packed into one blob, and the blob's
//! versioned hash (0x01 || sha256(KZG commitment)[1..]), the value `blobhash(0)` returns on L1
//! and the public input binds.
//!
//! Packing: a 4-byte big-endian length, then the data, 31 bytes per 32-byte field element
//! (the first byte of each element is 0, so every element is below the BLS12-381 modulus).

use sha2::{Digest, Sha256};

pub const BYTES_PER_BLOB: usize = 4096 * 32;
/// Data bytes one blob holds (after the 4-byte length).
pub const MAX_DATA: usize = 4096 * 31 - 4;

/// The blob holding `data`, or None if it does not fit.
pub fn to_blob(data: &[u8]) -> Option<Vec<u8>> {
    if data.len() > MAX_DATA {
        return None;
    }
    let mut payload = (data.len() as u32).to_be_bytes().to_vec();
    payload.extend_from_slice(data);
    let mut blob = vec![0u8; BYTES_PER_BLOB];
    for (i, chunk) in payload.chunks(31).enumerate() {
        blob[i * 32 + 1..i * 32 + 1 + chunk.len()].copy_from_slice(chunk);
    }
    Some(blob)
}

/// The data of a blob made by `to_blob`, or None if it is not one.
pub fn from_blob(blob: &[u8]) -> Option<Vec<u8>> {
    if blob.len() != BYTES_PER_BLOB || blob.chunks(32).any(|e| e[0] != 0) {
        return None;
    }
    let payload: Vec<u8> = blob.chunks(32).flat_map(|e| e[1..].iter().copied()).collect();
    let n = u32::from_be_bytes(payload[..4].try_into().unwrap()) as usize;
    if n > MAX_DATA || payload[4 + n..].iter().any(|&b| b != 0) {
        return None;
    }
    Some(payload[4..4 + n].to_vec())
}

/// The KZG commitment of a blob (Ethereum's trusted setup).
pub fn commitment(blob: &[u8]) -> [u8; 48] {
    let b = c_kzg::Blob::from_bytes(blob).expect("blob size");
    let c = c_kzg::ethereum_kzg_settings(0).blob_to_kzg_commitment(&b).expect("valid blob");
    let bytes: &[u8] = c.as_ref();
    bytes.try_into().unwrap()
}

/// 0x01 || sha256(KZG commitment)[1..].
pub fn versioned_hash(blob: &[u8]) -> [u8; 32] {
    let mut h: [u8; 32] = Sha256::digest(commitment(blob)).into();
    h[0] = 0x01;
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn packing_round_trips() {
        for n in [0usize, 1, 30, 31, 32, 1000, MAX_DATA] {
            let data: Vec<u8> = (0..n).map(|i| (i * 7 + 3) as u8).collect();
            let blob = to_blob(&data).unwrap();
            assert_eq!(blob.len(), BYTES_PER_BLOB);
            assert_eq!(from_blob(&blob).unwrap(), data);
        }
        assert!(to_blob(&vec![0; MAX_DATA + 1]).is_none());
    }

    #[test]
    fn versioned_hash_of_the_empty_blob() {
        // KZG commitment of the zero blob is the point at infinity (0xc0, 47 zero bytes)
        let blob = vec![0u8; BYTES_PER_BLOB];
        let mut inf = [0u8; 48];
        inf[0] = 0xc0;
        assert_eq!(commitment(&blob), inf);
        let h = versioned_hash(&blob);
        assert_eq!(h[0], 1);
        let want: [u8; 32] = Sha256::digest(inf).into();
        assert_eq!(h[1..], want[1..]);
    }
}
