//! EIP-4844 blobs: how a batch's transactions are packed into blobs, and the blob hash the
//! public input binds: the versioned hash (0x01 || sha256(KZG commitment)[1..]) that
//! `blobhash(0)` returns on L1 when the batch fits in one blob, else keccak256 of the versioned
//! hashes of all its blobs in order (`blobhash(0)`, `blobhash(1)`, ...), so one proof covers
//! every blob of the transaction.
//!
//! Packing: a 4-byte big-endian length, then the data, 31 bytes per 32-byte field element
//! (the first byte of each element is 0, so every element is below the BLS12-381 modulus).
//! A batch larger than one blob is cut into MAX_DATA-byte pieces, one blob each.

use sha2::{Digest, Sha256};

pub const BYTES_PER_BLOB: usize = 4096 * 32;
/// Data bytes one blob holds (after the 4-byte length).
pub const MAX_DATA: usize = 4096 * 31 - 4;

/// Most blobs one transaction may carry (the EIP-4844 / EIP-7594 per-transaction limit).
pub const MAX_BLOBS: usize = 6;

/// The blobs holding `data` (MAX_DATA bytes each, the last one shorter), or None if it needs
/// more than MAX_BLOBS.
pub fn to_blobs(data: &[u8]) -> Option<Vec<Vec<u8>>> {
    if data.is_empty() {
        return Some(vec![to_blob(data)?]);
    }
    if data.len().div_ceil(MAX_DATA) > MAX_BLOBS {
        return None;
    }
    data.chunks(MAX_DATA).map(to_blob).collect()
}

/// The data of blobs made by `to_blobs`, in order.
pub fn from_blobs(blobs: &[Vec<u8>]) -> Option<Vec<u8>> {
    let mut data = Vec::new();
    for b in blobs {
        data.extend(from_blob(b)?);
    }
    Some(data)
}

/// The blob hash the public input binds: the single versioned hash, or keccak256 of all of them.
pub fn blobs_hash(versioned: &[[u8; 32]]) -> [u8; 32] {
    if versioned.len() == 1 {
        return versioned[0];
    }
    use tiny_keccak::{Hasher, Keccak};
    let mut k = Keccak::v256();
    for h in versioned {
        k.update(h);
    }
    let mut out = [0u8; 32];
    k.finalize(&mut out);
    out
}

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
    fn large_batches_take_several_blobs() {
        let data: Vec<u8> = (0..MAX_DATA * 4 + 123).map(|i| (i * 13 + 1) as u8).collect();
        let blobs = to_blobs(&data).unwrap();
        assert_eq!(blobs.len(), 5);
        assert_eq!(from_blobs(&blobs).unwrap(), data);
        assert_eq!(to_blobs(&data[..MAX_DATA]).unwrap().len(), 1);
        assert!(to_blobs(&vec![1; MAX_DATA * MAX_BLOBS + 1]).is_none());
        // one blob: its versioned hash itself; several: keccak256 of their concatenation
        let (a, b) = ([1u8; 32], [2u8; 32]);
        assert_eq!(blobs_hash(&[a]), a);
        let mut cat = a.to_vec();
        cat.extend(b);
        use tiny_keccak::{Hasher, Keccak};
        let mut k = Keccak::v256();
        k.update(&cat);
        let mut want = [0u8; 32];
        k.finalize(&mut want);
        assert_eq!(blobs_hash(&[a, b]), want);
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
