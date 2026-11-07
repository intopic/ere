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

/// Transaction slots of one blob (audit H-01 (b)): every transaction takes 4 field elements,
/// 124 data bytes (its 118-byte encoding, then 6 zero bytes), so the proof can find transaction
/// g of the batch at slot g; an empty slot is all zero (`ss_rap_p3::tx_bind`).
pub const TXS_PER_BLOB: usize = ss_rap_p3::tx_bind::TXS_PER_BLOB;
const SLOT: usize = ss_rap_p3::tx_bind::SLOT_BYTES;

/// The blobs of a batch's encoded transactions (`Tx::encode`, `TX_BYTES` each) in the slot
/// layout (at least one blob), or None if they need more than MAX_BLOBS.
pub fn tx_blobs(txs: &[Vec<u8>]) -> Option<Vec<Vec<u8>>> {
    let n = txs.len().div_ceil(TXS_PER_BLOB).max(1);
    if n > MAX_BLOBS || txs.iter().any(|t| t.len() != ss_rap_p3::tx_bind::TX_BYTES) {
        return None;
    }
    Some(
        (0..n)
            .map(|j| {
                let mut blob = vec![0u8; BYTES_PER_BLOB];
                for (k, t) in txs.iter().skip(j * TXS_PER_BLOB).take(TXS_PER_BLOB).enumerate() {
                    let mut slot = [0u8; SLOT];
                    slot[..t.len()].copy_from_slice(t);
                    for (e, c) in slot.chunks(31).enumerate() {
                        let at = (4 * k + e) * 32;
                        blob[at + 1..at + 32].copy_from_slice(c);
                    }
                }
                blob
            })
            .collect(),
    )
}

/// The encoded transactions of blobs made by `tx_blobs`, in order, or None if they are not in
/// that layout (a non-zero first byte or padding, or a transaction after an empty slot).
pub fn txs_of_blobs(blobs: &[Vec<u8>]) -> Option<Vec<Vec<u8>>> {
    let mut out = Vec::new();
    let mut ended = false;
    for b in blobs {
        if b.len() != BYTES_PER_BLOB || b.chunks(32).any(|e| e[0] != 0) {
            return None;
        }
        let data: Vec<u8> = b.chunks(32).flat_map(|e| e[1..].iter().copied()).collect();
        for slot in data.chunks(SLOT) {
            if slot.iter().all(|&x| x == 0) {
                ended = true;
                continue;
            }
            if ended || slot[ss_rap_p3::tx_bind::TX_BYTES..].iter().any(|&x| x != 0) {
                return None;
            }
            out.push(slot[..ss_rap_p3::tx_bind::TX_BYTES].to_vec());
        }
    }
    Some(out)
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
    fn transaction_slots_round_trip() {
        let txs: Vec<Vec<u8>> = (0..TXS_PER_BLOB + 5).map(|i| (0..ss_rap_p3::tx_bind::TX_BYTES).map(|k| (i * 7 + k + 1) as u8).collect()).collect();
        let blobs = tx_blobs(&txs).unwrap();
        assert_eq!(blobs.len(), 2);
        assert_eq!(txs_of_blobs(&blobs).unwrap(), txs);
        // the proof's view: transaction g sits in slot g (4 elements of 31 bytes)
        let e = crate::blob_eval::elements(&blobs[1]).unwrap();
        assert_eq!(&ss_rap_p3::tx_bind::slot_bytes(&e, 2)[..ss_rap_p3::tx_bind::TX_BYTES], &txs[TXS_PER_BLOB + 2][..]);
        let tx_arrays: Vec<[u8; ss_rap_p3::tx_bind::TX_BYTES]> = txs.iter().map(|t| t[..].try_into().unwrap()).collect();
        assert_eq!(ss_rap_p3::tx_bind::blob_elements(&tx_arrays)[1], e);
        assert_eq!(tx_blobs(&[]).unwrap().len(), 1);
        assert!(tx_blobs(&vec![txs[0].clone(); TXS_PER_BLOB * MAX_BLOBS + 1]).is_none());
        let mut bad = blobs.clone();
        bad[0][(4 * 2 + 3) * 32 + 31] = 1; // the padding of slot 2 (its last element's last byte)
        assert!(txs_of_blobs(&bad).is_none());
    }

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
