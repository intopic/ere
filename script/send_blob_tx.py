"""Signs an EIP-4844 transaction carrying the batch's own blob, byte for byte.

`cast send --blob` re-encodes the file it is given (alloy's SimpleCoder), so its blob, and the
versioned hash the contract reads with blobhash(0), would not be the ones the proof binds. This
signs our exact 131072-byte blob and checks that its versioned hash is the proven one.

usage: send_blob_tx.py <blob.bin> <expected versioned hash> <to> <calldata> <chain id> <nonce>
       <max fee> <priority fee> <max blob fee>   (key in SEPOLIA_PRIVATE_KEY, RPC in SEPOLIA_RPC_URL);
       sends it with eth_sendRawTransaction (the signed tx, blob included, is too long for argv)
       and prints the transaction hash.
"""
import json
import os
import sys
import urllib.request

from eth_account import Account
from eth_account.typed_transactions import TypedTransaction

blob_path, want, to, data, chain, nonce, max_fee, tip, blob_fee = sys.argv[1:10]
blob = open(blob_path, "rb").read()
assert len(blob) == 131072, len(blob)
tx = {
    "type": 3,
    "chainId": int(chain),
    "nonce": int(nonce),
    "to": to,
    "value": 0,
    "data": data,
    "gas": 600_000,
    "maxFeePerGas": int(max_fee),
    "maxPriorityFeePerGas": int(tip),
    "maxFeePerBlobGas": int(blob_fee),
}
signed = Account.sign_transaction(tx, os.environ["SEPOLIA_PRIVATE_KEY"], blobs=[blob])
got = TypedTransaction.from_bytes(signed.raw_transaction).transaction.dictionary["blobVersionedHashes"][0]
got = "0x" + bytes(got).hex()
if got.lower() != want.lower():
    sys.exit(f"blob versioned hash {got} is not the proven {want}")
raw = "0x" + signed.raw_transaction.hex().removeprefix("0x")
req = urllib.request.Request(
    os.environ["SEPOLIA_RPC_URL"],
    data=json.dumps({"jsonrpc": "2.0", "id": 1, "method": "eth_sendRawTransaction", "params": [raw]}).encode(),
    headers={"content-type": "application/json"},
)
reply = json.load(urllib.request.urlopen(req, timeout=60))
if "error" in reply:
    sys.exit(f"eth_sendRawTransaction: {reply['error']}")
print(reply["result"])
