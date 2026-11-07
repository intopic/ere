"""Signs an EIP-4844 transaction carrying the batch's own blobs, byte for byte.

`cast send --blob` re-encodes the file it is given (alloy's SimpleCoder), so its blob, and the
versioned hash the contract reads with blobhash(0), would not be the ones the proof binds. This
signs our exact 131072-byte blob and checks that its versioned hash is the proven one.

A batch larger than one blob is carried by several blobs of one transaction; the contract then
binds keccak256 of their versioned hashes (settlement/src/blob.rs, `blobs_hash`).

usage: send_blob_tx.py <blob.bin[,blob-1.bin,...]> <expected blob hash> <to> <calldata> <chain id> <nonce>
       <max fee> <priority fee> <max blob fee>   (key in SEPOLIA_PRIVATE_KEY, RPC in SEPOLIA_RPC_URL);
       sends it with eth_sendRawTransaction (the signed tx, blob included, is too long for argv)
       and prints the transaction hash.
"""
import json
import os
import sys
import urllib.error
import urllib.request

from eth_account import Account
from eth_account.typed_transactions import TypedTransaction
from eth_utils import keccak

blob_path, want, to, data, chain, nonce, max_fee, tip, blob_fee = sys.argv[1:10]
blobs = [open(p, "rb").read() for p in blob_path.split(",")]
assert all(len(b) == 131072 for b in blobs), [len(b) for b in blobs]
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
signed = Account.sign_transaction(tx, os.environ["SEPOLIA_PRIVATE_KEY"], blobs=blobs)
hashes = [bytes(h) for h in TypedTransaction.from_bytes(signed.raw_transaction).transaction.dictionary["blobVersionedHashes"]]
got = "0x" + (hashes[0] if len(hashes) == 1 else keccak(b"".join(hashes))).hex()
if got.lower() != want.lower():
    sys.exit(f"blob hash {got} is not the proven {want}")
raw = "0x" + signed.raw_transaction.hex().removeprefix("0x")
# Some RPC providers cap the request body (a tx with 5 blobs is ~1.3 MB of hex): try the
# configured RPC first, then the public ones in BLOB_RPC_URLS. The tx is signed, so any node can relay it.
urls = [os.environ["SEPOLIA_RPC_URL"]] + [u for u in os.environ.get("BLOB_RPC_URLS", "https://ethereum-sepolia-rpc.publicnode.com,https://sepolia.drpc.org").split(",") if u]
body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "eth_sendRawTransaction", "params": [raw]}).encode()
errors = []
for i, url in enumerate(urls):
    name = "SEPOLIA_RPC_URL" if i == 0 else url  # never print the configured (secret) URL
    req = urllib.request.Request(url, data=body, headers={"content-type": "application/json", "user-agent": "ere-sepolia-e2e/1.0"})
    try:
        reply = json.load(urllib.request.urlopen(req, timeout=120))
    except urllib.error.HTTPError as e:
        errors.append(f"{name}: HTTP {e.code}: {e.read()[:300]!r}")
        continue
    except (urllib.error.URLError, TimeoutError, ValueError) as e:
        errors.append(f"{name}: {e}")
        continue
    if "error" in reply:
        if "already known" in str(reply["error"]).lower():
            print("0x" + bytes(signed.hash).hex().removeprefix("0x"))
            sys.exit(0)
        errors.append(f"{name}: {reply['error']}")
        continue
    if i > 0:
        print(f"sent through {name}", file=sys.stderr)
    print(reply["result"])
    sys.exit(0)
sys.exit("eth_sendRawTransaction failed on every RPC:\n  " + "\n  ".join(errors))
