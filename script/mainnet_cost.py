#!/usr/bin/env python3
"""What the gas measured on the testnet would cost on Ethereum mainnet.

usage: mainnet_cost.py <deploy verifier gas> <deploy settlement gas> <first batch gas> <blob gas> <txs in batch> [later batch gas]

Reads the fees of the last 1024 mainnet blocks (eth_feeHistory) from MAINNET_RPC_URL (default: a
public node) and the ETH price from CoinGecko (or ETH_USD), then prints the cost of deploying,
of one settled batch, and per L2 transaction for larger batches. Nothing is sent: read-only.
"""
import json
import os
import sys
import urllib.request

UA = {"content-type": "application/json", "user-agent": "ere-mainnet-cost/1.0"}
RPC = os.environ.get("MAINNET_RPC_URL") or "https://ethereum-rpc.publicnode.com"
TX_BYTES = 118  # one signed L2 transaction in the blob
BLOB_TXS = (4096 * 31 - 4) // TX_BYTES  # transactions that fit in one blob


def rpc(method, params):
    req = urllib.request.Request(RPC, json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode(), UA)
    reply = json.load(urllib.request.urlopen(req, timeout=60))
    if "error" in reply:
        raise RuntimeError(reply["error"])
    return reply["result"]


def pct(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(p / 100 * len(xs)))]


def eth_usd():
    if os.environ.get("ETH_USD"):
        return float(os.environ["ETH_USD"])
    try:
        req = urllib.request.Request("https://api.coingecko.com/api/v3/simple/price?ids=ethereum&vs_currencies=usd", headers=UA)
        return float(json.load(urllib.request.urlopen(req, timeout=30))["ethereum"]["usd"])
    except Exception:
        return None


def main():
    dv, ds, settle, blob_gas, txs = (int(x) for x in sys.argv[1:6])
    h = rpc("eth_feeHistory", ["0x400", "latest", [50]])
    base = [int(x, 16) for x in h["baseFeePerGas"]]
    blob = [int(x, 16) for x in h["baseFeePerBlobGas"]]
    tip = [int(r[0], 16) for r in h["reward"]]
    usd = eth_usd()
    blocks = len(h["gasUsedRatio"])
    print(f"\n=== mainnet estimate (fees of the last {blocks} mainnet blocks, up to block {int(h['oldestBlock'], 16) + blocks - 1}) ===")
    print(f"base fee gwei: p10 {pct(base, 10) / 1e9:.3f}, median {pct(base, 50) / 1e9:.3f}, p90 {pct(base, 90) / 1e9:.3f}, max {max(base) / 1e9:.3f}")
    print(f"priority fee (median tip) gwei: {pct(tip, 50) / 1e9:.3f}")
    print(f"blob base fee gwei: median {pct(blob, 50) / 1e9:.9f}, p90 {pct(blob, 90) / 1e9:.9f}, max {max(blob) / 1e9:.9f}")
    print(f"blob space used: {sum(h['blobGasUsedRatio']) / blocks * 100:.0f}% of the per-block maximum")
    print(f"ETH price: {'$%.0f' % usd if usd else 'unknown'}")

    def cost(gas, bgas, gwei, blob_gwei):
        e = (gas * gwei + bgas * blob_gwei) / 1e9
        return f"{e:.6f} ETH" + (f" (${e * usd:,.2f})" if usd else "")

    steady = int(sys.argv[6]) if len(sys.argv) > 6 else settle  # measured on batch 2
    print(f"\nmeasured gas: deploy verifier {dv}, deploy settlement {ds}, first batch {settle} (+ {blob_gas} blob gas), later batches {steady}")
    med, tipm = pct(base, 50) / 1e9, pct(tip, 50) / 1e9
    scenarios = (
        ("today's median", med + tipm, max(pct(blob, 50), 1) / 1e9),
        ("busy hour (p90)", pct(base, 90) / 1e9 + tipm, max(pct(blob, 90), 1) / 1e9),
        ("10 gwei gas", 10.0, max(pct(blob, 50), 1) / 1e9),
        ("50 gwei gas, blob spike 30 gwei", 50.0, 30.0),
    )
    for name, gwei, bg in scenarios:
        print(f"\n[{name}: {gwei:.3f} gwei gas, {bg:.9f} gwei blob gas]")
        print(f"  deploy once (both contracts): {cost(dv + ds, 0, gwei, bg)}")
        print(f"  one batch (later batches):   {cost(steady, blob_gas, gwei, bg)}")
        for n in (txs, 100, 500, BLOB_TXS):
            e = (steady * gwei + blob_gas * bg) / 1e9 / n
            print(f"    per L2 tx, {n:>5} tx/batch: {e:.8f} ETH" + (f" (${e * usd:.5f})" if usd else ""))
    print(f"\none blob holds {BLOB_TXS} transactions of {TX_BYTES} bytes; settle gas does not grow with the batch (one proof, one blob)")


if __name__ == "__main__":
    main()
