#!/usr/bin/env bash
# Settles one real SS-RAP v2 batch on a public testnet (default Sepolia): generates the batch
# and its Groth16 proof, deploys the verifier and the settlement contract, then sends the batch
# as an EIP-4844 blob transaction and checks that the contract advanced its state root.
#
#   SEPOLIA_RPC_URL=... SEPOLIA_PRIVATE_KEY=... script/sepolia_e2e.sh
#
# The key is a TEST key: this deploys a DEV verifying key (public seed), never for real funds.
set -euo pipefail

: "${SEPOLIA_RPC_URL:?SEPOLIA_RPC_URL is not set}"
: "${SEPOLIA_PRIVATE_KEY:?SEPOLIA_PRIVATE_KEY is not set}"
out=out/e2e
chain=$(cast chain-id --rpc-url "$SEPOLIA_RPC_URL")
me=$(cast wallet address --private-key "$SEPOLIA_PRIVATE_KEY")
cast --version
echo "chain $chain, sender $me, balance $(cast balance "$me" --rpc-url "$SEPOLIA_RPC_URL" --ether) ETH"

cargo run --release --locked -p ss_rap_settlement --example sepolia_e2e -- "$chain" "$out"
cp "$out/E2EVerifier.sol" contracts/E2EVerifier.sol
# shellcheck disable=SC1090
source "$out/e2e.env"

send=(--rpc-url "$SEPOLIA_RPC_URL" --private-key "$SEPOLIA_PRIVATE_KEY")
# a load-balanced RPC can answer from a node that has not seen the new block yet
wait_code() {
  for _ in $(seq 1 30); do
    [ "$(cast code "$1" --rpc-url "$SEPOLIA_RPC_URL")" != "0x" ] && return 0
    sleep 4
  done
  echo "no code at $1 after 120 s"; return 1
}
dv=$(forge create contracts/E2EVerifier.sol:E2EVerifier "${send[@]}" --broadcast --json)
verifier=$(jq -r .deployedTo <<<"$dv")
echo "verifier $verifier"
wait_code "$verifier"
ds=$(forge create contracts/SSRapSettlementVerifierV2.sol:SSRapSettlementVerifierV2 "${send[@]}" --broadcast --json \
  --constructor-args "$OLD_ROOT" "$me" "$verifier")
settlement=$(jq -r .deployedTo <<<"$ds")
echo "settlement $settlement"
wait_code "$settlement"

# the proof must verify on-chain before the blob transaction is paid for
ok=$(cast call "$verifier" "verifyProof(uint256[2],uint256[2][2],uint256[2],uint256)(bool)" \
  "$PROOF_A" "$PROOF_B" "$PROOF_C" "$PUBLIC_INPUT" --rpc-url "$SEPOLIA_RPC_URL")
echo "verifyProof on-chain: $ok"
[ "$ok" = "true" ] || { echo "the proof does not verify on-chain"; exit 1; }
onchain=$(cast call "$settlement" "computePublicInput(bytes32,bytes32,bytes32,bytes32,uint256)(uint256)" \
  "$OLD_ROOT" "$NEW_ROOT" "$VUMT_ROOT" "$BLOB_HASH" "$BATCH" --rpc-url "$SEPOLIA_RPC_URL")
echo "public input on-chain: $onchain (prover: $PUBLIC_INPUT)"
verify_gas=$(cast estimate "$verifier" "verifyProof(uint256[2],uint256[2][2],uint256[2],uint256)" \
  "$PROOF_A" "$PROOF_B" "$PROOF_C" "$PUBLIC_INPUT" --rpc-url "$SEPOLIA_RPC_URL")
echo "verifyProof alone: $verify_gas gas (incl. 21000 base)"

# each batch: calldata plus OUR blob (the one the proof binds), read with blobhash(0)
settle_batch() {  # <env file> <blob file>; sets tx
  # shellcheck disable=SC1090
  source "$1"
  calldata=$(cast calldata "verifyAndSettleBatchV2(bytes32,bytes32,bytes32,uint256,uint256[2],uint256[2][2],uint256[2])" \
    "$OLD_ROOT" "$NEW_ROOT" "$VUMT_ROOT" "$BATCH" "$PROOF_A" "$PROOF_B" "$PROOF_C")
  gas=$(cast gas-price --rpc-url "$SEPOLIA_RPC_URL")
  blobfee=$(cast to-dec "$(cast rpc eth_blobBaseFee --rpc-url "$SEPOLIA_RPC_URL" | tr -d '"')")
  nonce=$(cast nonce "$me" --rpc-url "$SEPOLIA_RPC_URL" --block pending)
  tx=$(python3 script/send_blob_tx.py "$2" "$BLOB_HASH" "$settlement" "$calldata" "$chain" "$nonce" \
    $((gas * 2 + 2000000000)) 2000000000 $((blobfee * 2 + 1000000000)))
  [ -n "$tx" ] || { echo "the blob transaction was not accepted"; exit 1; }
  cast receipt "$tx" --rpc-url "$SEPOLIA_RPC_URL" >/dev/null  # waits for inclusion
  echo "batch $BATCH transaction $tx"
  cast receipt "$tx" --rpc-url "$SEPOLIA_RPC_URL" --json | jq -c '{status,blockNumber,gasUsed,blobGasUsed,blobGasPrice}'
  for _ in $(seq 1 30); do  # a load-balanced RPC may still answer from an older block
    root=$(cast call "$settlement" "latestStateRoot()(bytes32)" --rpc-url "$SEPOLIA_RPC_URL")
    [ "$root" = "$NEW_ROOT" ] && break
    sleep 4
  done
  [ "$root" = "$NEW_ROOT" ] || { echo "state root is $root, expected $NEW_ROOT"; exit 1; }
  echo "settled: batch $(cast call "$settlement" "latestBatchNumber()(uint256)" --rpc-url "$SEPOLIA_RPC_URL"), state root $root"
  echo "explorer: https://sepolia.etherscan.io/tx/$tx"
}
gas_of() { cast receipt "$1" gasUsed --rpc-url "$SEPOLIA_RPC_URL" | awk '{print $1}'; }

settle_batch "$out/e2e.env" "$out/blob.bin"
tx1=$tx
settle_batch "$out/e2e2.env" "$out/blob2.bin"
tx2=$tx

# replaying batch 2 must fail: the contract only takes the next batch on top of its root
if replay=$(cast estimate "$settlement" "verifyAndSettleBatchV2(bytes32,bytes32,bytes32,uint256,uint256[2],uint256[2][2],uint256[2])" \
  "$OLD_ROOT" "$NEW_ROOT" "$VUMT_ROOT" "$BATCH" "$PROOF_A" "$PROOF_B" "$PROOF_C" --from "$me" --rpc-url "$SEPOLIA_RPC_URL" 2>&1); then
  echo "REPLAY OF BATCH 2 WAS ACCEPTED"; exit 1
fi
echo "replay of batch 2 rejected (as it must be): $(grep -o '0x[0-9a-f]\{8\}\|InvalidBatchSequence\|revert[^,]*' <<<"$replay" | head -1)"

# what the same transactions would cost on mainnet, at the fees of the last ~1024 mainnet blocks
deploy_verifier_gas=$(gas_of "$(jq -r .transactionHash <<<"$dv")")
deploy_settlement_gas=$(gas_of "$(jq -r .transactionHash <<<"$ds")")
settle_gas=$(gas_of "$tx1")
settle2_gas=$(gas_of "$tx2")
blob_gas=$(cast to-dec "$(cast receipt "$tx2" --rpc-url "$SEPOLIA_RPC_URL" --json | jq -r .blobGasUsed)")
echo "gas: deploy verifier $deploy_verifier_gas, deploy settlement $deploy_settlement_gas, batch 1 $settle_gas, batch 2 $settle2_gas, blob gas $blob_gas per batch"
echo "code size: verifier $(( ($(cast code "$verifier" --rpc-url "$SEPOLIA_RPC_URL" | wc -c) - 3) / 2 )) bytes, settlement $(( ($(cast code "$settlement" --rpc-url "$SEPOLIA_RPC_URL" | wc -c) - 3) / 2 )) bytes"
python3 script/mainnet_cost.py "$deploy_verifier_gas" "$deploy_settlement_gas" "$settle_gas" "$blob_gas" "$TXS" "$settle2_gas" \
  || echo "(mainnet fee estimate unavailable)"
