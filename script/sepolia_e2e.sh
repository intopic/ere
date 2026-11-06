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
verifier=$(forge create contracts/E2EVerifier.sol:E2EVerifier "${send[@]}" --broadcast --json | jq -r .deployedTo)
echo "verifier $verifier"
wait_code "$verifier"
settlement=$(forge create contracts/SSRapSettlementVerifierV2.sol:SSRapSettlementVerifierV2 "${send[@]}" --broadcast --json \
  --constructor-args "$OLD_ROOT" "$me" "$verifier" | jq -r .deployedTo)
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

# the batch itself: calldata plus the blob the contract reads with blobhash(0)
tx=$(cast send "$settlement" \
  "verifyAndSettleBatchV2(bytes32,bytes32,bytes32,uint256,uint256[2],uint256[2][2],uint256[2])" \
  "$OLD_ROOT" "$NEW_ROOT" "$VUMT_ROOT" "$BATCH" "$PROOF_A" "$PROOF_B" "$PROOF_C" \
  --blob --path "$out/blob.bin" "${send[@]}" --json | jq -r .transactionHash)
echo "batch transaction $tx"
cast receipt "$tx" --rpc-url "$SEPOLIA_RPC_URL" --json | jq '{status,blockNumber,gasUsed,blobGasUsed,blobGasPrice}'

root=$(cast call "$settlement" "latestStateRoot()(bytes32)" --rpc-url "$SEPOLIA_RPC_URL")
[ "$root" = "$NEW_ROOT" ] || { echo "state root is $root, expected $NEW_ROOT"; exit 1; }
echo "settled: batch $(cast call "$settlement" "latestBatchNumber()(uint256)" --rpc-url "$SEPOLIA_RPC_URL"), state root $root"
echo "explorer: https://sepolia.etherscan.io/tx/$tx"
