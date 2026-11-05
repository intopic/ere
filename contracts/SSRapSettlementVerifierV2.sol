// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {IGroth16Verifier} from "./IGroth16Verifier.sol";

/**
 * @title SSRapSettlementVerifierV2
 * @notice Settles SS-RAP v2 batches on Ethereum L1 (Phase C of docs/PLANI_MVP.md).
 * @dev Changes from the v2.0 prototype:
 *      1. The Groth16 verifying key is no longer hard-coded with known multiples of the
 *         generators (ALPHA = [11]G1, BETA = [5]G2, ...), which let anyone forge proofs.
 *         The verifier is a separate contract generated from a real setup
 *         (settlement/src/groth16.rs), injected at deployment.
 *      2. The public input binds oldStateRoot, newStateRoot, vUmtMerkleRoot (all STARK
 *         commitments), the EIP-4844 blob of the batch, the batch number and the chain id,
 *         exactly as in the PDF (f.14-15); settlement/src/public_input.rs computes the same value.
 */
contract SSRapSettlementVerifierV2 {
    uint256 internal constant R_MOD =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;

    IGroth16Verifier public immutable verifier;
    address public immutable sequencerAggregator;

    bytes32 public latestStateRoot;
    uint256 public latestBatchNumber;

    event BatchSettledV2(
        uint256 indexed batchNumber,
        bytes32 indexed oldStateRoot,
        bytes32 indexed newStateRoot,
        bytes32 vUmtMerkleRoot,
        bytes32 blobVersionedHash
    );

    error UnauthorizedAggregator();
    error InvalidBatchSequence();
    error InvalidStateTransition();
    error MissingEip4844Blob();
    error InvalidGroth16Proof();

    constructor(bytes32 genesisStateRoot, address aggregator, IGroth16Verifier groth16Verifier) {
        latestStateRoot = genesisStateRoot;
        sequencerAggregator = aggregator;
        verifier = groth16Verifier;
    }

    /// @notice The public input the proof must attest to (also used off-chain by the prover).
    function computePublicInput(
        bytes32 oldStateRoot,
        bytes32 newStateRoot,
        bytes32 vUmtMerkleRoot,
        bytes32 blobVersionedHash,
        uint256 batchNumber
    ) public view returns (uint256) {
        return uint256(
            keccak256(
                abi.encodePacked(oldStateRoot, newStateRoot, vUmtMerkleRoot, blobVersionedHash, batchNumber, block.chainid)
            )
        ) % R_MOD;
    }

    /// @notice Verifies the batch proof and advances the canonical L1 state root.
    function verifyAndSettleBatchV2(
        bytes32 oldStateRoot,
        bytes32 newStateRoot,
        bytes32 vUmtMerkleRoot,
        uint256 batchNumber,
        uint256[2] calldata proofA,
        uint256[2][2] calldata proofB,
        uint256[2] calldata proofC
    ) external {
        if (msg.sender != sequencerAggregator) revert UnauthorizedAggregator();
        if (batchNumber != latestBatchNumber + 1) revert InvalidBatchSequence();
        if (oldStateRoot != latestStateRoot) revert InvalidStateTransition();

        bytes32 blobHash = blobhash(0);
        if (blobHash == bytes32(0)) revert MissingEip4844Blob();

        uint256 publicInput = computePublicInput(oldStateRoot, newStateRoot, vUmtMerkleRoot, blobHash, batchNumber);
        if (!verifier.verifyProof(proofA, proofB, proofC, publicInput)) revert InvalidGroth16Proof();

        latestStateRoot = newStateRoot;
        latestBatchNumber = batchNumber;
        emit BatchSettledV2(batchNumber, oldStateRoot, newStateRoot, vUmtMerkleRoot, blobHash);
    }
}
