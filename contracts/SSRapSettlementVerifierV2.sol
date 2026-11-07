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
 *      3. The public input also binds this contract's own address (audit SET-06): a proof made
 *         for one deployment does not verify on another one with the same key, state and
 *         counter (testnet and mainnet, or an old and a new version on the same chain).
 *      4. The blob contents (audit H-01): the proof evaluates the polynomial of the blob
 *         elements it holds at a point z it derives from their digests and the blobs hash, and
 *         binds z and every value y_j. This contract checks y_j against the blob it actually
 *         carries with the point-evaluation precompile (0x0a), and y_j = 0 for an empty slot,
 *         so the proven elements are the published ones.
 */
contract SSRapSettlementVerifierV2 {
    uint256 internal constant R_MOD =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;
    /// BLS12-381 scalar field (EIP-4844 BLS_MODULUS) and the precompile's success output.
    uint256 internal constant BLS_MODULUS =
        52435875175126190479447740508185965837690552500527637822603658699938581184513;
    uint256 internal constant FIELD_ELEMENTS_PER_BLOB = 4096;
    address internal constant POINT_EVALUATION = address(0x0a);

    /// The blob part of a settlement (audit H-01): the point, one value per blob slot, and per
    /// blob of the transaction its KZG commitment (48 bytes) and opening proof at the point (48).
    struct BlobEvaluation {
        bytes32 point;
        bytes32[] values;
        bytes kzg;
    }

    IGroth16Verifier public immutable verifier;
    address public immutable sequencerAggregator;
    /// Blob slots of the circuit (the most blobs a batch may carry): part of its shape.
    uint256 public immutable blobSlots;

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
    error InvalidDeployment();
    error TooManyBlobs();
    error InvalidBlobEvaluation();

    constructor(bytes32 genesisStateRoot, address aggregator, IGroth16Verifier groth16Verifier, uint256 slots) {
        if (aggregator == address(0) || address(groth16Verifier).code.length == 0 || slots == 0) revert InvalidDeployment();
        latestStateRoot = genesisStateRoot;
        sequencerAggregator = aggregator;
        verifier = groth16Verifier;
        blobSlots = slots;
    }

    /// @notice The public input the proof must attest to (also used off-chain by the prover).
    function computePublicInput(
        bytes32 oldStateRoot,
        bytes32 newStateRoot,
        bytes32 vUmtMerkleRoot,
        bytes32 blobVersionedHash,
        uint256 batchNumber,
        bytes32 blobPoint,
        bytes32[] memory blobValues
    ) public view returns (uint256) {
        return uint256(
            keccak256(
                abi.encodePacked(
                    oldStateRoot,
                    newStateRoot,
                    vUmtMerkleRoot,
                    blobVersionedHash,
                    batchNumber,
                    block.chainid,
                    uint256(uint160(address(this))),
                    blobPoint,
                    blobValues
                )
            )
        ) % R_MOD;
    }

    /// @notice Checks the blob evaluation against the transaction's blobs (audit H-01): for blob
    /// j, p_j(point) = values[j] by the point-evaluation precompile; values[j] = 0 for every
    /// slot without a blob; no more blobs than slots.
    function checkBlobEvaluation(BlobEvaluation calldata ev) public view {
        if (ev.values.length != blobSlots) revert InvalidBlobEvaluation();
        if (blobhash(blobSlots) != bytes32(0)) revert TooManyBlobs();
        uint256 n;
        while (n < blobSlots && blobhash(n) != bytes32(0)) n++;
        if (ev.kzg.length != 96 * n || uint256(ev.point) >= BLS_MODULUS) revert InvalidBlobEvaluation();
        for (uint256 j = 0; j < blobSlots; j++) {
            if (j >= n) {
                if (ev.values[j] != bytes32(0)) revert InvalidBlobEvaluation();
                continue;
            }
            (bool ok, bytes memory out) = POINT_EVALUATION.staticcall(
                abi.encodePacked(blobhash(j), ev.point, ev.values[j], ev.kzg[96 * j:96 * j + 96])
            );
            if (!ok || out.length != 64) revert InvalidBlobEvaluation();
            (uint256 width, uint256 modulus) = abi.decode(out, (uint256, uint256));
            if (width != FIELD_ELEMENTS_PER_BLOB || modulus != BLS_MODULUS) revert InvalidBlobEvaluation();
        }
    }

    /// @notice The blob hash the proof binds: blobhash(0) when the batch fits in one blob, else
    /// keccak256 of the versioned hashes of all the transaction's blobs in order, so one proof
    /// covers every blob (see settlement/src/blob.rs, `blobs_hash`).
    function blobsHash() public view returns (bytes32) {
        bytes32 first = blobhash(0);
        if (first == bytes32(0)) revert MissingEip4844Blob();
        if (blobhash(1) == bytes32(0)) return first;
        bytes memory all = abi.encodePacked(first);
        for (uint256 i = 1; ; i++) {
            bytes32 h = blobhash(i);
            if (h == bytes32(0)) break;
            all = abi.encodePacked(all, h);
        }
        return keccak256(all);
    }

    /// @notice Verifies the batch proof and advances the canonical L1 state root.
    function verifyAndSettleBatchV2(
        bytes32 oldStateRoot,
        bytes32 newStateRoot,
        bytes32 vUmtMerkleRoot,
        uint256 batchNumber,
        BlobEvaluation calldata blobEval,
        uint256[2] calldata proofA,
        uint256[2][2] calldata proofB,
        uint256[2] calldata proofC
    ) external {
        if (msg.sender != sequencerAggregator) revert UnauthorizedAggregator();
        if (batchNumber != latestBatchNumber + 1) revert InvalidBatchSequence();
        if (oldStateRoot != latestStateRoot) revert InvalidStateTransition();

        bytes32 blobHash = blobsHash();
        checkBlobEvaluation(blobEval);

        uint256 publicInput = computePublicInput(
            oldStateRoot, newStateRoot, vUmtMerkleRoot, blobHash, batchNumber, blobEval.point, blobEval.values
        );
        if (!verifier.verifyProof(proofA, proofB, proofC, publicInput)) revert InvalidGroth16Proof();

        latestStateRoot = newStateRoot;
        latestBatchNumber = batchNumber;
        emit BatchSettledV2(batchNumber, oldStateRoot, newStateRoot, vUmtMerkleRoot, blobHash);
    }
}
