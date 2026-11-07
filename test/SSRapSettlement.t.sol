// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {SSRapSettlementVerifierV2} from "../contracts/SSRapSettlementVerifierV2.sol";
import {Groth16Verifier} from "../contracts/Groth16Verifier.sol";
import {IGroth16Verifier} from "../contracts/IGroth16Verifier.sol";
import {SettlementFixture as F} from "./SettlementFixture.sol";

/// Minimal cheatcode interface, so the tests need no external dependency.
interface Vm {
    function prank(address) external;
    function expectRevert(bytes4) external;
    function blobhashes(bytes32[] calldata) external;
    function chainId(uint256) external;
}

/// End-to-end L1 tests with a proof produced by the Rust pipeline
/// (cargo run -p ss_rap_settlement --example export_fixture).
contract SSRapSettlementTest {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    address internal constant AGG = address(0xA66);
    uint256 internal constant P_MOD = 21888242871839275222246405745257275088696311157297823662689037894645226208583;

    event log_named_uint(string key, uint256 val);

    SSRapSettlementVerifierV2 internal settlement;
    Groth16Verifier internal groth16;

    /// The transaction's blob hashes; set on every call, since newer forge does not keep
    /// blobhashes from setUp in the test.
    bytes32[] internal blobSet;

    function setUp() public {
        groth16 = new Groth16Verifier();
        settlement = new SSRapSettlementVerifierV2(F.OLD_ROOT, AGG, IGroth16Verifier(address(groth16)), 1);
        // the fixture's proof is bound to this contract's address (the test contract's 2nd CREATE)
        require(address(settlement) == F.SETTLEMENT, "settlement is not at the fixture's address");
        vm.chainId(F.CHAIN_ID);
        blobSet.push(F.BLOB_HASH);
    }

    /// The fixture's blob evaluation (audit H-01): point, values, KZG commitment and opening.
    function _ev() internal pure returns (SSRapSettlementVerifierV2.BlobEvaluation memory) {
        return SSRapSettlementVerifierV2.BlobEvaluation(F.BLOB_POINT, F.blobValues(), F.KZG);
    }

    /// Settles with the fixture's proof and another blob evaluation; expects `err`.
    function _settleEv(SSRapSettlementVerifierV2.BlobEvaluation memory ev, bytes4 err) internal {
        vm.blobhashes(blobSet);
        vm.prank(AGG);
        vm.expectRevert(err);
        settlement.verifyAndSettleBatchV2(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BATCH, ev, F.a(), F.b(), F.c());
    }

    /// Audit H-01: the blob's value at the point is checked against the blob itself (0x0a).
    function test_rejectsAnotherBlobValue() public {
        SSRapSettlementVerifierV2.BlobEvaluation memory ev = _ev();
        ev.values[0] = bytes32(uint256(ev.values[0]) ^ 1);
        _settleEv(ev, SSRapSettlementVerifierV2.InvalidBlobEvaluation.selector);
    }

    function test_rejectsAnotherBlobPoint() public {
        SSRapSettlementVerifierV2.BlobEvaluation memory ev = _ev();
        ev.point = bytes32(uint256(ev.point) + 1);
        _settleEv(ev, SSRapSettlementVerifierV2.InvalidBlobEvaluation.selector);
    }

    function test_rejectsMissingOrExtraKzgOpening() public {
        SSRapSettlementVerifierV2.BlobEvaluation memory ev = _ev();
        ev.kzg = "";
        _settleEv(ev, SSRapSettlementVerifierV2.InvalidBlobEvaluation.selector);
        ev = _ev();
        ev.values = new bytes32[](2);
        _settleEv(ev, SSRapSettlementVerifierV2.InvalidBlobEvaluation.selector);
    }

    function _settle(bytes32 newRoot, uint256 batch, uint256[2] memory a, uint256[2][2] memory b, uint256[2] memory c) internal {
        vm.blobhashes(blobSet);
        vm.prank(AGG);
        settlement.verifyAndSettleBatchV2(F.OLD_ROOT, newRoot, F.VUMT_ROOT, batch, _ev(), a, b, c);
    }

    function test_publicInputMatchesRust() public view {
        uint256 x = settlement.computePublicInput(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BLOB_HASH, F.BATCH, F.BLOB_POINT, F.blobValues());
        require(x == F.PUBLIC_INPUT, "public input differs from Rust");
        require(groth16.verifyProof(F.a(), F.b(), F.c(), x), "Rust proof must verify in Solidity");
    }

    function test_settlesValidBatch() public {
        uint256 g = gasleft();
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
        emit log_named_uint("verifyAndSettleBatchV2 gas (incl. cold storage writes)", g - gasleft());
        require(settlement.latestBatchNumber() == F.BATCH, "batch not advanced");
        require(settlement.latestStateRoot() == F.NEW_ROOT, "root not advanced");
    }

    function test_rejectsTamperedProof() public {
        uint256[2] memory c = F.c();
        c[1] = (c[1] + 1) % P_MOD;
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        uint256 g = gasleft();
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), c);
        // Invalid point: the pairing precompile fails, but only burns its capped gas.
        require(g - gasleft() < 400_000, "invalid proof must stay cheap to reject");
    }

    function test_rejectsValidPointsForWrongStatement() public {
        // Swap A and C: both are valid curve points, so the pairing runs and returns false.
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        _settle(F.NEW_ROOT, F.BATCH, F.c(), F.b(), F.a());
    }

    function test_rejectsProofForAnotherStateRoot() public {
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        _settle(bytes32(uint256(F.NEW_ROOT) ^ 1), F.BATCH, F.a(), F.b(), F.c());
    }

    function test_rejectsOtherBlob() public {
        bytes32[] memory blobs = new bytes32[](1);
        blobs[0] = bytes32(uint256(F.BLOB_HASH) ^ 1);
        blobSet = blobs;
        vm.blobhashes(blobs);
        // the KZG opening is for the fixture's blob: the precompile rejects it for another one
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidBlobEvaluation.selector);
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }

    function test_severalBlobsBindTheirKeccak() public {
        bytes32[] memory blobs = new bytes32[](3);
        blobs[0] = F.BLOB_HASH;
        blobs[1] = bytes32(uint256(2));
        blobs[2] = bytes32(uint256(3));
        blobSet = blobs;
        vm.blobhashes(blobs);
        require(settlement.blobsHash() == keccak256(abi.encodePacked(blobs[0], blobs[1], blobs[2])), "blobs hash");
        // this deployment has one blob slot: a transaction with more blobs is refused
        vm.expectRevert(SSRapSettlementVerifierV2.TooManyBlobs.selector);
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }

    function test_rejectsMissingBlob() public {
        delete blobSet;
        vm.expectRevert(SSRapSettlementVerifierV2.MissingEip4844Blob.selector);
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }

    function test_rejectsOtherChain() public {
        vm.chainId(1);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }

    function test_rejectsWrongBatchNumber() public {
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidBatchSequence.selector);
        _settle(F.NEW_ROOT, F.BATCH + 1, F.a(), F.b(), F.c());
    }

    function test_rejectsWrongOldRoot() public {
        vm.blobhashes(blobSet);
        vm.prank(AGG);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidStateTransition.selector);
        settlement.verifyAndSettleBatchV2(bytes32(0), F.NEW_ROOT, F.VUMT_ROOT, F.BATCH, _ev(), F.a(), F.b(), F.c());
    }

    function test_rejectsReplay() public {
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidBatchSequence.selector);
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }

    function test_rejectsUnauthorizedAggregator() public {
        vm.blobhashes(blobSet);
        vm.expectRevert(SSRapSettlementVerifierV2.UnauthorizedAggregator.selector);
        settlement.verifyAndSettleBatchV2(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BATCH, _ev(), F.a(), F.b(), F.c());
    }

    function test_rejectsNonCanonicalCoordinate() public {
        uint256[2] memory a = F.a();
        a[0] = a[0] + P_MOD; // same point mod p, but not canonical: malleability guard
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        _settle(F.NEW_ROOT, F.BATCH, a, F.b(), F.c());
    }

    /// Audit SET-06: the same proof, header and blob on another deployment (same chain, key,
    /// genesis root and aggregator) must not settle.
    function test_rejectsSameProofOnAnotherDeployment() public {
        SSRapSettlementVerifierV2 twin = new SSRapSettlementVerifierV2(F.OLD_ROOT, AGG, IGroth16Verifier(address(groth16)), 1);
        vm.blobhashes(blobSet);
        vm.prank(AGG);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        twin.verifyAndSettleBatchV2(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BATCH, _ev(), F.a(), F.b(), F.c());
    }

    function test_constructorRejectsMissingAggregatorOrVerifier() public {
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidDeployment.selector);
        new SSRapSettlementVerifierV2(F.OLD_ROOT, address(0), IGroth16Verifier(address(groth16)), 1);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidDeployment.selector);
        new SSRapSettlementVerifierV2(F.OLD_ROOT, AGG, IGroth16Verifier(address(0xBEEF)), 1);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidDeployment.selector);
        new SSRapSettlementVerifierV2(F.OLD_ROOT, AGG, IGroth16Verifier(address(groth16)), 0);
    }

    /// A slot without a blob must carry the value 0 (else the proven elements of that slot are
    /// not empty, and nothing on L1 holds them).
    function test_rejectsValueForEmptySlot() public {
        SSRapSettlementVerifierV2 two = new SSRapSettlementVerifierV2(F.OLD_ROOT, AGG, IGroth16Verifier(address(groth16)), 2);
        SSRapSettlementVerifierV2.BlobEvaluation memory ev = _ev();
        ev.values = new bytes32[](2);
        ev.values[0] = F.blobValues()[0];
        ev.values[1] = bytes32(uint256(1));
        vm.blobhashes(blobSet);
        vm.prank(AGG);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidBlobEvaluation.selector);
        two.verifyAndSettleBatchV2(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BATCH, ev, F.a(), F.b(), F.c());
        // with 0 there the blob checks pass, and the proof (made for one slot) does not verify
        ev.values[1] = bytes32(0);
        vm.blobhashes(blobSet);
        vm.prank(AGG);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        two.verifyAndSettleBatchV2(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BATCH, ev, F.a(), F.b(), F.c());
    }
}
