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

    function setUp() public {
        groth16 = new Groth16Verifier();
        settlement = new SSRapSettlementVerifierV2(F.OLD_ROOT, AGG, IGroth16Verifier(address(groth16)));
        vm.chainId(F.CHAIN_ID);
        bytes32[] memory blobs = new bytes32[](1);
        blobs[0] = F.BLOB_HASH;
        vm.blobhashes(blobs);
    }

    function _settle(bytes32 newRoot, uint256 batch, uint256[2] memory a, uint256[2][2] memory b, uint256[2] memory c) internal {
        vm.prank(AGG);
        settlement.verifyAndSettleBatchV2(F.OLD_ROOT, newRoot, F.VUMT_ROOT, batch, a, b, c);
    }

    function test_publicInputMatchesRust() public view {
        uint256 x = settlement.computePublicInput(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BLOB_HASH, F.BATCH);
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
        vm.blobhashes(blobs);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }

    function test_rejectsMissingBlob() public {
        vm.blobhashes(new bytes32[](0));
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
        vm.prank(AGG);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidStateTransition.selector);
        settlement.verifyAndSettleBatchV2(bytes32(0), F.NEW_ROOT, F.VUMT_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }

    function test_rejectsReplay() public {
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidBatchSequence.selector);
        _settle(F.NEW_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }

    function test_rejectsUnauthorizedAggregator() public {
        vm.expectRevert(SSRapSettlementVerifierV2.UnauthorizedAggregator.selector);
        settlement.verifyAndSettleBatchV2(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }

    function test_rejectsNonCanonicalCoordinate() public {
        uint256[2] memory a = F.a();
        a[0] = a[0] + P_MOD; // same point mod p, but not canonical: malleability guard
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        _settle(F.NEW_ROOT, F.BATCH, a, F.b(), F.c());
    }
}
