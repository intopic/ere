// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {SSRapSettlementVerifierV2} from "../contracts/SSRapSettlementVerifierV2.sol";
import {P3WrapperVerifier} from "../contracts/P3WrapperVerifier.sol";
import {IGroth16Verifier} from "../contracts/IGroth16Verifier.sol";
import {P3SettlementFixture as F} from "./P3SettlementFixture.sol";

interface VmP {
    function prank(address) external;
    function expectRevert(bytes4) external;
    function blobhashes(bytes32[] calldata) external;
    function chainId(uint256) external;
}

/// P4b: the same settlement contract, with the verifier of the circuit that checks the 5-lane
/// Plonky3 batch-STARK inside the SNARK (cargo run -p ss_rap_settlement --example export_p3_fixture).
contract P3SettlementTest {
    VmP internal constant vm = VmP(address(uint160(uint256(keccak256("hevm cheat code")))));
    address internal constant AGG = address(0xA66);
    uint256 internal constant P_MOD = 21888242871839275222246405745257275088696311157297823662689037894645226208583;

    event log_named_uint(string key, uint256 val);

    SSRapSettlementVerifierV2 internal settlement;
    P3WrapperVerifier internal groth16;

    /// The transaction's blob hashes; set on every call, since newer forge does not keep
    /// blobhashes from setUp in the test.
    bytes32[] internal blobSet;

    function setUp() public {
        groth16 = new P3WrapperVerifier();
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

    function _settle(bytes32 newRoot, bytes32 vUmt, uint256[2] memory a, uint256[2][2] memory b, uint256[2] memory c) internal {
        vm.blobhashes(blobSet);
        vm.prank(AGG);
        settlement.verifyAndSettleBatchV2(F.OLD_ROOT, newRoot, vUmt, F.BATCH, _ev(), a, b, c);
    }

    function test_publicInputMatchesRust() public view {
        uint256 x = settlement.computePublicInput(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BLOB_HASH, F.BATCH, F.BLOB_POINT, F.blobValues());
        require(x == F.PUBLIC_INPUT, "public input differs from Rust");
        require(groth16.verifyProof(F.a(), F.b(), F.c(), x), "Plonky3-wrapper proof must verify in Solidity");
    }

    function test_settlesWithPlonky3VerifiedInside() public {
        uint256 g = gasleft();
        _settle(F.NEW_ROOT, F.VUMT_ROOT, F.a(), F.b(), F.c());
        emit log_named_uint("verifyAndSettleBatchV2 gas, Plonky3 settlement circuit", g - gasleft());
        require(settlement.latestStateRoot() == F.NEW_ROOT, "root not advanced");
    }

    function test_rejectsAnotherNewRoot() public {
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        _settle(bytes32(uint256(F.NEW_ROOT) ^ 1), F.VUMT_ROOT, F.a(), F.b(), F.c());
    }

    function test_rejectsAnotherVUmtRoot() public {
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        _settle(F.NEW_ROOT, bytes32(uint256(F.VUMT_ROOT) ^ 1), F.a(), F.b(), F.c());
    }

    function test_rejectsValidPointsForWrongStatement() public {
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        _settle(F.NEW_ROOT, F.VUMT_ROOT, F.c(), F.b(), F.a());
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
}
