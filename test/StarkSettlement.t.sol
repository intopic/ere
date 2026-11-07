// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {SSRapSettlementVerifierV2} from "../contracts/SSRapSettlementVerifierV2.sol";
import {StarkWrapperVerifier} from "../contracts/StarkWrapperVerifier.sol";
import {IGroth16Verifier} from "../contracts/IGroth16Verifier.sol";
import {StarkSettlementFixture as F} from "./StarkSettlementFixture.sol";

interface VmS {
    function prank(address) external;
    function expectRevert(bytes4) external;
    function blobhashes(bytes32[] calldata) external;
    function chainId(uint256) external;
}

/// R8: the same settlement contract, with the verifier of the circuit that checks the state STARK
/// inside the SNARK (cargo run -p ss_rap_settlement --example export_stark_fixture).
contract StarkSettlementTest {
    VmS internal constant vm = VmS(address(uint160(uint256(keccak256("hevm cheat code")))));
    address internal constant AGG = address(0xA66);
    uint256 internal constant P_MOD = 21888242871839275222246405745257275088696311157297823662689037894645226208583;

    event log_named_uint(string key, uint256 val);

    SSRapSettlementVerifierV2 internal settlement;
    StarkWrapperVerifier internal groth16;

    /// The transaction's blob hashes; set on every call, since newer forge does not keep
    /// blobhashes from setUp in the test.
    bytes32[] internal blobSet;

    function setUp() public {
        groth16 = new StarkWrapperVerifier();
        settlement = new SSRapSettlementVerifierV2(F.OLD_ROOT, AGG, IGroth16Verifier(address(groth16)));
        // the fixture's proof is bound to this contract's address (the test contract's 2nd CREATE)
        require(address(settlement) == F.SETTLEMENT, "settlement is not at the fixture's address");
        vm.chainId(F.CHAIN_ID);
        blobSet.push(F.BLOB_HASH);
    }

    function _settle(bytes32 newRoot, bytes32 vUmt, uint256[2] memory a, uint256[2][2] memory b, uint256[2] memory c) internal {
        vm.blobhashes(blobSet);
        vm.prank(AGG);
        settlement.verifyAndSettleBatchV2(F.OLD_ROOT, newRoot, vUmt, F.BATCH, a, b, c);
    }

    function test_publicInputMatchesRust() public view {
        uint256 x = settlement.computePublicInput(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BLOB_HASH, F.BATCH);
        require(x == F.PUBLIC_INPUT, "public input differs from Rust");
        require(groth16.verifyProof(F.a(), F.b(), F.c(), x), "STARK-wrapper proof must verify in Solidity");
    }

    function test_settlesWithStarkVerifiedInside() public {
        uint256 g = gasleft();
        _settle(F.NEW_ROOT, F.VUMT_ROOT, F.a(), F.b(), F.c());
        emit log_named_uint("verifyAndSettleBatchV2 gas, STARK-wrapper circuit", g - gasleft());
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
        SSRapSettlementVerifierV2 twin = new SSRapSettlementVerifierV2(F.OLD_ROOT, AGG, IGroth16Verifier(address(groth16)));
        vm.blobhashes(blobSet);
        vm.prank(AGG);
        vm.expectRevert(SSRapSettlementVerifierV2.InvalidGroth16Proof.selector);
        twin.verifyAndSettleBatchV2(F.OLD_ROOT, F.NEW_ROOT, F.VUMT_ROOT, F.BATCH, F.a(), F.b(), F.c());
    }
}
