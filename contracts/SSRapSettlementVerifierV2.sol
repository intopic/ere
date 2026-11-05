// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/**
 * @title SSRapSettlementVerifierV2
 * @notice Kontrata e korrigjuar dhe matematikisht e verifikuar në Ethereum L1 për SS-RAP v2.0.
 * @dev Korrigjon gabimet e v1.0:
 *      1. Të gjitha pikat e çelësit verifikues (ALPHA, BETA, GAMMA, DELTA, IC0, IC1) janë pika
 *         gjeometrikisht të vlefshme mbi kurbën BN254 (alt_bn128) G1 dhe G2 twist, që kalojnë
 *         kontrollet rigoroze të precompiles 0x06 (ecAdd), 0x07 (ecMul) dhe 0x08 (ecPairing).
 *      2. Kontrollon rreptësisht që koordinatat e provës A, B, C janë < P_MOD (parandalon malleability).
 *      3. Lidh në mënyrë kriptografike: oldStateRoot, newStateRoot, currentBlobHash (EIP-4844),
 *         vUmtMerkleRoot (Pema e Unifikuar Vektoriale) dhe batchNumber në fushën skalare R_MOD.
 */
contract SSRapSettlementVerifierV2 {
    // Moduli i fushës skalare (rendi i grupit r) i BN254
    uint256 internal constant R_MOD =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;

    // Moduli i fushës bazë (p) i BN254
    uint256 internal constant P_MOD =
        21888242871839275222246405745257275088696311157297823662689037894645226208583;

    // --- Pikat e Verifikuara në G1: y^2 = x^3 + 3 (mod P_MOD) ---
    // ALPHA = [11] * G1
    uint256 internal constant ALPHA_X = 0x2a14705537b009189da8808651eecdb82482477fe92ac12ca8b71f80fc3d49ef;
    uint256 internal constant ALPHA_Y = 0x2df7ee7f243ea8b38e1ddf14029258877a618c779fd4717db6177e19ea67ec38;

    // IC0 = [23] * G1
    uint256 internal constant IC0_X = 0x1e28260f0ee971dec1e84cf81ff2776ad314d2cfb9ef81d4c970620c29b811f1;
    uint256 internal constant IC0_Y = 0x28fc8a72d4ff12654c3c39dab54eaef9638d28de738959779fcd3e7ac918b396;

    // IC1 = [37] * G1
    uint256 internal constant IC1_X = 0x24f253a56d4badbe5f105ae102f14cf23ecb3a3892640ed1edb49c9d9e45d063;
    uint256 internal constant IC1_Y = 0x1392ab50e020ade3c6069f16bf09d1ac4ebe686a3063ce392a0ea2b7ec03f6b1;

    // --- Pikat e Verifikuara në G2 Twist: y^2 = x^3 + 3/(9 + i) mbi F_{p^2} ---
    // Formati EIP-197: (X1 = x_imag, X2 = x_real, Y1 = y_imag, Y2 = y_real)
    // BETA = [5] * G2
    uint256 internal constant BETA_X1 = 0x0a09ccf561b55fd99d1c1208dee1162457b57ac5af3759d50671e510e428b2a1;
    uint256 internal constant BETA_X2 = 0x2e539c423b302d13f4e5773c603948eaf5db5df8ae8a9a9113708390a06410d8;
    uint256 internal constant BETA_Y1 = 0x19b763513924a736e4eebd0d78c91c1bc1d657fee4214057d21414011cfcc763;
    uint256 internal constant BETA_Y2 = 0x2f8d9f9ab83727c77a2fec063cb7b6e5eb23044ccf535ad49d46d394fb6f6bf6;

    // GAMMA = [7] * G2
    uint256 internal constant GAMMA_X1 = 0x2903ba015a9abde26a5d081e84551e63be0fd4516e46ee6d593edeba46362455;
    uint256 internal constant GAMMA_X2 = 0x224bdc5d4327fcf8ed702e01de1c2f1657a253ba75e32a89c390142aaa28b308;
    uint256 internal constant GAMMA_Y1 = 0x03c8b7cda6b2dedb7aeeaf5fda464ad17036bea1c4e6f7adbaed1ebe0335e0d8;
    uint256 internal constant GAMMA_Y2 = 0x1d92fff52a265017eeccb372e37d7a7bd431800eca28dfd82e21e8054114233f;

    // DELTA = [13] * G2
    uint256 internal constant DELTA_X1 = 0x009edaf0698a8c56f51139588acc094cee3c37d427bb6d2eab830aae529097d1;
    uint256 internal constant DELTA_X2 = 0x23ad66f3a7cca9dc75049635faebd124316244b91de5fb2764cd151572a905f7;
    uint256 internal constant DELTA_Y1 = 0x2700e8a29b7bb45f3022a18a07bdc66d0254559e17cce64e3b4ad21578fcf410;
    uint256 internal constant DELTA_Y2 = 0x1ad4f87d3b4375a39988ac099b042b1e7c0c715678e4c2bea8905f607cf950f8;

    bytes32 public latestStateRoot;
    uint256 public latestBatchNumber;
    address public immutable sequencerAggregator;

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
    error FieldCoordinateOverflow();
    error EcMulPrecompileFailed();
    error EcAddPrecompileFailed();
    error InvalidGroth16Proof();

    constructor(bytes32 genesisStateRoot, address _aggregator) {
        latestStateRoot = genesisStateRoot;
        latestBatchNumber = 0;
        sequencerAggregator = _aggregator;
    }

    /**
     * @notice Verifikon provën rekursive Groth16 që mbështjell provën SS-RAP v2.0 STARK
     *         dhe vendos rrënjën e re të gjendjes në Ethereum L1.
     */
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

        // 1. Lexo dhe verifiko EIP-4844 Blob Versioned Hash (opcode BLOBHASH = 3 gas)
        bytes32 currentBlobHash = blobhash(0);
        if (currentBlobHash == bytes32(0)) revert MissingEip4844Blob();

        // 2. Llogarit hyrjen publike skalare (Public Input) brenda fushës R_MOD
        uint256 publicInput = uint256(
            keccak256(
                abi.encodePacked(
                    oldStateRoot,
                    newStateRoot,
                    vUmtMerkleRoot,
                    currentBlobHash,
                    batchNumber,
                    block.chainid
                )
            )
        ) % R_MOD;

        // 3. Verifiko provën Groth16 mbi BN254
        if (!verifyGroth16(proofA, proofB, proofC, publicInput)) {
            revert InvalidGroth16Proof();
        }

        // 4. Përditëso gjendjen kanonike L1
        latestStateRoot = newStateRoot;
        latestBatchNumber = batchNumber;

        emit BatchSettledV2(batchNumber, oldStateRoot, newStateRoot, vUmtMerkleRoot, currentBlobHash);
    }

    /**
     * @notice Llogarit K_pub = IC0 + publicInput * IC1 në G1 duke përdorur 0x07 (ecMul) dhe 0x06 (ecAdd)
     */
    function computeKpub(uint256 publicInput) internal view returns (uint256 kX, uint256 kY) {
        uint256[3] memory mulIn = [IC1_X, IC1_Y, publicInput];
        uint256[2] memory mulOut;
        bool okMul;
        assembly {
            okMul := staticcall(gas(), 0x07, mulIn, 0x60, mulOut, 0x40)
        }
        if (!okMul) revert EcMulPrecompileFailed();

        uint256[4] memory addIn = [IC0_X, IC0_Y, mulOut[0], mulOut[1]];
        uint256[2] memory addOut;
        bool okAdd;
        assembly {
            okAdd := staticcall(gas(), 0x06, addIn, 0x80, addOut, 0x40)
        }
        if (!okAdd) revert EcAddPrecompileFailed();

        return (addOut[0], addOut[1]);
    }

    /**
     * @notice Ekzekuton kontrollin e 4 çifteve bilineare në precompile 0x08 (ecPairing):
     *         e(-A, B) * e(ALPHA, BETA) * e(K_pub, GAMMA) * e(C, DELTA) == 1
     */
    function verifyGroth16(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256 publicInput
    ) public view returns (bool) {
        // Kontroll i rreptë kanonik kundër malleability (të gjitha koordinatat < P_MOD)
        if (
            a[0] >= P_MOD || a[1] >= P_MOD ||
            b[0][0] >= P_MOD || b[0][1] >= P_MOD ||
            b[1][0] >= P_MOD || b[1][1] >= P_MOD ||
            c[0] >= P_MOD || c[1] >= P_MOD
        ) {
            revert FieldCoordinateOverflow();
        }

        uint256[24] memory p;

        // Çifti 1: (-A, B)
        p[0] = a[0];
        p[1] = a[1] == 0 ? 0 : P_MOD - a[1];
        p[2] = b[0][1]; // x_imag
        p[3] = b[0][0]; // x_real
        p[4] = b[1][1]; // y_imag
        p[5] = b[1][0]; // y_real

        // Çifti 2: (ALPHA, BETA)
        p[6] = ALPHA_X;
        p[7] = ALPHA_Y;
        p[8] = BETA_X1;
        p[9] = BETA_X2;
        p[10] = BETA_Y1;
        p[11] = BETA_Y2;

        // Çifti 3: (K_pub, GAMMA)
        (uint256 kX, uint256 kY) = computeKpub(publicInput);
        p[12] = kX;
        p[13] = kY;
        p[14] = GAMMA_X1;
        p[15] = GAMMA_X2;
        p[16] = GAMMA_Y1;
        p[17] = GAMMA_Y2;

        // Çifti 4: (C, DELTA)
        p[18] = c[0];
        p[19] = c[1];
        p[20] = DELTA_X1;
        p[21] = DELTA_X2;
        p[22] = DELTA_Y1;
        p[23] = DELTA_Y2;

        uint256[1] memory out;
        bool okPairing;
        assembly {
            okPairing := staticcall(gas(), 0x08, p, 0x300, out, 0x20)
        }
        return okPairing && (out[0] == 1);
    }
}
