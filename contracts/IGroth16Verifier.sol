// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice Groth16 verifier over BN254 with exactly one public input.
interface IGroth16Verifier {
    /// @param a Proof point A in G1 (x, y).
    /// @param b Proof point B in G2: b[0] = [x_real, x_imag], b[1] = [y_real, y_imag].
    /// @param c Proof point C in G1 (x, y).
    /// @param publicInput The batch public input, already reduced mod r.
    /// @return True iff the pairing check passes and every coordinate is canonical.
    function verifyProof(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256 publicInput
    ) external view returns (bool);
}
