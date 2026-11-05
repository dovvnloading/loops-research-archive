#!/usr/bin/env python3
"""Finite Fourier-mode checks of the exact rectangular trace response.

Checks the *finite rectangle* identity and relative error bound only.
No test here proves a dynamical realization of a physical puzzle collar.
Requires NumPy.
Run: python research/independent_audits/verify_rectangle_response.py
"""
from __future__ import annotations

import math
import numpy as np


def dtn(length: float, frequency: float) -> np.ndarray:
    """Two-end Dirichlet-to-Neumann matrix for one Neumann Fourier mode."""
    if length <= 0:
        raise ValueError("length must be positive")
    if frequency == 0:
        return np.array([[1, -1], [-1, 1]], dtype=float) / length
    t = frequency * length
    return frequency * np.array([
        [1 / math.tanh(t), -1 / math.sinh(t)],
        [-1 / math.sinh(t), 1 / math.tanh(t)],
    ])


def glue(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    """Minimize over the common complete interior trace (Schur complement)."""
    total = np.zeros((3, 3), dtype=float)
    total[:2, :2] += left
    total[1:, 1:] += right
    external = total[np.ix_([0, 2], [0, 2])]
    cross = total[np.ix_([0, 2], [1])]
    return external - (cross @ cross.T) / total[1, 1]


def main() -> None:
    n_gluing = 0
    n_relative = 0
    for R, S in ((0.4, 0.9), (0.7, 2.1), (1.5, 1.2), (2.5, 1.5)):
        for k in range(9):
            omega = math.pi * k
            actual = glue(dtn(R, omega), dtn(S, omega))
            expected = dtn(R + S, omega)
            assert np.allclose(actual, expected, rtol=1e-12, atol=1e-12)
            n_gluing += 1

        eta = 2 / math.expm1(math.pi * R)
        if eta < 1:
            for k in range(1, 10):
                omega = math.pi * k
                reference = omega * np.eye(2)
                exact = dtn(R, omega)
                eigenvalues = np.linalg.eigvalsh(exact - reference)
                assert max(abs(eigenvalues)) <= eta * omega * (1 + 1e-12)
                assert np.linalg.eigvalsh((1 + eta) * reference - exact).min() >= -1e-12
                assert np.linalg.eigvalsh(exact - (1 - eta) * reference).min() >= -1e-12
                n_relative += 1

    print(f"PASS: {n_gluing} gluing identities and {n_relative} relative-bound checks")
    print("Interpretation: finite spectral rectangle only, not dynamic realization")


if __name__ == "__main__":
    main()
