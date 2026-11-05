#!/usr/bin/env python3
"""Independent numerical checks for the full cloned adjacency spectral radius.

The Lean proof of the nonnegative eigenvalue modulus bound is the actual
universal result. This separate regression uses NumPy diagonalization of
finite full graph matrices and a bisection solve of t^(2n+5)=t+1.

No numerical checks are reported as an MLC proof or as an analytic
Perron-Frobenius theorem.
"""
from __future__ import annotations

import numpy as np


def clone_adjacency(n: int) -> np.ndarray:
    L = 2 * n + 5
    a = np.zeros((L, L), dtype=float)
    for i in range(L):
        a[i, (i + 1) % L] = 1.0
    a[n, n + 2] = 1.0
    return a


def positive_clone_root(n: int) -> float:
    L = 2 * n + 5
    low, high = 1.0, 2.0
    for _ in range(110):
        mid = (low + high) / 2
        if mid**L > mid + 1:
            high = mid
        else:
            low = mid
    return (low + high) / 2


def clone_vector(n: int, t: float) -> np.ndarray:
    L = 2 * n + 5
    return np.array([
        t**i if i <= n else t**i / (t + 1)
        for i in range(L)
    ])


def main() -> None:
    checked = 0
    for n in range(34):
        mat = clone_adjacency(n)
        root = positive_clone_root(n)
        vec = clone_vector(n, root)
        residual = mat @ vec - root * vec
        assert np.all(vec > 0), n
        assert np.linalg.norm(residual, ord=np.inf) < 2e-12, (n, residual)
        eigenvalues = np.linalg.eigvals(mat)
        rho = float(max(abs(eigenvalues)))
        assert abs(rho - root) < 4e-9, (n, root, rho)
        assert any(abs(eigenvalues - root) < 4e-9), (n, root)
        checked += 1
        if n in (0, 1, 2, 4, 8, 16, 32):
            print(f"n={n:2d}: root={root:.12f}, rho(A)={rho:.12f}")

    print(f"PASS: {checked} complete cloned graph eigenspectra and positive eigenpairs")
    print("Universal dominance proof belongs to SpectralDominance.lean")


if __name__ == "__main__":
    main()
