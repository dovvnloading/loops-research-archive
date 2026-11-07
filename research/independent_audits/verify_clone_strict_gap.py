#!/usr/bin/env python3
"""Independent exact modular determinant tests for the full cloned graph.

The Lean theorem proves that every full-graph eigenvalue satisfies
z^(2n+5) = z+1. Here we independently check, over finite fields,
that det(z*I-A) = z^(2n+5)-z-1 for multiple delays and scalar inputs.

Finite tests do NOT prove the characteristic-polynomial identity for
all n. The all-n characteristic-root statement is Lean-checked; the
determinant identity has a separate written cycle-cover proof.
"""

from __future__ import annotations

from math import isclose

PRIMES = (1000003, 1000033)
DELAYS = (0, 1, 2, 3, 5, 8, 12, 20, 30)
PARAMETERS = (-5, -2, -1, 0, 1, 2, 4, 7)


def full_adjacency(n: int) -> list[list[int]]:
    m = 2 * n + 5
    out = [[0] * m for _ in range(m)]
    for u in range(m):
        out[u][(u + 1) % m] = 1
    out[n][n + 2] = 1
    return out


def det_mod(matrix: list[list[int]], p: int) -> int:
    """Exact Gaussian elimination in F_p; independent of eigensolvers."""
    a = [[v % p for v in row] for row in matrix]
    m = len(a)
    result = 1
    for j in range(m):
        pivot_row = next((i for i in range(j, m) if a[i][j]), None)
        if pivot_row is None:
            return 0
        if pivot_row != j:
            a[j], a[pivot_row] = a[pivot_row], a[j]
            result = -result
        pivot = a[j][j]
        result = (result * pivot) % p
        inv = pow(pivot, -1, p)
        for i in range(j + 1, m):
            if a[i][j]:
                factor = a[i][j] * inv % p
                for k in range(j + 1, m):
                    a[i][k] = (a[i][k] - factor * a[j][k]) % p
                a[i][j] = 0
    return result % p


def check_exact_determinants() -> int:
    tests = 0
    for n in DELAYS:
        graph = full_adjacency(n)
        m = len(graph)
        assert m == 2 * n + 5
        assert all(sum(row) == (2 if u == n else 1)
                   for u, row in enumerate(graph))
        for lam in PARAMETERS:
            mat = [[(lam if i == j else 0) - graph[i][j]
                    for j in range(m)] for i in range(m)]
            for prime in PRIMES:
                lhs = det_mod(mat, prime)
                rhs = (pow(lam % prime, m, prime) - lam - 1) % prime
                assert lhs == rhs, (n, lam, prime, lhs, rhs)
                tests += 1
    return tests


def check_numerical_gap() -> list[dict[str, float]]:
    """Supplementary diagnostics, not part of any kernel-proof claim."""
    import numpy as np

    result = []
    for n in (0, 1, 2, 4, 10, 20):
        m = 2 * n + 5
        A = np.asarray(full_adjacency(n), dtype=float)
        roots = np.linalg.eigvals(A)
        real_roots = [r.real for r in roots
                      if abs(r.imag) < 1e-8 and r.real > 1]
        assert len(real_roots) == 1, (n, real_roots)
        t = real_roots[0]
        others = [abs(r) for r in roots if abs(r - t) > 1e-7]
        second = max(others)
        assert second < t - 1e-8, (n, t, second)
        assert t ** m - t - 1 < 1e-5
        assert (m - 1) * (t - 1) <= 1 + 1e-8
        result.append({"n": n, "degree": m, "root": float(t),
                       "other_max": float(second),
                       "gap": float(t - second)})
    return result


def main() -> None:
    count = check_exact_determinants()
    print(f"Passed {count} exact finite-field determinant checks")
    try:
        gaps = check_numerical_gap()
    except ImportError:
        print("NumPy unavailable: skipped supplemental spectral diagnostics")
        return
    for row in gaps:
        print("n={n:2.0f} degree={degree:3.0f} root={root:.9f} "
              "second={other_max:.9f} gap={gap:.9g}".format(**row))


if __name__ == "__main__":
    main()
