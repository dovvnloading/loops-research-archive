#!/usr/bin/env python3
"""Independent finite-matrix checks for delayed cross-section cloning.

Requires NumPy. Does not certify the analytic results of a source paper.
Run: python research/independent_audits/verify_clone_spectral.py
"""
from __future__ import annotations

import math
import numpy as np


def clone_matrix(Q: np.ndarray, C: np.ndarray, D: np.ndarray, n: int) -> np.ndarray:
    """Row-source adjacency for A plus the E_0 -> ... -> E_n chain."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    a, e = Q.shape[0], D.shape[0]
    assert Q.shape == (a, a) and C.shape == (a, e) and D.shape == (e, a)
    M = np.zeros((a + (n + 1) * e, a + (n + 1) * e), dtype=float)
    M[:a, :a] = Q
    M[:a, a:a + e] = C
    for k in range(n):
        M[a + k * e:a + (k + 1) * e,
          a + (k + 1) * e:a + (k + 2) * e] = np.eye(e)
    M[a + n * e:a + (n + 1) * e, :a] = D
    return M


def returns(Q: np.ndarray, C: np.ndarray, D: np.ndarray) -> dict[int, np.ndarray]:
    """R_k = D Q^(k-2) C; assert nilpotence rather than silently truncate."""
    a = Q.shape[0]
    power = np.eye(a)
    out = {}
    for j in range(a):
        Rj = D @ power @ C
        if np.any(Rj != 0):
            out[j + 2] = Rj
        power = power @ Q
    if not np.array_equal(power, np.zeros_like(power)):
        raise AssertionError("Q is not nilpotent: no finite cross section")
    if not out:
        raise AssertionError("No return paths")
    return out


def spectral_radius(M: np.ndarray) -> float:
    return float(np.max(np.abs(np.linalg.eigvals(M))))


def first_return_root(ret: dict[int, np.ndarray], t: float) -> float:
    H = sum((t ** (-k) * Rk for k, Rk in ret.items()))
    return spectral_radius(H)


def solve_lambda(ret: dict[int, np.ndarray], n: int) -> float:
    """Independent bisection for rho(H(lambda)) = lambda**n."""
    lo, hi = 1.0, 2.0
    while math.log(first_return_root(ret, hi)) > n * math.log(hi):
        hi *= 1.5
    for _ in range(100):
        mid = (lo + hi) / 2
        if math.log(first_return_root(ret, mid)) > n * math.log(mid):
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def weighted_return_mean(ret: dict[int, np.ndarray]) -> float:
    R = sum(ret.values())
    er, right = np.linalg.eig(R)
    ir = int(np.argmax(er.real))
    r = right[:, ir].real
    el, left = np.linalg.eig(R.T)
    il = int(np.argmax(el.real))
    l = left[:, il].real
    M = sum(k * Rk for k, Rk in ret.items())
    return float(l @ M @ r / (spectral_radius(R) * (l @ r)))


def test(name: str, Q: np.ndarray, C: np.ndarray, D: np.ndarray) -> None:
    ret = returns(Q, C, D)
    R = sum(ret.values())
    rho = spectral_radius(R)
    kmin, kmax = min(ret), max(ret)
    assert rho > 1, name
    print(f"CASE {name}: return lengths {list(ret)}, rho(R)={rho:.12f}")
    for n in (0, 1, 2, 4, 8, 16):
        direct = spectral_radius(clone_matrix(Q, C, D, n))
        reduced = solve_lambda(ret, n)
        assert abs(direct - reduced) < 2e-11, (name, n, direct, reduced)
        lo = rho ** (1 / (n + kmax))
        hi = rho ** (1 / (n + kmin))
        assert lo - 2e-12 <= direct <= hi + 2e-12, (name, n, lo, direct, hi)
        print(f"  n={n:2d}: direct={direct:.12f} reduced={reduced:.12f}"
              f" bracket=[{lo:.12f}, {hi:.12f}]")
    mu = weighted_return_mean(ret)
    L = math.log(rho)
    n = 1000
    direct = solve_lambda(ret, n)
    second = 1 + L / n + (L * L / 2 - mu * L) / n**2
    err = abs(direct - second)
    print(f"  weighted mean={mu:.12f}; second-order error at n=1000: {err:.3e}")
    assert err < 1e-7
    print("  PASS")


def main() -> None:
    Q = np.array([[0, 1], [0, 0]], dtype=float)
    C = np.array([[1], [1]], dtype=float)
    D = np.array([[1, 0]], dtype=float)
    test("one-gate e,a,b", Q, C, D)

    n = 4
    lam = spectral_radius(clone_matrix(Q, C, D, n))
    lhs = lam**n
    positive = lam**2 + lam**3
    negative = lam**(-2) + lam**(-3)
    print(f"  PRINTED WEIGHT CHECK n=4: lambda^n={lhs:.12f}, "
          f"positive={positive:.12f}, negative={negative:.12f}")
    assert abs(lhs - negative) < 1e-10
    assert abs(lhs - positive) > 0.1

    C = np.array([[1, 1], [1, 0]], dtype=float)
    D = np.array([[1, 1], [1, 0]], dtype=float)
    test("two-gate", Q, C, D)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
