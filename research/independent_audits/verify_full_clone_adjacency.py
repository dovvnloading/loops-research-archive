#!/usr/bin/env python3
"""Exact rational verification of full cloned-graph adjacency eigen residuals.

No floating point and no numerical eigenvalue routine are used.  For
each n and positive rational t, the vector is

    x[i] = t**i                   (0 <= i <= n)
           t**i / (t + 1)        (n < i < 2*n+5).

The actual graph has all clockwise edges i->i+1 (wrapping at the end)
plus one shortcut n->n+2.

All row residuals of A*x-t*x vanish identically except the final row.
The final residual multiplied by (t+1) is exactly

    (t+1) - t**(2*n+5).

Thus the entire finite matrix has this explicit eigenvector exactly at
a root of the clone polynomial. This regression is finite, independent
of Lean, and does not assert a general Perron spectral-radius theorem.
"""
from __future__ import annotations

from fractions import Fraction


def edge_targets(n: int, u: int) -> tuple[int, ...]:
    if n < 0:
        raise ValueError("n must be nonnegative")
    L = 2 * n + 5
    if not (0 <= u < L):
        raise IndexError("source vertex outside clone")
    if u == n:
        return n + 1, n + 2
    if u == L - 1:
        return (0,)
    return (u + 1,)


def full_vector(n: int, t: Fraction) -> list[Fraction]:
    if t <= 0 or t == -1:
        raise ValueError("test parameter must be positive")
    L = 2 * n + 5
    return [t**i if i <= n else t**i / (t + 1) for i in range(L)]


def exact_check(n: int, t: Fraction) -> None:
    L = 2 * n + 5
    v = full_vector(n, t)
    assert v[0] == 1
    assert all(x > 0 for x in v)

    for u in range(L):
        targets = edge_targets(n, u)
        # The adjacency is 0/1 and has no parallel edge occurrences.
        assert len(targets) == len(set(targets))
        assert all(0 <= w < L for w in targets)
        residual = sum((v[w] for w in targets), Fraction(0)) - t * v[u]
        if u < L - 1:
            assert residual == 0, (n, t, u, residual)
        else:
            assert (t + 1) * residual == (t + 1) - t**L, (n, t)


def main() -> None:
    parameters = [
        Fraction(1, 2), Fraction(3, 4), Fraction(1),
        Fraction(5, 4), Fraction(3, 2), Fraction(2),
        Fraction(5, 2), Fraction(3),
    ]
    tested = 0
    for n in range(66):
        for t in parameters:
            exact_check(n, t)
            tested += 1
    print(f"PASS: {tested} rational graph/eigenvector residual identities")
    print("All non-wrap rows vanish; wrap residual equals the clone polynomial")
    print("Full adjacency matrix has its positive eigenvector at every positive root")


if __name__ == "__main__":
    main()
