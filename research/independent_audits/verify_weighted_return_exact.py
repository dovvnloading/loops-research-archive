#!/usr/bin/env python3
"""Exact rational regression of the two-gate negative-power return reduction.

For each rational t>0, the candidate vector (t^(n+2), 1) makes the
second eigen-equation an identity. Multiplying the first equation's
residual by t^3 gives (t+1)-t^(2*n+5) exactly.

This uses fractions.Fraction (no tolerance, no floating eigenvalues).
It is a finite diagnostic; the all-n Real theorem is in Lean.
"""
from __future__ import annotations

from fractions import Fraction


def weighted_return(t: Fraction, e: Fraction, f: Fraction):
    a = t**(-2) + t**(-3)
    b = t**(-2)
    return a * f, b * e


def test_exact() -> None:
    cases = (Fraction(1, 2), Fraction(2, 3), Fraction(1),
             Fraction(5, 4), Fraction(3, 2), Fraction(2),
             Fraction(5))
    checks = 0
    for n in range(51):
        for t in cases:
            e, f = t ** (n + 2), Fraction(1)
            left_e, left_f = weighted_return(t, e, f)
            right_e, right_f = t ** n * e, t ** n * f
            assert left_f == right_f, (n, t, left_f, right_f)
            assert (left_e - right_e) * t**3 == t + 1 - t**(2 * n + 5)
            checks += 1
    # Demonstrate the sign issue numerically without using it as proof.
    t = Fraction(2)
    correct = t**(-2) + t**(-3)
    incorrect = t**2 + t**3
    assert correct != incorrect
    print(f"PASS: {checks} exact negative-power/cleared-polynomial identities")
    print("Status: finite rational regression; universal Real equivalence is Lean-checked")


if __name__ == "__main__":
    test_exact()
