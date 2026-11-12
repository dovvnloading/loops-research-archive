#!/usr/bin/env python3
"""Exact finite arithmetic for a boundary-spectrum MLC research direction.

This program does NOT test the infinite Cauchy condition and does NOT prove MLC.
The initial Laurent coefficients are published data (Ewing--Schober; see
https://mathworld.wolfram.com/MandelbrotSet.html), not newly computed here.
"""

from fractions import Fraction as Q
import json

# Psi(w) = w + b0 + sum_{n>=1} b_n w^(-n), |w| > 1.
# Only the first five positive-degree Laurent coefficients are used.
B = {1: Q(1, 8), 2: Q(-1, 4), 3: Q(15, 128), 4: Q(0), 5: Q(-47, 1024)}


def weighted_fejer(N):
    """Rational coefficients of the Fejer mean, omitting the continuous w+b0."""
    if N < 1 or N > 5:
        raise ValueError("only 1 <= N <= 5 has authenticated data")
    return {n: B[n] * Q(N + 1 - n, N + 1) for n in range(1, N + 1)}


def squared_energy(N=5):
    """Exact finite partial sum sum(n*b_n^2)."""
    return sum((n * B[n] * B[n] for n in range(1, N + 1)), Q(0))


def residual_area_budget(N=5):
    """Rigorous bound from the elementary disk |c|<=1/4 contained in M."""
    return Q(15, 16) - squared_energy(N)


def outer_tail_bound_squared(N, R):
    """Exact rational upper bound for |Psi(w)-P_N(w)|^2, |w|>=R.

    By Gronwall's area theorem, sum_{n>N} n|b_n|^2 <= E_N.
    Cauchy--Schwarz and 1/n <= 1/(N+1) for n>N give the
    purely rational estimate E_N*q^(N+1)/((N+1)*(1-q)), q=R^-2.
    """
    R = Q(R)
    if R <= 1:
        raise ValueError("R must be > 1")
    q = 1 / (R * R)
    return residual_area_budget(N) * q ** (N + 1) / ((N + 1) * (1 - q))


def exact_fejer_1_to_2_norm():
    """Exact sup on the unit circle for sigma_2-sigma_1."""
    first = weighted_fejer(1)
    second = weighted_fejer(2)
    a = second[1] - first[1]
    b = second[2]
    # |a z^-1+b z^-2|=|a+b z^-1|; z^-1 runs over the unit circle.
    return abs(a) + abs(b)


def check():
    assert weighted_fejer(1) == {1: Q(1, 16)}
    assert weighted_fejer(2) == {1: Q(1, 12), 2: Q(-1, 12)}
    assert exact_fejer_1_to_2_norm() == Q(5, 48)
    assert squared_energy(5) == Q(201701, 1048576)
    assert residual_area_budget(5) == Q(781339, 1048576)
    assert residual_area_budget(5) > 0
    assert outer_tail_bound_squared(5, Q(2)) == Q(781339, 19327352832)
    # Adding known coefficients can only decrease the residual area budget.
    assert all(residual_area_budget(n + 1) <= residual_area_budget(n) for n in range(1, 5))


def manifest():
    radii = [Q(5, 4), Q(3, 2), Q(2)]
    return {
        "scope": "finite rational checks, not an MLC proof or a convergence test",
        "provenance": "Ewing-Schober Laurent coefficients as reproduced by MathWorld",
        "coefficients": {str(i): str(B[i]) for i in B},
        "fejer_1_2_uniform_difference": str(exact_fejer_1_to_2_norm()),
        "known_area_energy_S5": str(squared_energy()),
        "rigorous_unknown_energy_upper_bound": str(residual_area_budget()),
        "disk_inside_M_radius": "1/4",
        "outer_Laurent_squared_error_upper_bounds": {
            str(R): str(outer_tail_bound_squared(5, R)) for R in radii
        },
    }


if __name__ == "__main__":
    check()
    print(json.dumps(manifest(), indent=2, sort_keys=True))
