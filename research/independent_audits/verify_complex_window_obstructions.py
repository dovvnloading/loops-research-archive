#!/usr/bin/env python3
"""Exact two-scale complex-window obstruction certificates.

Uses the 2^-224 outward interval engine in verify_real_nested_3_9.py.
No floating point, sampled orbits, nonlinear solvers, or unstated source geometry.
"""
from __future__ import annotations

from verify_real_nested_3_9 import (
    C_K, PREC, UNIT, ZERO, Interval, iterate,
    orbit_and_derivative, parameter,
)

RETURN_PERIOD = 27
PARAM_BITS = 26
TRAPPING_BITS = 13
STADIUM_LIMIT_BITS = 21


def ceil_div(n: int, d: int) -> int:
    assert d > 0
    return -(-n // d)


def center_orbit() -> list[Interval]:
    lower = parameter(C_K)
    upper = parameter(C_K + 1)
    assert iterate(ZERO, lower, RETURN_PERIOD)[-1].positive()
    assert iterate(ZERO, upper, RETURN_PERIOD)[-1].negative()
    enclosure = Interval(lower.lo, upper.hi)
    orbit, derivative = orbit_and_derivative(enclosure, RETURN_PERIOD)
    assert derivative[-1].negative(), "the period-27 root must be unique"
    assert orbit[RETURN_PERIOD].lo < 0 < orbit[RETURN_PERIOD].hi
    return orbit


def uniform_error_bounds(orbit: list[Interval]) -> list[int]:
    """Outward dyadic bounds on |f_c'^j(z)-f_c*^j(0)| for |z|<=2^-13.

    c* is the unique period-27 root in the certified dyadic bracket;
    |c'-c*| < 2^-26. If E_j bounds the error and M_j bounds
    |f_c*^j(0)|, the exact complex identity gives
    E_(j+1) <= E_j(2*M_j+E_j)+2^-26.
    """
    radius = UNIT >> TRAPPING_BITS
    param_radius = UNIT >> PARAM_BITS
    errors = [radius]
    for j in range(RETURN_PERIOD):
        center_abs = max(abs(orbit[j].lo), abs(orbit[j].hi))
        assert center_abs < 2 * UNIT
        prev = errors[-1]
        next_error = ceil_div(prev * (2 * center_abs + prev), UNIT) + param_radius
        errors.append(next_error)
    return errors


def check() -> None:
    X = center_orbit()
    E = uniform_error_bounds(X)
    radius = UNIT >> TRAPPING_BITS
    half_radius = radius >> 1

    # F=f_c'^27 maps the whole closed disk |z|<=radius into the
    # strictly smaller disk |z|<3*radius/8. Cauchy's derivative bound
    # gives |F'|<3/4 on |z|<=radius/2, hence an attracting fixed point.
    assert 8 * E[-1] < 3 * radius, "uniform trapping disk failed"

    # That fixed point has exact f-period 27, not 1, 3 or 9:
    # |f_c'^j(a)-a| >= |x_j(c*)|-E_j-radius/2 > 0.
    for j in (1, 3, 9):
        threshold = E[j] + half_radius
        assert X[j].lo > threshold or X[j].hi < -threshold, (
            "lower-period exclusion failed", j
        )

    # Each c' in this open parameter disk thus has an attracting
    # period-27 orbit that captures the critical point 0. The disk
    # |z|<radius/2 has bounded forward orbits: K(f_c') has interior,
    # so Paper 2's H3, K(f)=J(f), fails throughout this parameter disk.

    # The obvious equal-thickness stadium U_p(epsilon)=N_epsilon(I_p)
    # also fails as the base of a quadratic-like first-return component.
    # At the center, x3 and x9 are boundary points of I3 and I9,
    # respectively, and x6<x9<0<x18<x3.
    assert X[6].hi < X[9].lo
    assert X[9].hi < 0 < X[18].lo
    assert X[18].hi < X[3].lo
    assert all(max(abs(v.lo), abs(v.hi)) < 2 * UNIT for v in X[:9])

    # For any 0<epsilon<=2^-21, the segment {it: 0<=t<=2epsilon}
    # maps under f_c*^p into U_p(epsilon), p=3,9. Its endpoint lies
    # outside U_p(epsilon). The preimage component containing 0
    # therefore cannot be contained in the same U_p(epsilon).
    # The bound is 4*5^(p-1)*epsilon^2 <= 4*5^8*epsilon^2 < epsilon.
    assert 4 * 5**8 < 2**STADIUM_LIMIT_BITS

    print("PASS: exact complex two-scale first-failure certificates")
    print("  center: unique period-27 root in the source 2^-128 bracket")
    print("  complex parameters: |c'-c*| < 2^-26")
    print("  all |z|<=2^-13 satisfy |f_c'^27(z)| < (3/8)*2^-13")
    print("  f_c'^27 is <3/4-Lipschitz on |z|<=2^-14")
    print("  attracting orbit has exact f-period 27, critical orbit captured")
    print("  entire parameter disk violates Paper 2 H3: K(f)=J(f)")
    print("  for p=3,9 and 0<epsilon<=2^-21, thin stadium full preimage")
    print("  component at 0 is NOT contained in its target stadium")
    print("LIMIT: no proper quadratic-like restriction, complex KL atlas,")
    print("       global H1/H2/H3/H4 closure, or MLC proof asserted")


if __name__ == "__main__":
    check()
