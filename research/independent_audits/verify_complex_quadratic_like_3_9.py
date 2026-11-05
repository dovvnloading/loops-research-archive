#!/usr/bin/env python3
"""Exact certificate for nested COMPLEX quadratic-like periods 3 and 9.

At the unique real root c* of f_c^27(0)=0 in the archived dyadic
bracket, and uniformly for |c-c*|<2^-32, certify explicit disk targets:

  U3 = D(0, 1/4), U9 = D(0, 1/32).

The preimage components of f_c^3 and f_c^9 containing zero are
compactly contained proper degree-two quadratic-like domains.
The inner component is inside D(0, 13/512), all pre-return phase
images at both levels are disjoint, and the actual inner phase cells
refine the three outer phase cells. The critical point is nonescaping
in both restrictions.

The arithmetic is exact, using outward 2^-224 signed-integer
enclosures. The analytic theorems (Rouche, Riemann-Hurwitz and
connectivity of quadratic-like Julia sets) are written explicitly in
the companion research note and are NOT kernel-checked by this script.

No KL puzzle rays, prime ends, sheets, Paper 2 H3 or MLC is proved.
"""
from __future__ import annotations

from dataclasses import dataclass

from verify_real_nested_3_9 import (
    C_K, PREC, UNIT, ZERO, ONE, Interval,
    parameter, iterate, orbit_and_derivative,
)

OUTER = UNIT // 4
INNER = UNIT // 32
INNER_SHRINK = 13 * UNIT // 512
PARAMETER_RADIUS = UNIT // (2**32)
CRITICAL_TRAP = UNIT // (2**13)
CENTER_PERIOD = 27


def ceil_div(n: int, den: int = UNIT) -> int:
    assert n >= 0 and den > 0
    return -(-n // den)


def abs_upper(x: Interval) -> int:
    return max(abs(x.lo), abs(x.hi))


def abs_lower(x: Interval) -> int:
    if x.lo > 0:
        return x.lo
    if x.hi < 0:
        return -x.hi
    return 0


def interval_gap(a: Interval, b: Interval) -> int:
    """Exact lower bound on distance of two real interval enclosures."""
    return max(0, a.lo - b.hi, b.lo - a.hi)


def center_and_coefficients() -> tuple[list[Interval], list[Interval]]:
    lo = parameter(C_K)
    hi = parameter(C_K + 1)
    assert iterate(ZERO, lo, CENTER_PERIOD)[-1].positive()
    assert iterate(ZERO, hi, CENTER_PERIOD)[-1].negative()
    center = Interval(lo.lo, hi.hi)
    x, derivative = orbit_and_derivative(center, CENTER_PERIOD)
    assert derivative[CENTER_PERIOD].negative()
    assert x[CENTER_PERIOD].lo < 0 < x[CENTER_PERIOD].hi
    for j in (1, 3, 9, 18):
        assert abs_lower(x[j]) > 0, ("critical period", j)

    # Write f_c*^j(z) = x_j + a_j z^2 + O(z^4).
    # a_1=1, a_(j+1)=2*x_j*a_j; coefficients vary with c*
    # but each a_j lies in the enclosure A[j].
    a = [ZERO, ONE]
    for j in range(1, 9):
        a.append(x[j] * a[j].times(2))
    assert all(abs_lower(a[j]) > 0 for j in range(1, 10))
    return x, a


@dataclass(frozen=True)
class Bounds:
    radius: int
    deviation: list[int]
    tail: list[int]
    leading: list[int]


def evaluate_bounds(
    x: list[Interval], a: list[Interval], radius: int, horizon: int
) -> Bounds:
    """For |z|<=radius bound F_j=x_j+a_j*z^2+H_j.

    H_1=0 and
    H_(j+1) <= 2|x_j| H_j + (|a_j| radius^2 + H_j)^2.
    All products/roundings are outward (upward) in integer units.
    """
    assert radius * radius % UNIT == 0
    radius_sq = radius * radius // UNIT
    tail = [0] * (horizon + 1)
    dev = [0] * (horizon + 1)
    lead = [0] * (horizon + 1)
    dev[0] = radius
    for j in range(1, horizon + 1):
        az2_up = ceil_div(abs_upper(a[j]) * radius_sq)
        dev[j] = az2_up + tail[j]
        lead[j] = abs_lower(a[j]) * radius_sq // UNIT
        if j < horizon:
            tail[j + 1] = (
                ceil_div(2 * abs_upper(x[j]) * tail[j])
                + ceil_div(dev[j] * dev[j])
            )
    return Bounds(radius, dev, tail, lead)


def rouche_margin(
    x: list[Interval], bounds: Bounds, period: int, target: int
) -> int:
    """Lower bound: |a_p|r^2 - |x_p| - H_p - target."""
    return (
        bounds.leading[period]
        - abs_upper(x[period])
        - bounds.tail[period]
        - target
    )


def small_decimal_lower(value: int) -> str:
    """Display only: truncate a nonnegative exact lower bound to 6 places."""
    assert value > 0
    n = value * 1_000_000 // UNIT
    return f"{n // 1_000_000}.{n % 1_000_000:06d}"


def check() -> None:
    x, a = center_and_coefficients()
    b3 = evaluate_bounds(x, a, OUTER, 3)
    b9 = evaluate_bounds(x, a, INNER, 9)
    bs = evaluate_bounds(x, a, INNER_SHRINK, 9)

    # Uniform perturbation: |c-c*| < 2^-32.
    # On the certified CENTER domains, |f_c*^j(z)| < 2.
    # Thus |f_c^j(z)-f_c*^j(z)| <= E_j, where
    # E_0=0, E_(j+1)=5 E_j + 2^-32, provided E_j<1.
    errors = [0]
    for _ in range(9):
        errors.append(5 * errors[-1] + PARAMETER_RADIUS)
    assert all(e < UNIT for e in errors)
    for b, period in ((b3, 3), (b9, 9), (bs, 9)):
        for j in range(period):
            assert abs_upper(x[j]) + b.deviation[j] < 2 * UNIT

    # On each circular target boundary, a_p z^2 dominates
    # f_c^p(z) - a_p z^2 - w, simultaneously for EVERY |w|<R_p.
    # Rouche gives exactly two solutions f_c^p(z)=w in the disk.
    margins = {}
    for period, b, target in ((3, b3, OUTER), (9, b9, INNER)):
        margin = rouche_margin(x, b, period, target) - errors[period]
        assert margin > 0, ("proper quadratic-like boundary", period)
        assert abs_upper(x[period]) + errors[period] < target
        margins[period] = margin

        # f_c^p has exactly one critical point in its target disk:
        # (f_c^p)'=2^p*z*prod_{j=1}^{p-1}f_c^j(z).
        for j in range(1, period):
            assert abs_lower(x[j]) > b.deviation[j] + errors[j], (
                "unaccounted critical preimage", period, j
            )

    # All solutions to f_c^9(z)=w, |w|<R9, already lie in the
    # smaller disk of radius 13/512: Rouche gives two roots in
    # this disk as well as exactly two in U9.
    shrink_margin = rouche_margin(x, bs, 9, INNER) - errors[9]
    assert shrink_margin > 0
    assert INNER_SHRINK < INNER < OUTER

    # The original actual real restrictive intervals lie inside
    # their corresponding complex target disks at the center.
    assert max(abs_upper(x[6]), abs_upper(x[3])) < OUTER
    assert max(abs_upper(x[9]), abs_upper(x[18])) < INNER

    # Pairwise disjoint COMPLEX phase images, even after perturbation.
    # Outer: f_c^j(V3) subset f_c^j(U3), 0<=j<3.
    # Inner: f_c^j(V9) subset f_c^j(D(0,13/512)), 0<=j<9.
    phase_margins = {}
    for period, b in ((3, b3), (9, bs)):
        pair_margins = [
            interval_gap(x[i], x[j])
            - b.deviation[i] - b.deviation[j]
            - errors[i] - errors[j]
            for i in range(period)
            for j in range(i + 1, period)
        ]
        assert pair_margins and min(pair_margins) > 0, (
            "complex phase collision", period
        )
        phase_margins[period] = min(pair_margins)

    # Physical cross-scale inclusion: U9 and its F3 and F3^2
    # images all lie in the outer return component V3. Check
    # f_c^{3k}(U9) and f_c^{3k+3}(U9) both lie in U3:
    # j=0,3,6,9. Since U3 contains only one F3-preimage
    # component over U3, f_c^{3k}(U9) subset V3, k=0,1,2.
    nested_margin = min(
        OUTER - abs_upper(x[j]) - b9.deviation[j] - errors[j]
        for j in (0, 3, 6, 9)
    )
    assert nested_margin > 0

    # Critical nonescape for ALL parameters in the claimed disk.
    # Starting |z|<=2^-13, compare with the center's 27-orbit:
    # e_(j+1) <= e_j(2|x_j|+e_j)+2^-32.
    # This is valid for COMPLEX z and COMPLEX parameters.
    trap_errors = [CRITICAL_TRAP]
    for j in range(CENTER_PERIOD):
        e = trap_errors[-1]
        trap_errors.append(
            ceil_div(e * (2 * abs_upper(x[j]) + e))
            + PARAMETER_RADIUS
        )
    assert 2 * trap_errors[27] < CRITICAL_TRAP
    assert CRITICAL_TRAP < INNER
    for j in (9, 18):
        assert abs_upper(x[j]) + trap_errors[j] < INNER, (
            "critical block escapes inner target", j
        )
    # Therefore F27 maps the critical trapping disk into itself,
    # and its 9th and 18th images are inside U9. Every 9-block
    # critical iterate stays inside U9, hence in V9; K9 (and K3)
    # are connected by the standard quadratic-like criterion.

    print("PASS: exact complex quadratic-like two-scale 3/9 certificate")
    print("  c*: unique root f_c^27(0)=0 in source 2^-128 bracket")
    print("  parameter-uniform disk: |c-c*| < 2^-32 (complex)")
    print("  U3=D(0,1/4), U9=D(0,1/32), Vp=component_0(f^-p(Up))")
    for p in (3, 9):
        print(f"  period {p}: proper degree 2, critical point 0 only")
        print("    Rouché margin >", small_decimal_lower(margins[p]))
        print("    phase separation >", small_decimal_lower(phase_margins[p]))
    print("  V9 compactly inside D(0,13/512) and U9")
    print("    shrink boundary margin >", small_decimal_lower(shrink_margin))
    print("  U9, f^3(U9), f^6(U9) contained in V3")
    print("    four-step outer containment margin >",
          small_decimal_lower(nested_margin))
    print("  f^27 critical trapping disk: radius 2^-13")
    print("  connected inner/outer filled Julia sets; K9 subset K3")
    print("  complex physical phase projection j mod 9 -> j mod 3")
    print("  at real center: F3 critical period 9; F9 critical period 3")
    print("  inner real quadratic straightening: unique real period-3 center")
    print("LIMIT: center/nearby parameters fail Paper 2 K(f)=J(f);")
    print("       no KL rays, prime ends, coset sheets or MLC closure")


if __name__ == "__main__":
    check()
