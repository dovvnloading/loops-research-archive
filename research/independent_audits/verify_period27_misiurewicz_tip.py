#!/usr/bin/env python3
"""Exact integer certificate for the real 9-periodic Misiurewicz tip.

Verifies finite arithmetic and angles, not imported landing/Julia theorems
or the Kahn-Lyubich prime-end and sheet constructions.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

from verify_real_nested_3_9 import (
    Interval, ZERO, ONE, UNIT, C_BITS, parameter, iterate,
    orbit_and_derivative,
)

TIP_K = -607918036626757496169199575185708826140
CENTER_K = -607890580437450502081459824019535455703


def substitute(word: str) -> str:
    return "".join("011" if bit == "0" else "100" for bit in word)


def certify() -> dict:
    low, high = parameter(TIP_K), parameter(TIP_K + 1)
    orbit_low = iterate(ZERO, low, 18)
    orbit_high = iterate(ZERO, high, 18)
    assert (orbit_low[18] + orbit_low[9]).positive()
    assert (orbit_high[18] + orbit_high[9]).negative()
    bracket = Interval(low.lo, high.hi)
    X, deriv = orbit_and_derivative(bracket, 27)
    derivative_G = deriv[18] + deriv[9]
    assert -71 * UNIT < derivative_G.lo <= derivative_G.hi < -70 * UNIT
    assert -2 * UNIT < bracket.lo < bracket.hi < -UNIT
    assert CENTER_K - (TIP_K + 1) > (1 << (C_BITS - 32))
    assert X[1].negative() and X[9].negative() and X[18].positive()
    assert all(interval.excludes_zero() for interval in X[1:19])

    # At the unique root of P18+P9, x18=-x9 and x19=x10.
    # Consequently the critical orbit has exact preperiod 10, period 9.
    early = X[:10]
    cycle = X[10:19]
    assert all(a.below(b) or b.below(a)
               for i, a in enumerate(early) for b in early[i + 1:])
    assert all(a.below(b) or b.below(a) for a in early for b in cycle)
    assert all(a.below(b) or b.below(a)
               for i, a in enumerate(cycle) for b in cycle[i + 1:])
    multiplier = ONE
    for j in range(10, 19):
        multiplier = multiplier * X[j].times(2)
    assert 3 * UNIT < multiplier.lo <= multiplier.hi < 4 * UNIT

    # Actual real restrictive intervals of periods 3 and 9.
    assert X[6].negative() and X[3].positive()
    I3 = Interval(X[6].lo, X[3].hi)
    I9 = Interval(X[9].lo, X[18].hi)
    assert I9.strictly_inside(I3)
    assert X[9].strictly_inside(I3) and X[18].strictly_inside(I3)
    for period, interval in ((3, I3), (9, I9)):
        images = iterate(interval, bracket, period)
        assert all(a.below(b) or b.below(a)
                   for i, a in enumerate(images[:period])
                   for b in images[i + 1:period])
        assert all(phase.excludes_zero() for phase in images[1:period])
        # f^period(I_period)=I_period follows from the unique turning
        # point, whose critical value is x_period, and endpoint images.
        if period == 3:
            assert X[9].strictly_inside(I3)
        else:
            assert X[9].negative() and X[18].positive()

    block_0 = substitute(substitute("0"))
    block_1 = substitute(substitute("1"))
    assert (block_0, block_1) == ("011100100", "100011011")
    base = 1 << 9
    lower = Fraction(int(block_0, 2), base) + Fraction(
        int(block_1, 2), base * (base - 1))
    upper = Fraction(int(block_1, 2), base) + Fraction(
        int(block_0, 2), base * (base - 1))
    assert (lower, upper) == (Fraction(116791, 261632),
                              Fraction(144841, 261632))
    assert lower + upper == 1

    # Zakeri's real critical-value sign-to-angle recurrence.
    signs = ["1" if X[j].negative() else "0" for j in range(1, 19)]
    assert signs[:9] == list("100101101")
    assert signs[9:] == list("100101100")
    bits = [0]
    for sign in signs + signs[9:]:
        bits.append(1 - bits[-1] if sign == "1" else bits[-1])
    assert bits[:9] == list(map(int, block_0))
    assert bits[9:18] == list(map(int, block_1))
    assert bits[18:27] == bits[9:18] and bits[27] == bits[18]

    double = lambda angle: 2 * angle % 1
    for angle in (lower, upper):
        orbit_angle = [angle]
        for _ in range(27):
            orbit_angle.append(double(orbit_angle[-1]))
        assert orbit_angle[9] == orbit_angle[18]
        assert all(orbit_angle[j] != orbit_angle[j + 9] for j in range(9))
        assert orbit_angle[9] not in (orbit_angle[10], orbit_angle[12])
        assert all(not (lower < orbit_angle[j] < upper)
                   for j in range(1, 19))
        angular_symbols = [
            "*" if 2 * orbit_angle[j] in (angle, angle + 1)
            else "1" if angle < 2 * orbit_angle[j] < angle + 1
            else "0" for j in range(27)
        ]
        assert angular_symbols == signs + signs[9:]

    accesses = sorted([lower / 2, (lower + 1) / 2,
                       upper / 2, (upper + 1) / 2])
    assert len(set(accesses)) == 4
    assert [double(angle) for angle in accesses] == [lower, upper, lower, upper]
    images_f6 = [64 * angle % 1 for angle in accesses]
    assert images_f6 == [Fraction(2327, 8176), Fraction(5849, 8176),
                         Fraction(2327, 8176), Fraction(5849, 8176)]
    assert accesses[0] != accesses[2] and images_f6[0] == images_f6[2]

    return {
        "status": "EXACT_PERIOD9_MISIUREWICZ_TIP_CERTIFICATE_PASS",
        "parameter_bracket": {"lower_numerator": TIP_K,
                              "upper_numerator": TIP_K + 1,
                              "denominator_power_of_two": C_BITS},
        "critical_preperiod": 10,
        "critical_period": 9,
        "repelling_f9_multiplier_bounds": ["3", "4"],
        "G_derivative_bounds": ["-71", "-70"],
        "outer_return": 3,
        "inner_return": 9,
        "tuned_tip_angles": [str(lower), str(upper)],
        "critical_preimage_angles": [str(angle) for angle in accesses],
        "critical_ray_f6_angles": [str(angle) for angle in images_f6],
        "tuning_blocks": {"0": block_0, "1": block_1},
        "physical_f6_access_collision": {
            "first": str(accesses[0]), "second": str(accesses[2]),
            "common_image": str(images_f6[0])},
        "scope": "Finite real-algebraic and angular claims; ray landing from Zakeri Theorem 3.1, K=J from classical Misiurewicz theory. This does not establish a KL puzzle/sheet atlas",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-manifest", action="store_true")
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()
    report = certify()
    serialized = json.dumps(report, sort_keys=True, indent=2) + "\n"
    if args.check_manifest:
        path = (Path(__file__).resolve().parents[2] / "results" /
                "period27_misiurewicz_tip.json")
        assert path.read_text(encoding="utf-8") == serialized, "manifest mismatch"
    print(serialized if args.print_json else report["status"],
          end="" if args.print_json else "\n")


if __name__ == "__main__":
    main()
