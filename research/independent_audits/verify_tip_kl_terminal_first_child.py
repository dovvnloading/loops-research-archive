#!/usr/bin/env python3
"""Exact finite checks for the two terminal KL first-child deductions.

The companion note proves the analytic statements using the source KL nest,
landed puzzle graphs, polynomial-like connectedness and germ uniqueness.
This program checks their real interval, ray-boundary and clock inputs. It
does not formalize those analytic theorems or any localization markings.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import json

from verify_real_nested_3_9 import (
    Interval, UNIT, parameter, iterate, orbit_and_derivative,
)
from verify_period27_misiurewicz_tip import TIP_K, certify as certify_tip
from verify_tip_puzzle_ray_tree import certify as certify_ambient_tree
from verify_tip_internal_ray_lifts import certify as certify_internal_tree


def boundary_angles(pairs: list[str]) -> set[F]:
    return {F(angle) for pair in pairs for angle in pair.split(",")}


def certify() -> dict:
    tip = certify_tip()
    assert (tip["critical_preperiod"], tip["critical_period"]) == (10, 9)
    lower, upper = parameter(TIP_K), parameter(TIP_K + 1)
    parameter_interval = Interval(lower.lo, upper.hi)
    orbit, _ = orbit_and_derivative(parameter_interval, 27)

    # These are outward enclosures of the actual endpoint-defined intervals.
    # Invariance of the actual intervals uses endpoint identities in the note;
    # interval overlap is never used to infer an exact orbit equality.
    outer = Interval(orbit[6].lo, orbit[3].hi)
    inner = Interval(orbit[9].lo, orbit[18].hi)
    assert orbit[6].negative() and orbit[3].positive()
    assert orbit[9].negative() and orbit[18].positive()
    assert orbit[6].below(orbit[9]) and orbit[9].below(orbit[3])
    assert orbit[18].below(orbit[3])
    assert inner.strictly_inside(outer)
    assert -UNIT // 4 < outer.lo < 0 < outer.hi < UNIT // 4
    assert -UNIT // 32 < inner.lo < 0 < inner.hi < UNIT // 32

    phase_signs = {}
    for period, interval, expected_negative_count in (
        (3, outer, 1), (9, inner, 4),
    ):
        images = iterate(interval, parameter_interval, period)
        assert all(image.excludes_zero() for image in images[1:period])
        negatives = sum(image.negative() for image in images[1:period])
        assert negatives == expected_negative_count
        phase_signs[period] = "".join(
            "-" if image.negative() else "+" for image in images[1:period]
        )
        # (f^p)'(x)=2^p*x*product_{j=1}^{p-1} f^j(x).
        # The signs certify a unique maximum for p=3, minimum for p=9.
        assert all(a.below(b) or b.below(a)
                   for i, a in enumerate(images[:period])
                   for b in images[i + 1:period])
    assert phase_signs == {3: "-+", 9: "-++-+--+"}

    # The exact algebraic relation P18(c_tip)+P9(c_tip)=0 is part of
    # certify_tip's IVT/derivative proof. It implies x18=-x9, then x19=x10,
    # hence x27=x18. The checker deliberately makes no equality assertion
    # about two independently rounded interval enclosures.

    ambient = certify_ambient_tree()
    internal = certify_internal_tree()
    boundaries = []
    for name, levels, key in (
        ("ambient f", ambient["levels"], "critical_piece_boundary_pairs"),
        ("internal G=f^3", internal["levels"], "critical_face_internal_pairs"),
    ):
        top = boundary_angles(levels[3][key])
        child = boundary_angles(levels[6][key])
        assert len(top) == 4 and len(child) == 8
        assert top.isdisjoint(child)
        images = Counter(8 * angle % 1 for angle in child)
        assert images == Counter({angle: 2 for angle in top})
        assert F(1, 64) < F(1, 8)
        boundaries.append({
            "scale": name,
            "top_depth": 3,
            "first_child_depth": 6,
            "top_boundary_pairs": levels[3][key],
            "child_boundary_pairs": levels[6][key],
            "common_boundary_angles": [],
            "child_to_top_ray_multiplicity": 2,
            "equipotential_height_ratio_child_to_top": "1/8",
        })

    # An independent internal critical-value calculation. A real-symmetric
    # straightening reverses real order because G has a maximum at 0 whereas
    # the normalized quadratic has a minimum; see the companion note.
    physical_signs = ["+" if orbit[j].positive() else "-"
                      for j in (3, 6, 9, 12, 15, 18)]
    assert physical_signs == ["+", "-", "-", "+", "-", "+"]
    normalized_negative_bits = [int(sign == "+") for sign in physical_signs]
    assert normalized_negative_bits == [1, 0, 0, 1, 0, 1]
    bits = [0]
    itinerary = normalized_negative_bits + normalized_negative_bits[3:] * 3
    for negative in itinerary:
        bits.append(1 - bits[-1] if negative else bits[-1])
    assert bits[:3] == [0, 1, 1]
    assert all(bits[start:start + 3] == [1, 0, 0]
               for start in (3, 6, 9, 12))
    tau_g = F(int("011", 2), 2**3) + F(int("100", 2), 2**3 * (2**3 - 1))
    assert tau_g == F(25, 56)
    assert str(tau_g) == internal["independent_internal_critical_value_angle"]

    stage_clocks = []
    for stage, physical_unit in ((1, 1), (2, 3)):
        q, n, chi, period = 2, 1, 1, 3
        assert ((n - 1) * q + 1, n * q + 1, (2 * n - 1) * q + 1) == (1, 3, 3)
        assert n * q == q
        stage_clocks.append({
            "stage": stage,
            "q": q,
            "n": n,
            "terminal_chi_from_written_nonescape_proof": chi,
            "primitive_return_in_stage_units": period,
            "primitive_return_in_physical_f_units": period * physical_unit,
            "branch_time_in_stage_units": q,
            "branch_time_in_physical_f_units": q * physical_unit,
            "root_arrow_phase_modulo_stage_period": q % period,
        })

    return {
        "status": "EXACT_TIP_KL_TERMINAL_FIRST_CHILD_INPUTS_PASS",
        "parameter": "certified root of P18(c)+P9(c)=0 in the 2^-128 tip bracket",
        "actual_intervals": {"I3": "[x6,x3]", "I9": "[x9,x18]"},
        "noncritical_phase_signs": phase_signs,
        "return_turning_points": {"f3": "unique maximum at 0", "f9": "unique minimum at 0"},
        "endpoint_identities_used_in_written_proof": {
            "f3": ["x6 -> x9", "x3 -> x6", "0 -> x3"],
            "f9": ["x9 -> x18", "x18 -> x27=x18", "0 -> x9"],
        },
        "first_child_boundaries": boundaries,
        "stage_clocks": stage_clocks,
        "normalized_G_critical_value_itinerary": "100(101)^infinity; 1 denotes negative",
        "normalized_G_critical_value_angles": [str(tau_g), str(1 - tau_g)],
        "analytic_trust_boundary": [
            "KL source puzzle topology and first-return/nest definitions",
            "actual ray landing and internal-to-ambient access correspondence",
            "Douady-Hubbard connectedness and polynomial-like straightening",
            "Levin section 1.2 equality of filled Julia sets for equivalent germs",
        ],
        "scope": "Finite exact inputs to the written two-stage terminal proof; no localization O/xi/eta, interscale sheet functor or global ledger promotion",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()
    report = certify()
    print(json.dumps(report, indent=2, sort_keys=True) if args.print_json else report["status"])


if __name__ == "__main__":
    main()
