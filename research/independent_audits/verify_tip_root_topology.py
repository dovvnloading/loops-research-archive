#!/usr/bin/env python3
"""Exact finite inputs for the tip's inner interval and root-type obstruction.

The companion proof uses normalized straightening to conclude K9=I9
and an embedded cross in K3; no equivariant conjugacy is assumed.
This checker verifies critical clocks, the
straightening parameter identity, and every endpoint/order/orientation of
the nine actual interval phases. It does not formalize straightening or
Kahn's localization theorem.
"""
from __future__ import annotations

import argparse
import json
from math import gcd
from pathlib import Path

from verify_period27_misiurewicz_tip import TIP_K, certify as certify_tip
from verify_real_nested_3_9 import (
    C_BITS, PREC, Interval, orbit_and_derivative, parameter,
)


def poly_add(a: list[int], b: list[int]) -> list[int]:
    result = [0] * max(len(a), len(b))
    for j, value in enumerate(a):
        result[j] += value
    for j, value in enumerate(b):
        result[j] += value
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    result = [0] * (len(a) + len(b) - 1)
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            result[j + k] += x * y
    return result


def canonical_index(index: int) -> int:
    """Use the certified x19=x10 and exact eventual period nine."""
    return index if index < 10 else 10 + (index - 10) % 9


def enclosure(interval: Interval) -> dict:
    return {
        "lower_numerator": interval.lo,
        "upper_numerator": interval.hi,
        "denominator_power_of_two": PREC,
    }


def certify() -> dict:
    tip = certify_tip()
    preperiod, period = tip["critical_preperiod"], tip["critical_period"]
    assert (preperiod, period) == (10, 9)
    clocks = {}
    for step in (3, 9):
        clocks[str(step)] = {
            "critical_preperiod": (preperiod + step - 1) // step,
            "eventual_period": period // gcd(step, period),
        }
    assert clocks == {
        "3": {"critical_preperiod": 4, "eventual_period": 3},
        "9": {"critical_preperiod": 2, "eventual_period": 1},
    }

    # Independent polynomial arithmetic: Q_c^3(0)-Q_c^2(0)=c^3(c+2).
    polynomials = [[0]]
    for _ in range(3):
        last = polynomials[-1]
        polynomials.append(poly_add(poly_mul(last, last), [0, 1]))
    relation = poly_add(polynomials[3], [-a for a in polynomials[2]])
    assert relation == poly_mul([0, 0, 0, 1], [2, 1])
    assert relation == [0, 0, 0, 2, 1]
    chebyshev_orbit = [0]
    for _ in range(3):
        chebyshev_orbit.append(chebyshev_orbit[-1] ** 2 - 2)
    assert chebyshev_orbit == [0, -2, 2, 2]

    lower, upper = parameter(TIP_K), parameter(TIP_K + 1)
    c = Interval(lower.lo, upper.hi)
    orbit, _ = orbit_and_derivative(c, 27)
    assert orbit[9].negative() and orbit[18].positive()
    assert all(orbit[a].below(orbit[b]) or orbit[b].below(orbit[a])
               for a, b in ((0, 9), (0, 18), (9, 18)))

    # Exact orbit identities x18=-x9 and x19=x10 are imported from the
    # tip certificate's isolated algebraic relation, not inferred from
    # overlap of interval enclosures. For j>=1, the two phase endpoints
    # are x_j and x_(j+9); the central phase is [x9,x18].
    endpoint_pairs = [(9, 18)]
    for j in range(1, 9):
        left, right = j, j + 9
        if orbit[right].below(orbit[left]):
            left, right = right, left
        assert orbit[left].below(orbit[right]), j
        endpoint_pairs.append((left, right))
    assert endpoint_pairs == [
        (9, 18), (1, 10), (11, 2), (12, 3), (13, 4),
        (5, 14), (6, 15), (16, 7), (8, 17),
    ]
    phases = [Interval(orbit[a].lo, orbit[b].hi)
              for a, b in endpoint_pairs]
    for j, a in enumerate(phases):
        for b in phases[j + 1:]:
            assert a.below(b) or b.below(a), (j, a, b)
    assert all(interval.excludes_zero() for interval in phases[1:])

    records = []
    for j, ((left, right), interval) in enumerate(zip(endpoint_pairs, phases)):
        next_phase = (j + 1) % 9
        if j == 0:
            assert canonical_index(left + 1) == canonical_index(right + 1) == 10
            assert endpoint_pairs[next_phase] == (1, 10)
            orientation = "two monotone branches; unique minimum at 0"
        else:
            mapped = (canonical_index(left + 1), canonical_index(right + 1))
            if interval.negative():
                mapped = mapped[::-1]
                orientation = "decreasing"
            else:
                assert interval.positive()
                orientation = "increasing"
            assert mapped == endpoint_pairs[next_phase], (j, mapped)
        records.append({
            "physical_phase": j,
            "coarse_phase": j % 3,
            "exact_interval": f"[x{left},x{right}]",
            "left_endpoint_orbit_index": left,
            "right_endpoint_orbit_index": right,
            "left_endpoint_enclosure": enclosure(orbit[left]),
            "right_endpoint_enclosure": enclosure(orbit[right]),
            "next_physical_phase": next_phase,
            "f_on_phase": orientation,
        })

    return {
        "status": "EXACT_TIP_ROOT_INTERVAL_INPUTS_PASS",
        "parameter_bracket": {
            "lower_numerator": TIP_K,
            "upper_numerator": TIP_K + 1,
            "denominator_power_of_two": C_BITS,
        },
        "stage_critical_clocks": clocks,
        "normalized_inner_parameter_relation_coefficients_ascending": relation,
        "normalized_inner_parameter": -2,
        "normalized_inner_critical_orbit": chebyshev_orbit,
        "written_analytic_result": "K9=[x9,x18]; K3 contains an embedded four-arm cross at 0",
        "inner_root_exact_interval": "[x9,x18]",
        "exact_orbit_relations": ["x18=-x9", "x19=x10", "x27=x18"],
        "phase_intervals": records,
        "phase_intervals_pairwise_disjoint": True,
        "source_interface_obstructions": [
            "Written proof: no holomorphic Kahn marked morphism has full source root K9 and full target root K3",
            "No Kahn local cover can biject the full fine and coarse roots",
            "Written proof: every physical iterate fails the inverse-root equality already as a germ at 0",
        ],
        "analytic_trust_boundary": [
            "Connected quadratic-like restrictions and their equality to terminal puzzle filled sets",
            "Douady-Hubbard normalized straightening; parameter reality from reflection and uniqueness",
            "Filled Julia set of z^2-2 is [-2,2]",
            "Embedded cross excludes interval topology",
            "Compact marked-root image is clopen in the connected target root by the open mapping theorem",
            "A local holomorphic map pulls back a branched star to a branched star",
            "Kahn local-cover definition requires a bijection of the marked roots",
        ],
        "scope": "Finite exact inputs and interval phase table; the all-morphism obstruction is a separate written analytic proof, with no full canonical KL tile or global MLC closure claimed by this checker",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-manifest", action="store_true")
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()
    report = certify()
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.check_manifest:
        path = Path(__file__).resolve().parents[2] / "results" / "tip_root_interval_geometry.json"
        assert path.read_text(encoding="utf-8") == rendered, "manifest mismatch"
    print(rendered if args.print_json else report["status"], end="" if args.print_json else "\n")


if __name__ == "__main__":
    main()
