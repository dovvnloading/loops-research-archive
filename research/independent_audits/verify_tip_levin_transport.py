#!/usr/bin/env python3
"""Exact finite consequences of source-defined Levin 3/9 ray maps.

Does NOT prove Levin (p2), local connectivity, landing, or a KL sheet functor.
Those are separate classical analytical inputs in the accompanying audit.
"""
from __future__ import annotations

from itertools import product
from verify_tip_ray_portrait import LOWER, UPPER, doubled


def portrait_angles() -> dict[int, tuple[int, int]]:
    """Numerators on the common denominator 511; all operations are exact."""
    data: dict[int, tuple[int, int]] = {}
    for phase in range(10, 19):
        pair = tuple(int(511 * doubled(theta, phase - 1)) for theta in (LOWER, UPPER))
        assert all(511 * doubled(theta, phase - 1) == n
                   for theta, n in zip((LOWER, UPPER), pair))
        data[phase] = tuple(sorted(pair))
    return data


def circular_descents(values: tuple[int, ...]) -> int:
    return sum(values[j] > values[(j + 1) % len(values)]
               for j in range(len(values)))


def possible_period_three_residues(a: int, b: int) -> tuple[int, ...]:
    # Sorted ambient angles: 110, 114, 142, 369, 397, 401.
    # Doubling after ambient return times 8 generates both 3-cycles.
    return (a, b, (4 * b) % 7, (2 * a) % 7,
            (4 * a) % 7, (2 * b) % 7)


def certify() -> dict:
    rays = portrait_angles()
    assert rays[12] == (110, 401)
    assert rays[15] == (142, 369)
    assert rays[18] == (114, 397)
    assert len({n for pair in rays.values() for n in pair}) == 18

    # Eligibility labels are deduced *analytically* from phase separation
    # and the return invariance of K9 ⊂ K3, not certified by this script.
    period_9_phases = sorted(p for p in rays if p % 9 == 0)
    period_3_phases = sorted(p for p in rays if p % 3 == 0)
    assert period_9_phases == [18]
    assert period_3_phases == [12, 15, 18]
    eligible_9 = sorted(n for p in period_9_phases for n in rays[p])
    eligible_3 = sorted(n for p in period_3_phases for n in rays[p])
    assert eligible_9 == [114, 397]
    assert eligible_3 == [110, 114, 142, 369, 397, 401]

    # Theorem 3(b): internal angles on these ambient ×8 3-cycles must
    # be fixed by ×8 internally, hence residues mod 7.
    # Theorem 3(d): a circle-monotone degree-one extension permits
    # at most one *strict* circular descent in the ordered image.
    solutions = [
        (a, b) for a, b in product(range(7), repeat=2)
        if circular_descents(possible_period_three_residues(a, b)) <= 1
    ]
    assert solutions == [(0, 0), (4, 5)]

    # The all-zero solution is ruled out ANALYTICALLY, because the three
    # landing points have least period three under g3=f^3, while an
    # internal angle-zero ray lands at a fixed point.
    a, b = (4, 5)
    order = eligible_3
    internal_residues = possible_period_three_residues(a, b)
    assert internal_residues == (4, 5, 6, 1, 2, 3)
    p3 = dict(zip(order, internal_residues))
    for angle in order:
        assert (8 * angle) % 511 in p3
        assert p3[(8 * angle) % 511] == (2 * p3[angle]) % 7

    assert all((512 * angle) % 511 == angle for angle in eligible_9)
    # The unique fixed point of doubling modulo 1 is 0.
    assert [k for k in range(1) if (2 * k) % 1 == k] == [0]
    assert (p3[114], p3[397]) == (5, 2)
    return {
        "status": "EXACT_LEVIN_3_9_FINITE_ANGLE_CHECK_PASS",
        "period9_known_portrait_eligible": [f"{x}/511" for x in eligible_9],
        "period9_internal_angles": {"114/511": "0", "397/511": "0"},
        "period3_known_portrait_eligible": [f"{x}/511" for x in eligible_3],
        "period3_internal_angles": {f"{k}/511": f"{v}/7" for k, v in p3.items()},
        "circular_monotone_solutions_mod7": solutions,
        "scope": "Finite angular arithmetic and conditional phase labels only; p2 and actual source-map applicability are separate analytic arguments in the written audit",
    }


if __name__ == "__main__":
    print(certify()["status"])
