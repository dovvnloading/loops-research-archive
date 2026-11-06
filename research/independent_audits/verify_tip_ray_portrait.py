#!/usr/bin/env python3
"""Exact period-nine tip ray portrait. Checks arithmetic, not landing theory."""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations
import argparse
import json
from pathlib import Path

LOWER = Fraction(116791, 261632)
UPPER = Fraction(144841, 261632)


def doubled(angle: Fraction, steps: int) -> Fraction:
    return (2 ** steps * angle) % 1


def linked(first: tuple[Fraction, Fraction],
           second: tuple[Fraction, Fraction]) -> bool:
    a, b = sorted(first)
    c, d = sorted(second)
    return (a < c < b) != (a < d < b)


def certify() -> dict:
    assert LOWER + UPPER == 1
    portrait = [(doubled(LOWER, 9 + j), doubled(UPPER, 9 + j))
                for j in range(9)]
    assert portrait[0] == (Fraction(283, 511), Fraction(228, 511))
    assert portrait[-1] == (Fraction(397, 511), Fraction(114, 511))
    assert all(doubled(a, 9) == a and doubled(b, 9) == b
               for a, b in portrait)
    assert all(all(doubled(x, t) != x for t in range(1, 9))
               for pair in portrait for x in pair)
    assert len(set(angle for pair in portrait for angle in pair)) == 18
    assert all(not linked(a, b) for a, b in combinations(portrait, 2))
    pairs = [
        dict(phase=10 + j,
             lower=str(min(pair)),
             upper=str(max(pair)),
             lower_from_critical_value=str(pair[0]),
             upper_from_critical_value=str(pair[1]))
        for j, pair in enumerate(portrait)
    ]
    assert len({(a['lower'], a['upper']) for a in pairs}) == 9
    for modulus in (1, 2, 7, 511, 1022):
        assert [k for k in range(modulus) if (2*k) % modulus == k] == [0]
    return dict(
        status="EXACT_TIP_PERIOD9_RAY_PORTRAIT_PASS",
        critical_value_rays=[str(LOWER), str(UPPER)],
        first_periodic_landing_phase=10,
        periodic_orbit_length=9,
        nine_landing_pairs=pairs,
        distinct_rational_angles=18,
        pairwise_chord_crossings=0,
        tip_interval_endpoint_phase=18,
        tip_interval_endpoint_rays=["114/511", "397/511"],
        conditional_renormalization_fiber={
            "ambient_return": "x -> 512*x mod 1",
            "internal_return": "t -> 2*t mod 1",
            "forced_common_internal_angle": "0/1",
            "requires": "true connected degree-two period-nine renormalization with endpoint in its Julia set, Levin p1 and p2, and both rays in its admissible set",
        },
        scope="Exact finite arithmetic only; ray landing imported from Zakeri; no proof of a Levin map at this tip or any KL prime-end/sheet functor",
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-manifest", action="store_true")
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()
    report = certify()
    encoded = json.dumps(report, sort_keys=True, indent=2) + "\n"
    if args.check_manifest:
        manifest = Path(__file__).resolve().parents[2] / "results" / "period27_tip_ray_portrait.json"
        assert manifest.read_text(encoding="utf-8") == encoded, "manifest differs"
    print(encoded if args.print_json else report["status"],
          end="" if args.print_json else "\n")


if __name__ == "__main__":
    main()
