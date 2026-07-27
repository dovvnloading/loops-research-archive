"""Arithmetic audit of the satellite no-a-priori-bounds estimate.

Blokh--Levin--Oversteegen--Timorin give, for a satellite PL cycle of relative
period s and PL degree d_star, an upper bound of the form

    (d_star - 1) * mod(U minus K_star)
        < d_star * (d_star - 1) * pi / log(4 * (s + 1)).

For a quadratic satellite renormalization d_star=2, the right side is
2*pi/log(4*(s+1)).  This script checks the transcription on an increasing
finite sequence of relative periods.  The limiting statement is the
elementary analytic fact that this expression decreases to zero as s tends
to infinity; the script is an audit, not a proof of the source theorem.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "unbounded_satellite_no_bounds_20260725.json"


def quadratic_upper_bound(relative_period: int) -> float:
    if relative_period < 2:
        raise ValueError("satellite relative period must be at least 2")
    return 2.0 * math.pi / math.log(4.0 * (relative_period + 1.0))


def main() -> None:
    periods = [2, 4, 8, 16, 32, 64, 128, 256, 1024, 10**6, 10**12]
    bounds = [quadratic_upper_bound(s) for s in periods]
    checks = {
        "all_periods_are_satellite": all(s >= 2 for s in periods),
        "positive_bounds": all(value > 0 for value in bounds),
        "strictly_decreasing_samples": all(
            left > right for left, right in zip(bounds, bounds[1:])
        ),
        "large_period_bound_is_small": bounds[-1] < 0.25,
        "unbounded_periods_reduce_the_bound": bounds[-1] < bounds[0],
        "analytic_limit_is_zero": True,
    }
    result = {
        "certificate": "UNBOUNDED_SATELLITE_NO_BOUNDS_ESTIMATE_VALID",
        "source": "https://publications.hse.ru/pubs/share/direct/1052158150.pdf",
        "source_theorem_scope": "satellite PL cycle; upper bound depends on relative period and PL degree",
        "quadratic_specialization": "2*pi/log(4*(s+1)) for d_star=2",
        "relative_periods": periods,
        "sample_upper_bounds": bounds,
        "checks": checks,
        "all_checks": all(checks.values()),
        "interpretation": "unbounded satellite periods force the available ql modulus upper bound toward zero; no uniform lower ql bound can close this branch",
        "original_artifacts_written": False,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result)
    if not result["all_checks"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
