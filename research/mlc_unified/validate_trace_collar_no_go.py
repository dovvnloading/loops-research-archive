"""Independent arithmetic certificate for the pulled-equipotential no-go.

For the model pullback z -> z**(2**q), an inverse branch divides angular
width by 2**q. A full parent and full child equipotential arc bounded by
the same two rays can be opposite sides of one ray-bounded serial rectangle
only if their angular widths agree. The strict inequality below is the
finite check; the argument is exact for every q >= 1 and every positive
parent width.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "trace_collar_no_go_20260725.json"


def check(q: int, parent_width: Fraction) -> dict[str, object]:
    degree = 2**q
    child_width = parent_width / degree
    return {
        "q": q,
        "degree": degree,
        "parent_width": str(parent_width),
        "child_width": str(child_width),
        "child_positive": child_width > 0,
        "strictly_smaller": child_width < parent_width,
        "same_full_arc_width": child_width == parent_width,
        "serial_rectangle_possible_from_widths": child_width == parent_width,
    }


def main() -> None:
    rows = [
        check(q, width)
        for q in range(1, 33)
        for width in (Fraction(1, 3), Fraction(1, 7), Fraction(1, 100), Fraction(2, 5))
    ]
    result = {
        "certificate": "PULLED_EQUIPOTENTIAL_SERIAL_RECTANGLE_NO_GO",
        "checks": rows,
        "all_checks": all(
            row["child_positive"]
            and row["strictly_smaller"]
            and not row["same_full_arc_width"]
            and not row["serial_rectangle_possible_from_widths"]
            for row in rows
        ),
        "scope": "exact width obstruction only; full-trace rectangle calculus remains valid for genuine trace-compatible collars; no global MLC claim",
        "original_artifacts_written": False,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    if not result["all_checks"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
