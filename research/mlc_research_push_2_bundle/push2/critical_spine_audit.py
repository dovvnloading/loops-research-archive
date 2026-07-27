#!/usr/bin/env python3
"""Audit critical chronology and critical-spine retention for a finite lift.

Input JSON schema:
{
  "name": "example",
  "root_degrees": [2, 1],
  "lift_degrees": [1, 2],
  "source_projection_degree": 1,
  "retention": [true, false],
  "notes": "optional"
}

The degree ladder uses
    lift_degree[j] * projection_degree[j+1]
      = projection_degree[j] * root_degree[j].

The optional retention list is interpreted only after a quadratic partial
covering exists. Each value records whether the next embedded stage contains
its propagated critical value.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Sequence


class AuditError(ValueError):
    """Raised when an audit input is malformed or degree data are inconsistent."""


@dataclass(frozen=True)
class StageAudit:
    stage: int
    root_degree: int
    lift_degree: int
    projection_degree_in: int
    projection_degree_out: int
    swap: str | None


@dataclass(frozen=True)
class AuditReport:
    name: str
    valid_degree_ladder: bool
    exact_chronology: bool
    endpoint_projection_degree: int
    root_total_degree: int
    lift_total_degree: int
    first_swap_stage: int | None
    first_retention_failure: int | None
    stages: list[StageAudit]
    notes: str | None


def _positive_int(value: Any, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise AuditError(f"{field} must be a positive integer; got {value!r}")
    return value


def _degree_word(value: Any, field: str) -> list[int]:
    if not isinstance(value, list) or not value:
        raise AuditError(f"{field} must be a nonempty list")
    word = [_positive_int(item, f"{field}[{idx}]") for idx, item in enumerate(value)]
    if any(item not in (1, 2) for item in word):
        raise AuditError(f"{field} must contain only 1 or 2 for a quadratic stage system")
    return word


def _product(values: Sequence[int]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def audit(data: dict[str, Any]) -> AuditReport:
    name = str(data.get("name", "unnamed"))
    root = _degree_word(data.get("root_degrees"), "root_degrees")
    lift = _degree_word(data.get("lift_degrees"), "lift_degrees")
    if len(root) != len(lift):
        raise AuditError("root_degrees and lift_degrees must have the same length")

    projection = _positive_int(data.get("source_projection_degree", 1), "source_projection_degree")
    stages: list[StageAudit] = []
    first_swap: int | None = None

    for idx, (root_degree, lift_degree) in enumerate(zip(root, lift, strict=True)):
        numerator = projection * root_degree
        if numerator % lift_degree != 0:
            raise AuditError(
                "inconsistent degree square at stage "
                f"{idx}: {lift_degree} does not divide {projection}*{root_degree}"
            )
        next_projection = numerator // lift_degree
        swap: str | None = None
        if root_degree != lift_degree:
            if root_degree == 2 and lift_degree == 1:
                swap = "criticality moved from branch into transverse projection"
            elif root_degree == 1 and lift_degree == 2:
                swap = "criticality moved from transverse projection back into branch"
            else:
                swap = "degree mismatch"
            if first_swap is None:
                first_swap = idx

        stages.append(
            StageAudit(
                stage=idx,
                root_degree=root_degree,
                lift_degree=lift_degree,
                projection_degree_in=projection,
                projection_degree_out=next_projection,
                swap=swap,
            )
        )
        projection = next_projection

    retention_raw = data.get("retention", [])
    if retention_raw is None:
        retention_raw = []
    if not isinstance(retention_raw, list) or any(not isinstance(v, bool) for v in retention_raw):
        raise AuditError("retention must be a list of booleans")
    first_retention_failure = next((idx for idx, value in enumerate(retention_raw) if not value), None)

    exact_chronology = first_swap is None and all(stage.projection_degree_out == 1 for stage in stages)
    return AuditReport(
        name=name,
        valid_degree_ladder=True,
        exact_chronology=exact_chronology,
        endpoint_projection_degree=projection,
        root_total_degree=_product(root),
        lift_total_degree=_product(lift),
        first_swap_stage=first_swap,
        first_retention_failure=first_retention_failure,
        stages=stages,
        notes=str(data["notes"]) if "notes" in data else None,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON audit input")
    parser.add_argument("--output", type=Path, help="write JSON report to this path")
    args = parser.parse_args()

    try:
        raw = json.loads(args.input.read_text(encoding="utf-8"))
        if not isinstance(raw, dict):
            raise AuditError("top-level JSON value must be an object")
        report = audit(raw)
    except (OSError, json.JSONDecodeError, AuditError) as exc:
        print(f"audit failed: {exc}", file=sys.stderr)
        return 2

    payload = asdict(report)
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
