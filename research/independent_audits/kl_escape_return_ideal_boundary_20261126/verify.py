#!/usr/bin/env python3
"""Metadata and exact depth checks, NOT a verifier of the analytic proof."""
from __future__ import annotations

import csv
import json
from collections import deque
from pathlib import Path

TARGET = "ESCAPE_RETURN_KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY"
WAVE = "WAVE_TO_KL_ADDRESS_ACCESS_SELECTOR"
LIFT = "FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS"
SOURCE = "research/independent_audits/kl_escape_return_ideal_boundary_20261126/verify.py"
GATES = ("H1_MARKED_CONSTRUCTION", "MBTT", "H3_COERCIVITY", "H4_RIGIDITY")


def phase_depths(q: int, n: int, r: int) -> tuple[int, ...]:
    if q < 2 or n < 1 or r < 1:
        raise ValueError("need q >= 2, n >= 1 and r >= 1")
    m = n * q + 1
    return tuple(m + r - k for k in range(r + 1))


def dependency_path(rows: dict, root: str, target: str) -> list[str] | None:
    queue = deque([(root, [root])])
    seen = {root}
    while queue:
        node, path = queue.popleft()
        if node == target:
            return path
        for dep in rows[node]["deps"]:
            if dep not in seen:
                seen.add(dep)
                queue.append((dep, path + [dep]))
    return None


def self_test() -> None:
    assert phase_depths(2, 1, 3) == (6, 5, 4, 3)
    for q in range(2, 12):
        for n in range(1, 8):
            for r in range(1, 41):
                depths = phase_depths(q, n, r)
                assert len(depths) == r + 1
                assert depths[-1] == n * q + 1
                assert all(a - b == 1 for a, b in zip(depths, depths[1:]))
    for args in ((1, 1, 1), (2, 0, 1), (2, 1, 0)):
        try:
            phase_depths(*args)
        except ValueError:
            pass
        else:
            raise AssertionError(f"invalid clock accepted: {args}")
    graph = {"A": {"deps": ["B"]}, "B": {"deps": ["A", "C"]}, "C": {"deps": []}}
    assert dependency_path(graph, "A", "C") == ["A", "B", "C"]
    assert dependency_path(graph, "C", "A") is None


def audit(root: Path) -> dict:
    ledger = json.loads((root / "ledger.json").read_text(encoding="utf-8"))
    rows = {row["id"]: row for row in ledger["obligations"]}
    assert len(rows) == len(ledger["obligations"])
    for key in (TARGET, WAVE, LIFT, *GATES):
        assert key in rows
    with (root / "formalization/physical_bridge_sources.tsv").open(encoding="utf-8") as stream:
        registered = [row for row in csv.DictReader(stream, delimiter="\t") if row["source"] == SOURCE]
    assert registered == [{"source": SOURCE, "routes": "METADATA"}]
    index = json.loads((root / "formalization/physical_bridge_index.json").read_text(encoding="utf-8"))
    assert SOURCE in index["w1"]["checks"]
    assert TARGET in index["w1"]["obligations"]
    return {
        "classification": "METADATA; phase arithmetic only, not analytic proof",
        "target": TARGET,
        "ledger_status": rows[TARGET]["status"],
        "direct_consumers": sorted(k for k, row in rows.items() if TARGET in row["deps"]),
        "gate_paths_to_target": {g: dependency_path(rows, g, TARGET) for g in GATES},
        "gate_paths_to_wave_selector": {g: dependency_path(rows, g, WAVE) for g in GATES},
        "two_tip_stage_example": {"q": 2, "n": 1, "stage_return": 3, "depths": phase_depths(2, 1, 3)},
        "clock_cases_tested": 10 * 7 * 40,
    }


if __name__ == "__main__":
    self_test()
    print(json.dumps(audit(Path(__file__).resolve().parents[3]), indent=2, sort_keys=True))
