#!/usr/bin/env python3
"""Audit the Lean mirror of the canonical research obligation ledger.

This is a source-sync / graph integrity check. It does NOT check
mathematical statements: Lean independently checks only the mirrored
discrete status and dependency graph, while source geometry remains open.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STATUS = {"imported": "sourceImported", "proved": "ledgerProved", "open": "openGoal"}
ROW = re.compile(
    r'⟨"([A-Z0-9_]+)", \.(sourceImported|ledgerProved|openGoal), '
    r'\[([0-9, ]*)\], \[([0-9, ]*)\]⟩'
)


def assumptions(entry: dict) -> list[str]:
    raw = entry.get("hyp", "none")
    if not raw or raw == "none":
        return []
    return [re.sub(r"\s+", "", s) for s in raw.split(",")]


def canonical_order(entries: list[dict]) -> list[dict]:
    by_id = {item["id"]: item for item in entries}
    if len(by_id) != len(entries):
        raise ValueError("duplicate ledger IDs")
    visited: set[str] = set()
    active: set[str] = set()
    order: list[dict] = []

    def visit(item_id: str) -> None:
        if item_id not in by_id:
            raise ValueError(f"dangling reference: {item_id}")
        if item_id in active:
            raise ValueError(f"cycle via {item_id}")
        if item_id in visited:
            return
        active.add(item_id)
        item = by_id[item_id]
        for dep in [*item["deps"], *assumptions(item)]:
            visit(dep)
        active.remove(item_id)
        visited.add(item_id)
        order.append(item)

    for item in entries:
        visit(item["id"])
    return order


def parse_indices(raw: str) -> list[int]:
    return [] if not raw.strip() else [int(s.strip()) for s in raw.split(",")]


def main() -> None:
    ledger = json.loads((ROOT / "ledger.json").read_text(encoding="utf-8"))
    records = ledger["obligations"]
    ordered = canonical_order(records)
    index = {entry["id"]: i for i, entry in enumerate(ordered)}
    expected = [
        (
            entry["id"],
            STATUS[entry["status"]],
            [index[d] for d in entry["deps"]],
            [index[d] for d in assumptions(entry)],
        )
        for entry in ordered
    ]

    text = (ROOT / "ResearchLedger.lean").read_text(encoding="utf-8")
    actual = []
    for line in text.splitlines():
        if '⟨"' not in line:
            continue
        match = ROW.fullmatch(line.strip().rstrip(","))
        if match is None:
            raise ValueError(f"unparseable Lean ledger row: {line!r}")
        name, status, deps, hyps = match.groups()
        actual.append((name, status, parse_indices(deps), parse_indices(hyps)))
    if actual != expected:
        mismatch = next(
            (i for i, (a, b) in enumerate(zip(actual, expected)) if a != b),
            min(len(actual), len(expected)),
        )
        raise AssertionError(
            f"Lean source mirror differs from ledger at row {mismatch}: "
            f"Lean={actual[mismatch:mismatch+1]} source={expected[mismatch:mismatch+1]}"
        )

    status_counts = {
        name: sum(entry["status"] == name for entry in ordered)
        for name in STATUS
    }
    assert ledger["counts"] == status_counts, (ledger["counts"], status_counts)
    assert len(records) == 465
    assert status_counts == {"imported": 34, "proved": 316, "open": 115}

    edge_count = sum(len(x["deps"]) for x in ordered)
    hyp_edge_count = sum(len(assumptions(x)) for x in ordered)
    conditional_count = sum(
        x["status"] == "proved" and bool(assumptions(x)) for x in ordered
    )
    by_id = {x["id"]: x for x in ordered}
    ready_open = [
        x["id"]
        for x in ordered
        if x["status"] == "open"
        and all(by_id[d]["status"] != "open" for d in x["deps"])
    ]
    assert (edge_count, hyp_edge_count, conditional_count, len(ready_open)) == (
        1035, 18, 14, 20
    )
    for i, x in enumerate(ordered):
        assert all(index[d] < i for d in [*x["deps"], *assumptions(x)])
        if x["status"] == "proved":
            assert all(by_id[d]["status"] != "open" for d in x["deps"])
    for gate in [
        "H1_MARKED_CONSTRUCTION",
        "H2_CALIBRATION",
        "H3_COERCIVITY",
        "H4_RIGIDITY",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    ]:
        assert by_id[gate]["status"] == "open"
    assert assumptions(by_id["UPTCR_IMPLIES_MLC"]) == [
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE"
    ]
    print(
        f"Lean ledger mirror: {len(records)} nodes, {edge_count} dependencies, "
        f"{hyp_edge_count} conditional edges, {conditional_count} conditional "
        f"paper-proved rows, {len(ready_open)} first-frontier open goals; OK"
    )


if __name__ == "__main__":
    main()
