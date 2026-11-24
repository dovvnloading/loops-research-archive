#!/usr/bin/env python3
"""Replay only the finite inputs of NOTE.md; no analytic certification.

The upstream script derives the blocks from the physical cut order and
covering alignment. This consumer checks the exact source-eligible grammar
(original multi-intervals and their closures), including punctured circles.
"""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import runpy
import sys


ROOT = Path(__file__).resolve().parents[3]
UPSTREAM = ROOT / "research/independent_audits/immersion_mark_resolution_20261124/verify.py"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


with contextlib.redirect_stdout(io.StringIO()):
    upstream = runpy.run_path(str(UPSTREAM))

lifted_cut = upstream["lifted_cut"]
blocks = upstream["blocks"]


def push(arc: tuple[int, int, str] | None) -> tuple[int, int, str] | None:
    """None is the entire circle; type is open or closed, never half-open."""
    if arc is None:
        return None
    start, length, kind = arc
    require(kind in ("open", "closed"), "outside source Proposition 6.5 grammar")
    require(0 <= start < 10 and 0 < length <= 10, "invalid marked arc")
    require(not (kind == "closed" and length == 10), "closed full turn must be None")
    left = lifted_cut(start)
    span = lifted_cut(start + length) - left
    if span > 10 or (span == 10 and kind == "closed"):
        return None
    return left % 10, span, kind


rows = []
for kind in ("open", "closed"):
    for start in range(10):
        for length in range(1, 11 if kind == "open" else 10):
            state = (start, length, kind)
            orbit = [list(state)]
            while state is not None:
                state = push(state)
                orbit.append(None if state is None else list(state))
                require(len(orbit) <= 6, "marked input did not saturate within five pushes")
            rows.append({"start": start, "length": length, "kind": kind,
                         "saturation_steps": len(orbit) - 1, "orbit": orbit})

rows.append({"kind": "circle", "saturation_steps": 0, "orbit": [None]})
require(len(rows) == 191, "source-eligible input count changed")
require(max(row["saturation_steps"] for row in rows) == 5, "five-step bound not sharp")
atom_times = [next(row["saturation_steps"] for row in rows
                   if row.get("start") == start and row.get("length") == 1
                   and row["kind"] == "open") for start in range(10)]
require(atom_times == [2, 4, 4, 5, 4, 3, 4, 5, 4, 4], "open atom clock changed")

# Same atom support, different endpoint inclusion: exactly one open turn
# omits a point, whereas one closed turn includes the entire circle.
halfturns = []
for start in range(10):
    for length in range(1, 10):
        if lifted_cut(start + length) - lifted_cut(start) == 10:
            opened = push((start, length, "open"))
            closed = push((start, length, "closed"))
            require(opened is not None and opened[1] == 10, "lost punctured-circle endpoint")
            require(closed is None, "closed turn did not cover circle")
            require(push(opened) is None, "punctured circle failed next-step saturation")
            halfturns.append([start, length])
require(halfturns == [[2, 6], [3, 6], [8, 4], [9, 4]], "endpoint regression inputs changed")

# The analytic identification of these limbs is in NOTE.md. This is only
# the finite source-clause census once that identification is supplied.
q, b = 2, 2
limbs = {0: ["K0", "K2"], 1: ["K1"]}
images = {"K0": "K1", "K1": "K2", "K2": "K0"}
require(max(map(len, limbs.values())) <= b, "source limb occupancy clause fails")
window = {j % q for j in range(-b, b + 1)}
require(window == {0, 1}, "source critical-window clause fails")
for phase in limbs[0]:
    target = images[phase]
    require(any(target in limbs[j] for j in window), "critical component leaves source window")

report = {
    "scope": "exact finite source-eligible marked inputs; independent topology is written; native application imports KKL 6.5, 6.6 and A.14",
    "source_arxiv": "2606.27272v1",
    "source_propositions": {"6.5": 42, "6.6": 43, "A.14": 65},
    "q": q, "b": b, "limb_components": {str(k): v for k, v in limbs.items()},
    "blocks": {str(k): blocks[k] for k in range(10)},
    "source_eligible_inputs": len(rows),
    "max_saturation_steps": 5,
    "open_atom_saturation_steps": atom_times,
    "open_exact_turn_regressions": halfturns,
    "rows": rows,
}
if "--write-manifest" in sys.argv:
    Path(__file__).with_name("certificate.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
if "--check-manifest" in sys.argv:
    expected = json.loads(Path(__file__).with_name("certificate.json").read_text(encoding="utf-8"))
    require(expected == report, "certificate drift")
print(json.dumps({k: v for k, v in report.items() if k != "rows"}, indent=2))
