#!/usr/bin/env python3
"""Exact finite inputs and cross-checks for the physical octal reconstruction.

The physical equality is the written entropy/degree argument in README.md.
This program checks rational maps, complete finite cylinder enclosures, the
old graph's recurrent component, and rational membership.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
DIGITS = (3, 4)
HULL = (F(3, 7), F(4, 7))
PHASES = {0: ((0, 2), (1, 2)), 1: ((0, 1),),
          2: ((0, 4), (3, 4))}
SHIFTS = (3, 4, 11, 12)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rational_address(x: F) -> dict:
    """Decide membership in C for a rational, retaining a complete witness."""
    if not 0 <= x < 1:
        return {"in_C": False, "reason": "outside [0,1)"}
    seen: dict[F, int] = {}
    digits = []
    remainder = x
    while remainder not in seen:
        seen[remainder] = len(digits)
        value = 8 * remainder
        digit = value.numerator // value.denominator
        if digit not in DIGITS:
            return {"in_C": False, "accepted_prefix": digits,
                    "first_forbidden_digit": digit,
                    "first_forbidden_position": len(digits) + 1}
        digits.append(digit)
        remainder = value - digit
    start = seen[remainder]
    return {"in_C": True, "prefix": digits[:start],
            "period": digits[start:]}


def phase_membership(theta: F) -> list[int]:
    return [j for j, copies in PHASES.items()
            if any(rational_address(den * theta - shift)["in_C"]
                   for shift, den in copies)]


def affine(interval: tuple[F, F], shift: int, den: int) -> tuple[F, F]:
    return tuple((x + shift) / den for x in interval)


def cylinder_hulls(depth: int) -> list[tuple[F, F]]:
    hulls = [HULL]
    for _ in range(depth):
        hulls = [affine(interval, digit, 8)
                 for digit in DIGITS for interval in hulls]
    return sorted(hulls)


def grid_cell(interval: tuple[F, F]) -> int | None:
    lo, hi = (768 * x for x in interval)
    if lo.denominator == 1 or hi.denominator == 1:
        return None
    left, right = lo.numerator // lo.denominator, hi.numerator // hi.denominator
    return left if left == right else None


def reconstruct_graph() -> dict:
    """Enclose all actual cylinders, not a finite sample of their points."""
    for depth in range(1, 10):
        edges: dict[int, set[int]] = {}
        phase_cells = {j: set() for j in PHASES}
        valid = True
        for j, copies in PHASES.items():
            for shift, den in copies:
                for interval in cylinder_hulls(depth):
                    source = affine(interval, shift, den)
                    lo, hi = (2 * x for x in source)
                    winding = lo.numerator // lo.denominator
                    if hi.numerator // hi.denominator != winding:
                        valid = False
                        break
                    target = (lo - winding, hi - winding)
                    i, k = grid_cell(source), grid_cell(target)
                    if i is None or k is None:
                        valid = False
                        break
                    phase_cells[j].add(i)
                    edges.setdefault(i, set()).add(k)
                if not valid:
                    break
            if not valid:
                break
        if valid:
            return {"cylinder_depth": depth,
                    "phase_cells": {str(j): sorted(v) for j, v in phase_cells.items()},
                    "edges": {str(i): sorted(edges[i]) for i in sorted(edges)}}
    raise ValueError("Cylinders failed to separate from the 768-grid")


def verify(repo: Path = ROOT) -> dict:
    atlas_path = repo / "results/tip_kl_side_atlas.json"
    atlas_raw = atlas_path.read_bytes()
    atlas = json.loads(atlas_raw)
    stage = next(v for v in atlas["stages"] if v["stage"] == "G")
    seams = [tuple(map(F, t["seam_stage_angles"]))
             for t in stage["pieces"]["W"]["tiles"]]
    require(seams == [(F(41, 192), F(43, 192)),
                      (F(53, 192), F(55, 192)),
                      (F(137, 192), F(139, 192)),
                      (F(149, 192), F(151, 192))], "Source seam atlas changed")
    doubled = sorted(set(tuple(2 * x - int(2 * interval[0]) for x in interval)
                         for interval in seams))
    require(doubled == [(F(41, 96), F(43, 96)),
                        (F(53, 96), F(55, 96))], "Incorrect doubled seam set")
    for digit, interval in zip(DIGITS, doubled):
        require(F(digit, 8) < interval[0] < interval[1] < F(digit + 1, 8),
                "A doubled seam is not strictly inside its octal digit cell")
        child = affine(HULL, digit, 8)
        require(interval[0] < child[0] <= child[1] < interval[1],
                "An octal first cylinder leaves the physical sector bound")

    seam_rows = []
    for i, (shift, seam) in enumerate(zip(SHIFTS, seams)):
        hull = affine(HULL, shift, 16)
        margins = (hull[0] - seam[0], seam[1] - hull[1])
        require(margins == (F(1, 1344), F(1, 1344)), "Wrong seam clearance")
        require(hull[1] - hull[0] == F(1, 112), "Wrong root hull diameter")
        require(all(phase_membership(x) == [0] for x in hull),
                "A rational root endpoint has the wrong physical phase")
        seam_rows.append({"seam": i, "shift": shift, "denominator": 16,
                          "hull": list(map(str, hull)),
                          "clearance": list(map(str, margins))})

    graph = reconstruct_graph()
    old_path = repo / "research/independent_audits/issue62_landing_angle_bound_20261123/certificate.json"
    old_raw = old_path.read_bytes()
    old = json.loads(old_raw)
    core = set(old["cyclic_component"])
    all_edges = {int(i): v for i, v in old["edges_in_grid_indices"].items()}
    expected = {str(i): [j for j in all_edges[i] if j in core] for i in sorted(core)}
    require(graph["edges"] == expected, "Actual octal reconstruction disagrees with recurrent graph")
    require(len(expected) == 32 and sum(map(len, expected.values())) == 40,
            "Incorrect recurrent graph size")
    phase_cells = {int(j): set(v) for j, v in graph["phase_cells"].items()}
    require([len(phase_cells[j]) for j in range(3)] == [16, 8, 8],
            "Incorrect phase cell counts")
    require(all(i // 96 in {3, 4} for i in phase_cells[1]),
            "Phase-one core cells leave the two octal digit cells")
    require(all(i // 192 in {0, 3} for i in phase_cells[2]),
            "Phase-two core cells leave the two physical quarter cells")
    require(all(k in phase_cells[(j + 1) % 3]
                for j in range(3) for i in phase_cells[j] for k in expected[str(i)]),
            "Graph does not realize the physical three-phase order")
    for i in core:
        paths = [i]
        for _ in range(3):
            paths = [k for j in paths for k in expected[str(j)]]
        require(len(paths) == 2, "A three-step recurrent row is not binary")

    live = set(core)
    while True:
        new = live | {i for i, js in all_edges.items() if any(j in live for j in js)}
        if new == live:
            break
        live = new
    heights = {i: 0 for i in core}
    while set(heights) != live:
        ready = [i for i in live - heights.keys()
                 if all(j in heights for j in all_edges[i] if j in live)]
        require(bool(ready), "Unexpected recurrent component outside the core")
        for i in ready:
            heights[i] = 1 + max(heights[j] for j in all_edges[i] if j in live)
    require(Counter(heights.values()) == Counter({0: 32, 1: 16, 2: 16}),
            "Unexpected transient structure")

    intervals = sorted(((a + k) / 2**r, (b + k) / 2**r)
                       for r in range(3) for k in range(2**r) for a, b in seams)
    require(all(not any(a <= x <= b for a, b in intervals)
                for x in (F(0), F(1, 3), F(2, 3))),
            "Grid escape points meet the CLOSED survivor region")
    spurious = F(3, 56)
    require(any(a < spurious < b for a, b in intervals), "Counterexample leaves S")
    require(phase_membership(spurious) == [] and phase_membership(2 * spurious) == [2],
            "Spurious-survivor counterexample failed")

    cuts = [("root", F(249, 896), 0), ("D01", F(25, 56), 1),
            ("D02", F(25, 28), 2)]
    cut_rows = []
    for label, theta, phase in cuts:
        require(phase_membership(theta) == [phase], "Wrong actual phase of a ray cut")
        addresses = [{"shift": shift, "denominator": den,
                      "address": rational_address(den * theta - shift)}
                     for shift, den in PHASES[phase]
                     if rational_address(den * theta - shift)["in_C"]]
        cut_rows.append({"label": label, "angle": str(theta),
                         "physical_phase": phase, "addresses": addresses})
    require(rational_address(F(1, 2))["in_C"] is False,
            "The central octal gap was incorrectly filled")

    gap = (affine(HULL, 3, 8)[1], affine(HULL, 4, 8)[0])
    require(gap == (F(25, 56), F(31, 56)) and gap[1] - gap[0] == F(3, 28),
            "Incorrect primary gap")
    require((gap[1] - gap[0]) / (1 - F(2, 8)) == HULL[1] - HULL[0],
            "All-level gap-length sum does not exhaust the hull")

    return {
        "scope": "Finite exact arithmetic. Physical equality and entropy saturation are proved in README.md.",
        "sources": [{"path": str(path.relative_to(repo)),
                     "sha256": hashlib.sha256(raw).hexdigest()}
                    for path, raw in ((atlas_path, atlas_raw), (old_path, old_raw))],
        "octal_base": 8, "digits": list(DIGITS),
        "doubled_source_seams": [list(map(str, x)) for x in doubled],
        "cantor_hull": list(map(str, HULL)), "root_seams": seam_rows,
        "primary_gap": list(map(str, gap)),
        "level_k_gap_count": "2^k", "level_k_gap_length": "3/(28*8^k)",
        "actual_recurrent_graph": graph,
        "old_graph_live_vertex_count": len(live),
        "old_graph_dead_vertex_count": len(all_edges) - len(live),
        "old_graph_transient_heights": {str(k): v for k, v in sorted(Counter(heights.values()).items())},
        "strict_survivor_counterexample": {"angle": str(spurious),
                                           "double": str(2 * spurious), "double_phase": 2},
        "physical_cut_addresses": cut_rows,
        "hausdorff_measure_convention": "sum of diameter powers, s=1/3",
        "hausdorff_measure_C": "7^(-1/3)",
        "hausdorff_measure_each_Ai": "112^(-1/3)",
        "basic_log_capacity_bounds_C": [str(F(3, 224)), str(F(1, 56))],
        "basic_log_capacity_bounds_each_Ai": [str(F(3, 3584)), str(F(1, 896))],
        "analytic_status": "written, not Lean-formalized; finite checks do not certify the physical analytic inputs",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--certificate", type=Path)
    group.add_argument("--check-certificate", nargs="?", type=Path,
                       const=HERE / "certificate.json")
    args = parser.parse_args()
    result = verify()
    if args.certificate:
        args.certificate.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    if args.check_certificate:
        require(json.loads(args.check_certificate.read_text()) == result,
                "Committed octal certificate differs from exact recomputation")
    print("PASS: actual source seams imply octal digits 3/4; all four affine root hulls have clearance 1/1344.")
    print("PASS: full cylinder enclosures independently reconstruct 32 recurrent vertices and 40 edges.")
    print("PASS: each recurrent three-step row is binary; source phases have 16/8/8 grid cells.")
    print("PASS: all rational root-cut addresses, exact gap hierarchy, and strict survivor counterexample.")
    print("Analytic equality, entropy, measure and trace arguments are written in the companion notes.")
    if args.check_certificate:
        print("PASS: committed certificate matches every recomputed field.")


if __name__ == "__main__":
    main()
