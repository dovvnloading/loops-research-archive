#!/usr/bin/env python3
"""Exact integer regressions for the critical-root closed-crest counting theorem.

These checks test FINITE CYCLIC MARKINGS, not a holomorphic KKL pullback.
They are reproducible without floating point, network, or dependencies.

    python research/independent_audits/verify_root_stalk_sieve.py --check-manifest
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve()
MANIFEST = HERE.parents[2] / "results" / "root_stalk_sieve_20261106.json"


def meets_critical(start: int, length: int, atoms: int, critical: int) -> bool:
    """Nonempty overlap of two open, consecutively atom-marked arcs."""
    return any((start + j) % atoms < critical for j in range(length))


def closed_contains_cut(start: int, length: int, atoms: int, cut: int) -> bool:
    """BOTH endpoint cuts are included in the closed crest."""
    return (cut - start) % atoms <= length


def open_contains_cut(start: int, length: int, atoms: int, cut: int) -> bool:
    """Only INTERNAL cuts belong to the open interval core."""
    return 0 < (cut - start) % atoms < length


def contains_atom(start: int, length: int, atoms: int, atom: int) -> bool:
    return (atom - start) % atoms < length


def verify_counts(max_atoms: int = 40) -> dict:
    count_cases = 0
    count_intervals = 0
    count_cut_roots = 0
    count_atom_roots = 0
    open_closed_boundary_differences = 0
    for m in range(2, max_atoms + 1):
        for r in range(1, m):
            for k in range(1, m - r + 1):
                eligible = [
                    s for s in range(m) if meets_critical(s, k, m, r)
                ]
                count_intervals += len(eligible)
                assert len(eligible) == r + k - 1, ("critical", m, r, k, eligible)
                for h in range(r + 1):
                    closed = sum(
                        closed_contains_cut(s, k, m, h) for s in eligible
                    )
                    open_ = sum(
                        open_contains_cut(s, k, m, h) for s in eligible
                    )
                    expected_closed = k + (1 if 0 < h < r else 0)
                    expected_open = k - 1
                    assert closed == expected_closed, (
                        "cut-closed", m, r, k, h, closed
                    )
                    assert open_ == expected_open, (
                        "cut-open", m, r, k, h, open_
                    )
                    assert len(eligible) - closed == r - (
                        2 if 0 < h < r else 1
                    )
                    assert closed - open_ == (2 if 0 < h < r else 1)
                    open_closed_boundary_differences += closed - open_
                    count_cut_roots += 1
                for t in range(r):
                    affected = sum(
                        contains_atom(s, k, m, t) for s in eligible
                    )
                    assert affected == k, ("atom", m, r, k, t, affected)
                    assert len(eligible) - affected == r - 1
                    count_atom_roots += 1
                count_cases += 1

    # The k <= M-r hypothesis is essential, not cosmetic.
    m, r, k, h = 4, 3, 3, 1
    eligible = [
        s for s in range(m) if meets_critical(s, k, m, r)
    ]
    survivors = sum(
        not closed_contains_cut(s, k, m, h) for s in eligible
    )
    assert survivors == 0 and survivors != r - 2

    return {
        "theorem": "closed critical-root sieve for finite cyclic marked intervals",
        "max_atoms_exhaustive": max_atoms,
        "case_triples": count_cases,
        "critical_intervals_scanned": count_intervals,
        "cut_root_cases": count_cut_roots,
        "atom_root_cases": count_atom_roots,
        "total_open_closed_cut_difference": open_closed_boundary_differences,
        "regime": "1 <= r < M; 1 <= k <= M-r; root in closed critical limb",
        "critical_meeting_count": "r+k-1",
        "survivors_root_internal_cut": "r-2",
        "survivors_root_outer_cut": "r-1",
        "survivors_root_atom": "r-1",
        "closure_extra_forbidden_internal_cut": 2,
        "closure_extra_forbidden_outer_cut": 1,
        "outside_regime_counterexample": {
            "M": m, "r": r, "k": k, "root_cut": h,
            "survivors": survivors, "incorrect_extrapolation": r - 2,
        },
    }


def verify_parabolic_range(max_b: int = 1000) -> dict:
    # Extremal arithmetic establishes the ENTIRE box of b,q,r,k values.
    checked = 0
    for b in range(1, max_b + 1):
        min_q = 24 * b
        max_r = 6 * b
        max_k = 12 * b - 1
        assert max_k < min_q - max_r
        assert max_r >= 1 and max_k >= 1
        assert max_r - 1 <= 6 * b - 1
        assert max_r - 2 <= 6 * b - 2
        checked += max_r * max_k
    return {
        "max_b": max_b,
        "symbolic_r_k_cases_implied": checked,
        "extremal_inequality": "12*b-1 < 24*b-6*b <= M-r",
        "short_length_range": "1 <= k < 12*b",
        "large_rotation_range": "q >= 24*b; M >= q; r <= 6*b",
        "root_cut_candidate_cap": "(r-2)*(12*b-1)",
        "root_atom_or_outer_cut_candidate_cap": "(r-1)*(12*b-1)",
        "visit_transition_cap_conditional": (
            "candidate cap, if proper length monotone and no proper critical-return cycles"
        ),
    }


def compute_manifest() -> dict:
    return {
        "schema_version": 1,
        "provenance": "finite integer checks only; no native KKL analytic verification",
        "counting": verify_counts(),
        "high_rotation": verify_parabolic_range(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write-manifest", action="store_true")
    group.add_argument("--check-manifest", action="store_true")
    opts = parser.parse_args()
    output = json.dumps(compute_manifest(), indent=2, sort_keys=True) + "\n"
    if opts.write_manifest:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(output, encoding="utf-8")
        print(f"Wrote {MANIFEST}")
    elif opts.check_manifest:
        assert MANIFEST.read_text(encoding="utf-8") == output, (
            "Manifest differs from exact recomputation"
        )
        print(f"PASS: exhaustive exact counts and manifest {MANIFEST.name}")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
