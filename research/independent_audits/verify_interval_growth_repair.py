#!/usr/bin/env python3
"""Exact finite regressions for the marked-contour interval-growth repair.

No floating point, no network access, and no third-party dependencies.
These checks are NOT an analytic proof or a realization of a KKL wave.

Run from a repository root:
    python research/independent_audits/verify_interval_growth_repair.py
    python research/independent_audits/verify_interval_growth_repair.py --check-manifest
    python research/independent_audits/verify_interval_growth_repair.py --write-manifest
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
import itertools
import json
from pathlib import Path
from typing import Optional


@dataclass(frozen=True, order=True)
class Interval:
    start: int
    length: int


# None denotes the ENTIRE circle; Interval(s, M) is the punctured circle
# with the marked point before s removed. These are deliberately different.
State = Optional[Interval]


def atoms(i: Interval, m: int) -> tuple[int, ...]:
    if m < 1 or not 0 <= i.start < m or not 1 <= i.length <= m:
        raise ValueError("Invalid cyclic interval")
    return tuple((i.start + j) % m for j in range(i.length))


def contained(small: Interval, large: Interval, m: int) -> bool:
    """Containment of OPEN arcs, retaining endpoints even for length M."""
    offset = (small.start - large.start) % m
    return offset + small.length <= large.length


@dataclass(frozen=True)
class Contour:
    words: tuple[tuple[int, ...], ...]
    weights: tuple[int, ...]
    expansion: Fraction

    @property
    def m(self) -> int:
        return len(self.words)

    def validate(self) -> None:
        if len(self.weights) != self.m or any(w < 0 for w in self.weights):
            raise ValueError("Weights must be nonnegative and label every atom")
        if self.expansion <= 1 or not any(self.weights):
            raise ValueError("Need strict expansion and a positive-weight atom")
        word = tuple(itertools.chain.from_iterable(self.words))
        if any(not part for part in self.words):
            raise ValueError("An atom must have a nonempty image")
        if any(not 0 <= x < self.m for x in word):
            raise ValueError("Invalid target label")
        if len(word) != 2 * self.m:
            raise ValueError("The test contour must have degree two")
        if any((word[j] + 1) % self.m != word[(j + 1) % len(word)]
               for j in range(len(word))):
            raise ValueError("Words must concatenate in positive cyclic order")

    def image(self, i: State) -> State:
        if i is None:
            return None
        word = tuple(x for a in atoms(i, self.m) for x in self.words[a])
        # EXACTLY one turn, with both endpoints omitted, is a punctured circle.
        if len(word) > self.m:
            return None
        return Interval(word[0], len(word))

    def mass(self, i: Interval) -> int:
        return sum(self.weights[a] for a in atoms(i, self.m))

    def states(self) -> list[Interval]:
        return [Interval(s, k) for s in range(self.m)
                for k in range(1, self.m + 1)]


def check_counting(max_m: int = 32) -> dict:
    cases = 0
    for m in range(2, max_m + 1):
        for r in range(1, m):
            critical = set(range(r))
            for k in range(1, m + 1):
                actual = sum(bool(set(atoms(Interval(s, k), m)) & critical)
                             for s in range(m))
                expected = min(m, r + k - 1)
                assert actual == expected, (m, r, k, actual, expected)
                cases += 1
        # All M punctured circles have the same atom set but differ as open sets.
        for a in range(m):
            for b in range(m):
                assert contained(Interval(a, m), Interval(b, m), m) == (a == b)
    return {"max_atoms": max_m, "critical_runs_tested": "1 <= r < M",
            "count_triples": cases,
            "formula": "min(M, r + k - 1)",
            "rotation_reduction": "critical run starts at 0 by cyclic symmetry"}


def proper_orbit(c: Contour, start: Interval) -> list[Interval]:
    result: list[Interval] = []
    seen: set[Interval] = set()
    i: State = start
    while i is not None:
        if i in seen:
            raise ValueError(f"Proper periodic state: {i}")
        seen.add(i)
        result.append(i)
        i = c.image(i)
    return result


def verify_positive_model() -> dict:
    # A standalone degree-two contour substitution. It is not certified here
    # to arise from any polynomial, a native KL pseudo-piece, or actual wave.
    c = Contour(
        words=((5,), (6, 7, 8), (9,), (0,), (1, 2),
               (3, 4, 5, 6, 7), (8, 9), (0,), (1,), (2, 3, 4)),
        weights=(0, 3, 2, 0, 3, 0, 3, 0, 2, 3),
        expansion=Fraction(3, 2),
    )
    c.validate()
    states = c.states()
    orbits = {i: proper_orbit(c, i) for i in states}
    proper_transitions = 0
    for i in states:
        j = c.image(i)
        if j is not None:
            assert j.length >= i.length
            assert c.mass(j) >= c.expansion * c.mass(i)
            proper_transitions += 1
    zero_steps = {}
    for i in states:
        if c.mass(i) == 0:
            for step, j in enumerate(orbits[i]):
                if c.mass(j) > 0:
                    zero_steps[f"{i.start}:{i.length}"] = step
                    break
            else:
                zero_steps[f"{i.start}:{i.length}"] = len(orbits[i])

    # Exhaust EVERY positive-time transition followed by arbitrary enlargement,
    # not only consecutive exact images. Retain only critical meeting states.
    critical = set(range(2, 9))
    eligible = [i for i in states if set(atoms(i, c.m)) & critical]
    edges: dict[Interval, set[Interval]] = {i: set() for i in eligible}
    for i in eligible:
        for iterate in orbits[i][1:]:
            for j in eligible:
                if contained(iterate, j, c.m):
                    edges[i].add(j)
    active: set[Interval] = set()
    done: dict[Interval, int] = {}

    def longest(i: Interval) -> int:
        if i in active:
            raise AssertionError("Cycle after allowing positive-time enlargement")
        if i in done:
            return done[i]
        active.add(i)
        out = 1 + max((longest(j) for j in edges[i]), default=0)
        active.remove(i)
        done[i] = out
        return out

    max_chain = max(longest(i) for i in eligible)
    finite_count_bound = sum(min(c.m, len(critical) + k - 1)
                             for k in range(1, c.m + 1))
    assert max_chain <= finite_count_bound
    # Matrix orientation: rows = source physical edge, columns = target edge.
    matrix = ((0, 1, 1), (1, 0, 0), (1, 1, 0))
    w = (3, 2, 3)
    aw = tuple(sum(row[j] * w[j] for j in range(3)) for row in matrix)
    assert all(Fraction(aw[j], w[j]) >= Fraction(3, 2) for j in range(3))
    return {
        "scope": "abstract degree-two contour; no dynamical realization claimed",
        "words": c.words, "atom_weights": c.weights,
        "rational_expansion_lower_bound": "3/2",
        "row_source_edge_matrix": matrix, "edge_weights": w, "A_times_w": aw,
        "proper_states": len(states), "proper_one_step_transitions": proper_transitions,
        "all_proper_orbits_saturate": True,
        "max_steps_to_whole_circle": max(map(len, orbits.values())),
        "saturation_histogram": dict(sorted(Counter(map(len, orbits.values())).items())),
        "zero_mass_escape_steps": zero_steps,
        "critical_atoms": sorted(critical),
        "all_time_enlargement_edges": sum(map(len, edges.values())),
        "max_critical_enlargement_chain_states": max_chain,
        "finite_state_chain_bound": finite_count_bound,
    }


def verify_negative_controls() -> dict:
    # Degree two and expanding positive-edge weights do NOT by themselves
    # exclude an invariant zero-weight atom. This is not a native KKL example.
    c = Contour(words=((0,), (1, 2), (0, 1, 2)),
                weights=(0, 1, 1), expansion=Fraction(2))
    c.validate()
    for i in c.states():
        j = c.image(i)
        if j is not None:
            assert j.length >= i.length
            assert c.mass(j) >= 2 * c.mass(i)
    fixed = Interval(0, 1)
    assert c.image(fixed) == fixed and c.mass(fixed) == 0
    assert c.image(None) is None
    assert c.image(Interval(2, 1)) == Interval(0, 3)
    assert c.image(Interval(0, 3)) is None
    return {
        "missing_zero_escape": {"words": c.words, "weights": c.weights,
                                "expansion": "2", "fixed_proper_state": [0, 1],
                                "native_dynamical_counterexample": False},
        "whole_circle_is_fixed": True,
        "one_turn_is_punctured_not_whole": True,
        "source_literal_counterexample":
            "The native full boundary C is fixed. At n=6b+M-1 it has 6b+M visits and no length growth.",
    }


def verify_vertex_count_patterns() -> dict:
    count = 0
    max_p = 9
    for p in range(2, max_p + 1):
        # Exhaust all possible sequences a_1 <= ... <= a_0 of values 1,2
        # with a_1=1; these are the sequences after the proved leaf argument.
        for cut in range(1, p + 1):
            seq = (1,) * cut + (2,) * (p - cut)
            assert seq[0] == 1 and all(a <= b for a, b in zip(seq, seq[1:]))
            if seq[-1] == 1:
                # Critical degree two produces an unoccupied inverse gate.
                assert 2 * seq[0] > seq[-1]
            else:
                increases = [j for j in range(p - 1) if seq[j] < seq[j + 1]]
                assert len(increases) == 1 and seq[increases[0]] == 1
            count += 1
    return {"periods": [2, max_p], "normalized_attachment_patterns": count,
            "scope": "finite integer pattern check, not prime-end realization"}


def verify_bound_arithmetic() -> dict:
    for b in range(1, 1001):
        total = sum(6 * b + k - 1 for k in range(1, 12 * b))
        assert total == (12 * b - 1) ** 2
        assert 216 * b * b - 1 > total
    return {"b_tested": [1, 1000],
            "short_critical_state_bound": "(12b-1)^2",
            "excluded_wave_chain_length": "(12b-1)^2+2",
            "published_excluded_length": "216b^2",
            "universal_proof": "algebraic derivation in companion note"}


def build_manifest() -> dict:
    return {
        "schema_version": 1,
        "date": "2026-11-06",
        "target": "KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR",
        "status": "partial repair; native marked-boundary identification not certified",
        "ledger_status_changes": [],
        "counting": check_counting(),
        "positive_contour": verify_positive_model(),
        "negative_controls": verify_negative_controls(),
        "vertex_counts": verify_vertex_count_patterns(),
        "bounds": verify_bound_arithmetic(),
        "trust_boundary": "Exact finite arithmetic and enumerations only. No proof of MLC, native analytic transport, or universal realization.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write-manifest", action="store_true")
    group.add_argument("--check-manifest", action="store_true")
    parser.add_argument("--manifest", type=Path,
                        default=Path(__file__).resolve().parents[2] /
                        "results" / "interval_growth_repair_20261106.json")
    args = parser.parse_args()
    text = json.dumps(build_manifest(), indent=2, sort_keys=True) + "\n"
    if args.write_manifest:
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(text, encoding="utf-8")
    if args.check_manifest:
        if not args.manifest.is_file():
            raise SystemExit(f"Missing manifest: {args.manifest}")
        if args.manifest.read_text(encoding="utf-8") != text:
            raise SystemExit("Manifest differs from exact regeneration")
    print(text, end="")


if __name__ == "__main__":
    main()
