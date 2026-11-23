#!/usr/bin/env python3
"""Exact SCC/cycle and characteristic-polynomial certificate for the REAL spine.

Standard library only.  The physical interval interpretation is proved in
Period27RealMarkov.lean; this script independently checks finite graph algebra.
It does not identify the matrix with a native KKL tree or the clone graph.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "results/period27_symbolic_marking.json"
MANIFEST = ROOT / "results/period27_real_markov_spectrum.json"
LEAN = ROOT / "formalization/weighted/Period27RealMarkov.lean"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def multiply(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def reachable(rows: list[list[int]], start: int) -> set[int]:
    seen, todo = {start}, [start]
    while todo:
        for nxt in rows[todo.pop()]:
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return seen


def characteristic_from_traces(rows: list[list[int]]) -> list[int]:
    """Newton identities for det(lambda I-A); returns ascending coefficients.

    Matrix powers and traces use Python integers.  Every division by k is
    required to be exact, so no numerical eigenvalue computation is involved.
    """
    size = len(rows)
    power = [[int(i == j) for j in range(size)] for i in range(size)]
    traces: list[int] = []
    descending = [1]
    for k in range(1, size + 1):
        # A times power, using the explicitly row-source adjacency.
        power = [[sum(power[j][col] for j in rows[i])
                  for col in range(size)] for i in range(size)]
        traces.append(sum(power[i][i] for i in range(size)))
        numerator = sum(descending[k - j] * traces[j - 1]
                        for j in range(1, k + 1))
        require(numerator % k == 0, f"Newton division by {k} is not integral")
        descending.append(-numerator // k)
    return list(reversed(descending))


def cycle_certificate(rows: list[list[int]], component: list[int]) -> dict:
    inside = set(component)
    restricted = {i: [j for j in rows[i] if j in inside] for i in component}
    branching = [i for i in component if len(restricted[i]) != 1]
    require(len(branching) == 1, "component must have one branching vertex")
    branch = branching[0]
    require(len(restricted[branch]) == 2, "branch must have two successors")
    # Every other vertex reaches the branch without a second cycle.
    for start in component:
        visited, cursor = set(), start
        while cursor != branch:
            require(cursor not in visited, "cycle avoiding branch")
            visited.add(cursor)
            cursor = restricted[cursor][0]
    cycles = []
    for first in restricted[branch]:
        cycle, cursor = [branch, first], first
        while cursor != branch:
            require(cursor not in cycle[:-1], "non-simple return cycle")
            cursor = restricted[cursor][0]
            cycle.append(cursor)
        cycles.append(cycle)
    cycles.sort(key=len)
    lengths = [len(cycle) - 1 for cycle in cycles]
    delay = len(component) // 2
    require(len(component) == 2 * delay and lengths == [delay, 2 * delay],
            "component is not the claimed two-cycle renewal block")
    factor = [0] * (2 * delay + 1)
    factor[0], factor[delay], factor[2 * delay] = -1, -1, 1
    return {"vertices": component, "branch_vertex": branch,
            "first_return_cycles": cycles, "cycle_lengths": lengths,
            "delay": delay, "factor_coefficients_ascending": factor}


def interval_phase_certificate(rows: list[list[int]], period: int, width: int,
                               order: list[int]) -> dict:
    blocks = [list(range(k * (width + 1), k * (width + 1) + width))
              for k in range(period)]
    targets = []
    for block in blocks:
        image = sorted({target for edge in block for target in rows[edge]})
        require(image in blocks, "whole interval image is not a declared phase interval")
        targets.append(blocks.index(image))
    require(sorted(targets) == list(range(period)), "phase action is not a permutation")
    visited, cursor = set(), 0
    while cursor not in visited:
        visited.add(cursor)
        cursor = targets[cursor]
    require(cursor == 0 and len(visited) == period, "phase permutation is not one full cycle")
    endpoints = [[block[0], block[-1] + 1] for block in blocks]
    return {"period": period, "edge_blocks": blocks, "vertex_rank_intervals": endpoints,
            "orbit_time_endpoints": [[order[a], order[b]] for a, b in endpoints],
            "image_interval_permutation": targets}


def build_certificate() -> dict:
    source = json.loads(SOURCE.read_text(encoding="utf-8"))["real_interval_markov_spine"]
    order, rows = source["ordered_orbit_indices"], source["edge_destinations"]
    require(sorted(order) == list(range(27)), "orbit order is not a permutation")
    position = {orbit_time: rank for rank, orbit_time in enumerate(order)}
    derived = [list(range(*sorted((position[(a + 1) % 27], position[(b + 1) % 27]))))
               for a, b in zip(order, order[1:])]
    require(rows == derived, "rows disagree with endpoint permutation")
    row_bytes = json.dumps(rows, separators=(",", ":"), ensure_ascii=True).encode()
    row_hash = hashlib.sha256(row_bytes).hexdigest()
    require(row_hash == source["edge_adjacency_sha256"], "source row hash mismatch")
    lean_match = re.search(r"theorem markovRows_exact : markovRows =\s*(\[\[.*?\]\]) := by",
                           LEAN.read_text(encoding="utf-8"), flags=re.DOTALL)
    require(lean_match is not None, "Lean row statement not found")
    require(ast.literal_eval(lean_match.group(1)) == rows, "Lean rows differ from source")
    reach = [reachable(rows, i) for i in range(26)]
    components, seen = [], set()
    for i in range(26):
        if i not in seen:
            component = [j for j in range(26) if j in reach[i] and i in reach[j]]
            components.append(component)
            seen.update(component)
    components.sort(key=len)  # Here this is the source-to-sink SCC order.
    require([len(c) for c in components] == [2, 6, 18], "unexpected SCC dimensions")
    block = {vertex: k for k, comp in enumerate(components) for vertex in comp}
    require(all(block[i] <= block[j] for i, row in enumerate(rows) for j in row),
            "SCC order is not block upper triangular")
    certificates = [cycle_certificate(rows, comp) for comp in components]
    factored = [1]
    for certificate in certificates:
        factored = multiply(factored, certificate["factor_coefficients_ascending"])
    by_traces = characteristic_from_traces(rows)
    require(factored == by_traces, "cycle factorization differs from trace calculation")
    phase3 = interval_phase_certificate(rows, 3, 8, order)
    phase9 = interval_phase_certificate(rows, 9, 2, order)
    require(all(phase3["vertex_rank_intervals"][i // 3][0] <=
                phase9["vertex_rank_intervals"][i][0] <
                phase9["vertex_rank_intervals"][i][1] <=
                phase3["vertex_rank_intervals"][i // 3][1] for i in range(9)),
            "fine physical intervals are not nested in coarse intervals")
    require(all(phase9["image_interval_permutation"][i] // 3 ==
                phase3["image_interval_permutation"][i // 3] for i in range(9)),
            "physical interval refinement fails to commute")
    return {"schema": "period27-real-markov-spectrum-v1",
            "matrix_orientation": "row source, column destination, multiplicity 0 or 1",
            "source_edge_adjacency_sha256": row_hash,
            "physical_bridge": "LoopsRealPeriod27.Markov.row_iff_unique_physical_preimage",
            "components_in_block_order": certificates,
            "invariant_interval_families": [phase3, phase9],
            "characteristic_coefficients_ascending": by_traces,
            "characteristic_factorization": "(x^2-x-1)(x^6-x^3-1)(x^18-x^9-1)",
            "scope": "Actual real-interval Markov spine after the Lean bridge; not a native KKL or clone-graph identification.",
            "verification": "Exact integer SCC/cycle enumeration and independent Newton trace identities; determinant argument is written, not Lean-formalized."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-manifest", action="store_true")
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()
    report = build_certificate()
    content = json.dumps(report, sort_keys=True, indent=2, ensure_ascii=True) + "\n"
    if args.check_manifest:
        require(MANIFEST.read_text(encoding="utf-8") == content, "stale spectrum manifest")
    if args.print_json:
        print(content, end="")
    else:
        print("PASS: exact physical-spine finite spectrum certificate")
        print("  SCC dimensions: 2, 6, 18; return-cycle lengths: (1,2), (3,6), (9,18)")
        print("  det(xI-A) =", report["characteristic_factorization"])
        print("  cycle-cover factors agree with independent integer trace identities")
        print("  physical matrix interpretation: Period27RealMarkov.lean")
        print("  determinant calculation: exact Python plus written proof, not Lean")


if __name__ == "__main__":
    main()
