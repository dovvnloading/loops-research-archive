#!/usr/bin/env python3
"""Exact arithmetic certificate for the Issue 62 external-angle upper bound.

Standard library only.  This verifies the finite arithmetic implications of the
archive's G:W seam data.  It does NOT certify the analytic landing, semiconjugacy,
or source-sector theorems that connect those data to the physical dynamical set.
See NOTE.md for that indispensable one-way implication and the boundary cases.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from math import lcm
from pathlib import Path


EXPECTED_SEAMS = (
    (Fraction(41, 192), Fraction(43, 192)),
    (Fraction(53, 192), Fraction(55, 192)),
    (Fraction(137, 192), Fraction(139, 192)),
    (Fraction(149, 192), Fraction(151, 192)),
)
EXPECTED_CYCLIC_COMPONENT = [
    82, 85, 106, 109, 164, 165, 170, 171,
    212, 213, 218, 219, 329, 330, 341, 342,
    425, 426, 437, 438, 548, 549, 554, 555,
    596, 597, 602, 603, 658, 661, 682, 685,
]


def require(condition: bool, message: str) -> None:
    """Assertions remain active even when Python is run with -O."""
    if not condition:
        raise ValueError(message)


def components(adjacency: list[list[int]]) -> list[list[int]]:
    """Tarjan's strongly connected components, in internal vertex numbering."""
    next_index = 0
    indices: dict[int, int] = {}
    lowlinks: dict[int, int] = {}
    stack: list[int] = []
    on_stack: set[int] = set()
    result: list[list[int]] = []

    def visit(v: int) -> None:
        nonlocal next_index
        indices[v] = lowlinks[v] = next_index
        next_index += 1
        stack.append(v)
        on_stack.add(v)
        for w in adjacency[v]:
            if w not in indices:
                visit(w)
                lowlinks[v] = min(lowlinks[v], lowlinks[w])
            elif w in on_stack:
                lowlinks[v] = min(lowlinks[v], indices[w])
        if lowlinks[v] == indices[v]:
            component = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                component.append(w)
                if w == v:
                    break
            result.append(sorted(component))

    for vertex in range(len(adjacency)):
        if vertex not in indices:
            visit(vertex)
    return sorted(result, key=lambda component: component[0])


def vector_step(adjacency: list[list[int]], vector: list[int]) -> list[int]:
    return [sum(vector[w] for w in row) for row in adjacency]


def matrix_step(adjacency: list[list[int]], matrix: list[list[int]]) -> list[list[int]]:
    """Right multiply a dense integer matrix by the sparse row-source A."""
    size = len(adjacency)
    product = [[0] * size for _ in range(size)]
    for source, row in enumerate(matrix):
        for middle, value in enumerate(row):
            if value:
                for target in adjacency[middle]:
                    product[source][target] += value
    return product


def verify(repo: Path) -> dict:
    source_path = repo / "results/tip_kl_side_atlas.json"
    raw = source_path.read_bytes()
    atlas = json.loads(raw)
    stage = next(stage for stage in atlas["stages"] if stage["stage"] == "G")
    tiles = stage["pieces"]["W"]["tiles"]
    seams = tuple(tuple(map(Fraction, tile["seam_stage_angles"])) for tile in tiles)
    require(seams == EXPECTED_SEAMS, "The source G:W seam data changed.")

    # d^(-r)(a,b) is the union of ((a+k)/2^r,(b+k)/2^r), 0<=k<2^r.
    intervals = sorted(
        ((a + k) / 2**r, (b + k) / 2**r)
        for r in range(3)
        for k in range(2**r)
        for a, b in seams
    )
    denominator = lcm(*(value.denominator for interval in intervals for value in interval))
    require(denominator == 768, "Unexpected common endpoint denominator.")
    require(len(intervals) == 28, "Unexpected number of inverse-image intervals.")
    require(all(0 <= a < b <= 1 for a, b in intervals), "Interval leaves [0,1].")
    require(
        all(left[1] < right[0] for left, right in zip(intervals, intervals[1:])),
        "This certificate expects strictly separated open survivor intervals.",
    )
    grid_eighth_images = {(256 * Fraction(i, denominator)) % 1
                          for i in range(denominator)}
    require(grid_eighth_images == {Fraction(0), Fraction(1, 3), Fraction(2, 3)},
            "The eighth image of the grid is not the expected three-point set.")
    require(all(not any(a < point < b for a, b in intervals)
                for point in grid_eighth_images),
            "A forward image of a grid endpoint lies in the open survivor region.")

    # All interval endpoints are grid points.  This closed-endpoint comparison
    # tests containment of the OPEN cell, not inclusion of its boundary points.
    vertices = [
        i for i in range(denominator)
        if any(a <= Fraction(i, denominator) and Fraction(i + 1, denominator) <= b
               for a, b in intervals)
    ]
    require(len(vertices) == 96, "Expected exactly 96 allowed open cells.")
    require(
        sum((b - a for a, b in intervals), Fraction(0)) == Fraction(1, 8),
        "Incorrect total length of the open survivor region.",
    )
    require(
        sum(int((b - a) * denominator) for a, b in intervals) == len(vertices),
        "Grid cells do not exhaust the open intervals up to grid endpoints.",
    )
    indices = {vertex: index for index, vertex in enumerate(vertices)}
    adjacency = [
        [indices[w] for w in ((2 * i) % denominator, (2 * i + 1) % denominator)
         if w in indices]
        for i in vertices
    ]
    require(sum(map(len, adjacency)) == 144, "Expected exactly 144 directed edges.")
    require(all(len(row) == len(set(row)) for row in adjacency), "Repeated edge.")

    sccs = components(adjacency)
    cyclic = [
        component for component in sccs
        if len(component) > 1 or component[0] in adjacency[component[0]]
    ]
    require(len(sccs) == 65, "Unexpected number of strongly connected components.")
    require(len(cyclic) == 1, "Expected exactly one component containing a cycle.")
    cyclic_labels = sorted(vertices[index] for index in cyclic[0])
    require(cyclic_labels == EXPECTED_CYCLIC_COMPONENT, "Cyclic component changed.")
    require(sum(len(component) for component in sccs if component not in cyclic) == 64,
            "Expected exactly 64 vertices outside the cyclic component.")

    # v_n = A^n * 1 counts n-edge paths beginning at each vertex.
    vectors = [[1] * len(vertices)]
    for _ in range(5):
        vectors.append(vector_step(adjacency, vectors[-1]))
    require(vectors[5] == [2 * value for value in vectors[2]],
            "Core identity A^5*1 = 2*A^2*1 failed.")
    totals = [sum(vector) for vector in vectors]
    require(totals == [96, 144, 192, 192, 288, 384], "Initial path counts changed.")
    require(totals[3] == 2 * totals[0] and totals[4] == 2 * totals[1],
            "The two exceptional scalar recurrence cases failed.")

    # Independent exact corroboration on the full adjacency matrix.  This is
    # not needed for the proof: the vector identity already gives all horizons.
    size = len(vertices)
    matrix = [[int(i == j) for j in range(size)] for i in range(size)]
    matrix10 = None
    for exponent in range(1, 14):
        matrix = matrix_step(adjacency, matrix)
        if exponent == 10:
            matrix10 = matrix
    require(matrix10 is not None, "Missing exponent-ten matrix.")
    require(matrix == [[2 * value for value in row] for row in matrix10],
            "Corroborating identity A^13 = 2*A^10 failed.")

    return {
        "scope": "Exact finite arithmetic only; physical inclusion requires the written analytic sources in NOTE.md.",
        "source": {
            "relative_path": "results/tip_kl_side_atlas.json",
            "sha256": hashlib.sha256(raw).hexdigest(),
            "stage": "G",
            "piece": "W",
            "tile_ids": [tile["id"] for tile in tiles],
            "open_seams": [[str(value) for value in interval] for interval in seams],
        },
        "denominator": denominator,
        "grid_endpoint_exclusion": {
            "grid_Q": "{j/768: 0 <= j < 768}",
            "d^8(Q)": [str(value) for value in sorted(grid_eighth_images)],
            "all_d^8_Q_outside_open_S": True,
            "consequence": "No point in any d^(-r)(Q) can survive in S forever; hence E is disjoint from their entire union.",
        },
        "open_S_intervals_in_grid_units": [[int(a * denominator), int(b * denominator)]
                                            for a, b in intervals],
        "allowed_open_cell_indices": vertices,
        "edges_in_grid_indices": {str(i): [vertices[w] for w in adjacency[k]]
                                   for k, i in enumerate(vertices)},
        "vertex_count": len(vertices),
        "edge_count": sum(map(len, adjacency)),
        "strongly_connected_components_in_grid_indices": [
            [vertices[index] for index in component] for component in sccs
        ],
        "cyclic_component": cyclic_labels,
        "acyclic_singleton_component_count": 64,
        "row_path_count_vectors": {str(n): vector for n, vector in enumerate(vectors)},
        "v2_level_sets_in_grid_indices": {
            str(value): [i for i, entry in zip(vertices, vectors[2]) if entry == value]
            for value in sorted(set(vectors[2]))
        },
        "v2_value_multiplicities": dict(sorted(Counter(vectors[2]).items())),
        "initial_total_path_counts_c0_through_c5": totals,
        "exact_vector_identity": "A^5 * 1 = 2 * A^2 * 1",
        "exact_matrix_corroboration": "A^13 = 2 * A^10",
        "all_horizon_recurrence": "c(n+3) = 2*c(n) for every integer n >= 0",
        "all_horizon_closed_formula": {
            "c(3k)": "96 * 2^k",
            "c(3k+1)": "144 * 2^k",
            "c(3k+2)": "192 * 2^k",
            "uniform_bound": "c(n) <= 192 * 2^(n/3) for every integer n >= 0",
        },
        "three_step_cover": {
            "number_at_depth_3k": "96 * 2^k",
            "interval_length_at_depth_3k": "1 / (768 * 8^k)",
            "total_length_at_depth_3k": "(1/8) * 4^(-k)",
            "endpoint_exclusion": "E avoids every backward iterate of Q because d^8(Q)={0,1/3,2/3} is disjoint from S; every stated cover covers all of E.",
        },
        "physical_conclusion_conditional_on_analytic_inputs": {
            "normalized_G_external_angle_Lebesgue_measure": "0",
            "normalized_G_external_angle_Hausdorff_dimension_upper_bound": "1/3",
            "normalized_G_external_angle_upper_box_dimension_upper_bound": "1/3",
            "not_claimed": [
                "Equality of the physical landing set and the graph survivor set",
                "A lower bound for the physical landing-set dimension",
                "A harmonic-measure, logarithmic-capacity or extremal-width conclusion",
                "A literal F9 connector word or the missing KKL proper-restriction correspondence",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    script_path = Path(__file__).resolve()
    parser.add_argument(
        "--repo", type=Path,
        default=script_path.parents[3],
        help="Path to the loops-research-archive checkout (read only).",
    )
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--certificate", type=Path,
                        help="Optional path at which to write the full JSON certificate.")
    output.add_argument("--check-certificate", nargs="?", type=Path,
                        const=script_path.with_name("certificate.json"),
                        help="Compare with the committed certificate, or a supplied path.")
    args = parser.parse_args()
    certificate = verify(args.repo)
    if args.check_certificate is not None:
        saved = json.loads(args.check_certificate.read_text())
        normalized = json.loads(json.dumps(certificate))
        require(saved == normalized, "The saved certificate differs from the exact calculation.")
    if args.certificate is not None:
        args.certificate.write_text(json.dumps(certificate, indent=2) + "\n")
    print("PASS: exact source seams; 768-grid; 96 allowed open cells; 144 directed edges.")
    print("PASS: d^8(Q) = {0,1/3,2/3} lies outside S; no grid preimage lies in E.")
    print("PASS: one 32-vertex cyclic SCC; 64 acyclic singleton SCCs; no other cycles.")
    print("PASS: A^5*1 = 2*A^2*1, c0..c5 = 96,144,192,192,288,384.")
    print("PASS: c(3k+r) = (96,144,192)[r] * 2^k for all k>=0, 0<=r<3.")
    print("PASS: independent full-matrix identity A^13 = 2*A^10.")
    print("CONDITIONAL PHYSICAL CONSEQUENCE: external-angle dim_H(E) <= upper_box_dim(E) <= 1/3; Leb(E) = 0.")
    print("Analytic inputs, endpoint treatment and the one-way inclusion are in NOTE.md.")
    if args.certificate is not None:
        print(f"Certificate: {args.certificate}")
    if args.check_certificate is not None:
        print("PASS: committed certificate matches every recomputed field.")


if __name__ == "__main__":
    main()
