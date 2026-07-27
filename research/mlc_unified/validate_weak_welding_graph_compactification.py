"""Audit the rejected weak welding-graph compactification.

This script checks the finite algebraic counterexamples and the correct graph
projection formula.  The bilateral-shift weak-convergence argument is proved
in the accompanying note; no finite computation is used to promote the open
dynamical welding gate.
"""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
OUT = (
    ROOT
    / "research"
    / "mlc_unified"
    / "weak_welding_graph_compactification_20260725.json"
)


def matmul(a: list[list[float]], b: list[list[float]]) -> list[list[float]]:
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def max_abs_difference(a: list[list[float]], b: list[list[float]]) -> float:
    return max(
        abs(a[i][j] - b[i][j])
        for i in range(len(a))
        for j in range(len(a[0]))
    )


def false_scalar_matrix(j: float) -> list[list[float]]:
    return [[0.5, 0.5 * j], [0.5 * j, 0.5]]


def true_scalar_projection(j: float) -> list[list[float]]:
    denominator = 1.0 + j * j
    return [
        [1.0 / denominator, j / denominator],
        [j / denominator, j * j / denominator],
    ]


def quadratic_form(a: list[list[float]], x: list[float]) -> float:
    return sum(x[i] * a[i][j] * x[j] for i in range(len(x)) for j in range(len(x)))


def main() -> None:
    false_two = false_scalar_matrix(2.0)
    false_half = false_scalar_matrix(0.5)
    true_two = true_scalar_projection(2.0)
    true_half = true_scalar_projection(0.5)

    checks = {
        # For J=2, x=(1,-1) gives quadratic form -1.
        "claimed_formula_not_positive_for_j_two": (
            quadratic_form(false_two, [1.0, -1.0]) < 0.0
        ),
        "claimed_formula_not_idempotent_for_j_half": (
            max_abs_difference(matmul(false_half, false_half), false_half) > 1e-6
        ),
        "correct_projection_idempotent_for_j_two": (
            max_abs_difference(matmul(true_two, true_two), true_two) < 1e-12
        ),
        "correct_projection_idempotent_for_j_half": (
            max_abs_difference(matmul(true_half, true_half), true_half) < 1e-12
        ),
        "correct_projection_annihilates_graph_orthogonal_vector": (
            abs(quadratic_form(true_two, [-2.0, 1.0])) < 1e-12
        ),
        "bilateral_shift_wot_counterexample_proved_in_note": True,
        "wot_compactification_not_promoted": True,
        "source_welding_bounds_not_claimed": True,
        "mlc_not_claimed": True,
    }

    all_checks = all(checks.values())
    payload = {
        "artifact": "WOT_WELDING_ALGEBRA_NO_GO",
        "date": "2026-07-25",
        "status": "WOT_WELDING_ALGEBRA_NO_GO_VALID" if all_checks else "FAILED",
        "checks": checks,
        "all_checks": all_checks,
        "logical_conclusion": (
            "the original graph-projection formula is false for general bounded "
            "weldings, and WOT convergence does not preserve graph or gluing algebra"
        ),
        "remaining_open": [
            "DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS",
            "END_PLUMBING_TRACE_RESPONSE_CONTROL",
            "UPTCR",
            "MLC",
        ],
        "original_artifacts_written": False,
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(payload["status"])
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
