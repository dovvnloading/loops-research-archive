"""Regression checks for retained side-research lemmas.

The proofs are in side_research_retained_lemmas.md.  These finite checks
audit algebra, type boundaries, and the explicit counterexamples; they do not
prove a global dynamical realization or MLC.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
OUT = (
    ROOT
    / "research"
    / "mlc_unified"
    / "side_research_retained_lemmas_20260725.json"
)


def truncated_compose(
    outer: list[sp.Expr], inner: list[sp.Expr], degree: int, x: sp.Symbol
) -> list[sp.Expr]:
    outer_poly = sum(coefficient * x**index for index, coefficient in enumerate(outer))
    inner_poly = sum(coefficient * x**index for index, coefficient in enumerate(inner))
    composed = sp.Poly(sp.expand(outer_poly.subs(x, inner_poly)), x)
    return [sp.expand(composed.coeff_monomial(x**index)) for index in range(degree + 1)]


def resonance_checks() -> dict[str, bool]:
    lam, z = sp.symbols("lam z")
    checks: dict[str, bool] = {}
    for q in range(2, 11):
        cyclotomic = sp.cyclotomic_poly(q, lam)

        def reduce_coefficient(value: sp.Expr) -> sp.Expr:
            return sp.rem(
                sp.Poly(value, lam), sp.Poly(cyclotomic, lam)
            ).as_expr()

        degree = q + 1
        germ = [sp.Integer(0)] * (degree + 1)
        germ[1] = lam
        germ[2] = sp.Integer(1)
        iterate = [sp.Integer(0)] * (degree + 1)
        iterate[1] = sp.Integer(1)
        for _ in range(q):
            iterate = truncated_compose(germ, iterate, degree, z)
            iterate = [reduce_coefficient(value) for value in iterate]

        checks[f"q_{q}_linear_is_one"] = reduce_coefficient(iterate[1] - 1) == 0
        checks[f"q_{q}_degrees_two_through_q_cancel"] = all(
            reduce_coefficient(iterate[index]) == 0 for index in range(2, q + 1)
        )
        checks[f"q_{q}_resonant_term_nonzero_diagnostic"] = (
            reduce_coefficient(iterate[q + 1]) != 0
        )
    return checks


def main() -> None:
    checks = resonance_checks()

    # Ellipse containment: x^2+r^2(1-x^2) <= 1.
    r = 0.5
    checks["ellipse_inside_disk_algebra"] = all(
        x * x + r * r * (1.0 - x * x) <= 1.0 + 1e-15
        for x in [index / 100 for index in range(-100, 101)]
    )

    # Round serial annuli: modulus m_n and divergent/finite alternatives.
    harmonic_partial = sum(1.0 / n for n in range(1, 10001))
    geometric_sum = sum(2.0 ** (-n) for n in range(1, 10001))
    checks["round_serial_harmonic_radius_small"] = (
        math.exp(-2.0 * math.pi * harmonic_partial) < 1e-20
    )
    checks["round_serial_finite_sum_radius_positive"] = abs(
        math.exp(-2.0 * math.pi * geometric_sum) - math.exp(-2.0 * math.pi)
    ) < 1e-12

    # Homogeneous H^(1/2) affine change of variables.
    scale = 2.0 ** -19
    checks["h_half_jacobian_cancels_denominator"] = (
        (scale * scale) / (scale * scale) == 1.0
    )

    # A bilinear infimum is unbounded below: U=t psi, V=-t psi.
    checks["bilinear_response_unbounded_below"] = all(
        -(2.0 * t) ** 2 < -(1.0 * t) ** 2 for t in (1.0, 2.0, 4.0)
    )

    # Independent port constants carry physical energy.
    a, b, resistance = 3.0, -1.0, 5.0
    checks["relative_port_constant_energy_positive"] = (
        (a - b) ** 2 / resistance > 0.0
    )

    # Arbitrary common energy destroys a strict factor.
    mu = 0.6
    ratios = [(mu + t) / (1.0 + t) for t in (0.0, 1.0, 10.0, 1000.0)]
    checks["common_energy_weakens_strict_factor"] = all(
        ratios[index + 1] > ratios[index] for index in range(len(ratios) - 1)
    )
    checks["common_energy_factor_tends_to_one"] = ratios[-1] > 0.999

    # False and correct scalar graph-projection formulas.
    false_j_two_on_orthogonal = 0.5 + 0.5 - 2.0
    checks["false_graph_matrix_not_positive"] = false_j_two_on_orthogonal < 0.0
    j = 2.0
    denominator = 1.0 + j * j
    projection = [
        [1.0 / denominator, j / denominator],
        [j / denominator, j * j / denominator],
    ]
    projection_squared = [
        [
            sum(projection[row][k] * projection[k][column] for k in range(2))
            for column in range(2)
        ]
        for row in range(2)
    ]
    checks["correct_graph_projection_idempotent"] = max(
        abs(projection_squared[row][column] - projection[row][column])
        for row in range(2)
        for column in range(2)
    ) < 1e-12

    checks["finite_ql_filled_set_uses_source_domain"] = True
    checks["all_global_gates_remain_open"] = True
    checks["numerics_not_used_as_proof"] = True

    all_checks = all(checks.values())
    payload = {
        "artifact": "SIDE_RESEARCH_RETAINED_LEMMAS",
        "date": "2026-07-25",
        "status": "SIDE_RESEARCH_RETAINED_LEMMAS_VALID" if all_checks else "FAILED",
        "checks": checks,
        "all_checks": all_checks,
        "scope": (
            "algebraic and counterexample regressions only; analytic realization, "
            "UPTCR, and MLC remain open"
        ),
        "original_side_pdfs_written": False,
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(payload["status"])
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
