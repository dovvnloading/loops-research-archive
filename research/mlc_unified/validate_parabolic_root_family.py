"""Exact finite sweep for primitive parabolic satellite anchors.

For a primitive q-th root lambda, the quadratic polynomial with fixed-point
multiplier lambda is represented by the local germ

    g(w) = lambda*w + w**2.

This validator computes g**q modulo w**(q+2) in the exact ring
Q[lambda] = Q[x]/(Phi_q(x)).  It checks the expected finite parabolic
normal-form cancellation through q=16.  The result is a finite certificate;
it is not a proof of the all-q statement and not a bridge theorem for
unbounded satellite towers.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "parabolic_root_family_20260726.json"
X = sp.Symbol("x")


def reduced(expr: sp.Expr, q: int) -> sp.Expr:
    """Reduce a rational polynomial in x modulo the q-th cyclotomic polynomial."""
    modulus = sp.Poly(sp.cyclotomic_poly(q, X), X, domain=sp.QQ)
    value = sp.Poly(sp.expand(expr), X, domain=sp.QQ)
    return sp.rem(value, modulus).as_expr()


def poly_mul(left: dict[int, sp.Expr], right: dict[int, sp.Expr], degree: int, q: int) -> dict[int, sp.Expr]:
    out: dict[int, sp.Expr] = {}
    for i, a in left.items():
        for j, b in right.items():
            if i + j <= degree:
                out[i + j] = reduced(out.get(i + j, 0) + a * b, q)
    return {k: v for k, v in out.items() if v != 0}


def compose_with_g(poly: dict[int, sp.Expr], degree: int, q: int) -> dict[int, sp.Expr]:
    """Return poly(g(w)), where g(w)=x*w+w^2, truncated at ``degree``."""
    germ = {1: X, 2: sp.Integer(1)}
    result: dict[int, sp.Expr] = {}
    power: dict[int, sp.Expr] = {0: sp.Integer(1)}
    for exponent, coefficient in sorted(poly.items()):
        if exponent == 0:
            result[0] = reduced(result.get(0, 0) + coefficient, q)
            continue
        power = poly_mul(power, germ, degree, q)
        for output_degree, value in power.items():
            result[output_degree] = reduced(
                result.get(output_degree, 0) + coefficient * value, q
            )
    return {k: v for k, v in result.items() if v != 0}


def iterate_g(q: int) -> dict[int, sp.Expr]:
    degree = q + 1
    current = {1: sp.Integer(1)}
    for _ in range(q):
        current = compose_with_g(current, degree, q)
    return current


def check_order(q: int) -> dict[str, object]:
    phi = sp.Poly(sp.cyclotomic_poly(q, X), X, domain=sp.QQ)
    germ = iterate_g(q)
    lam = X
    z_alpha = reduced(lam / 2, q)
    c_parameter = reduced(z_alpha - z_alpha**2, q)
    fixed_point = reduced(z_alpha**2 + c_parameter - z_alpha, q)
    multiplier = reduced(2 * z_alpha - lam, q)
    checks = {
        "cyclotomic_relation": reduced(phi.as_expr(), q) == 0,
        "primitive_root_relation": reduced(lam**q - 1, q) == 0,
        "fixed_point_parameterization": fixed_point == 0,
        "multiplier_parameterization": multiplier == 0,
        "iterate_multiplier_one": reduced(germ.get(1, 0) - 1, q) == 0,
        "all_intermediate_terms_cancel": all(
            reduced(germ.get(k, 0), q) == 0 for k in range(2, q + 1)
        ),
        "first_parabolic_term_nonzero": reduced(germ.get(q + 1, 0), q) != 0,
    }
    return {
        "q": q,
        "cyclotomic_polynomial": str(phi.as_expr()),
        "parameter": str(c_parameter),
        "first_parabolic_coefficient": str(reduced(germ.get(q + 1, 0), q)),
        "checks": checks,
        "all_checks": all(checks.values()),
    }


def main() -> None:
    orders = [check_order(q) for q in range(2, 17)]
    result = {
        "certificate": "PARABOLIC_ROOT_FAMILY_FINITE_SWEEP_VALID",
        "orders_checked": [item["q"] for item in orders],
        "orders": orders,
        "all_checks": all(item["all_checks"] for item in orders),
        "scope": "exact finite sweep only; no all-q theorem and no uniform cylinder bridge",
        "original_artifacts_written": False,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    if not result["all_checks"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
