"""Exact recurrence certificate for the first resonant parabolic term.

For g(w)=x*w+w**2 and a primitive q-th root x, formal conjugacy through
degree q gives b_n=S_n/(x**n-x), A=S_(q+1), and predicts the coefficient
q*x**(q-1)*A in g**q.  All arithmetic is performed exactly in
Q[x]/(Phi_q(x)).  This is a finite certificate, not an all-q theorem.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "parabolic_resonance_recurrence_20260725.json"
X = sp.Symbol("x")


def field_reduce(expr: sp.Expr, q: int) -> sp.Expr:
    """Reduce a rational expression in the exact cyclotomic field."""
    modulus = sp.Poly(sp.cyclotomic_poly(q, X), X, domain=sp.QQ)
    numerator, denominator = sp.cancel(expr).as_numer_denom()
    num = sp.Poly(sp.expand(numerator), X, domain=sp.QQ)
    den = sp.Poly(sp.expand(denominator), X, domain=sp.QQ)
    den_rem = sp.rem(den, modulus)
    if den_rem.is_zero:
        raise ZeroDivisionError(f"resonant denominator at q={q}: {denominator}")
    inverse = sp.invert(den_rem, modulus)
    return sp.rem(sp.rem(num, modulus) * inverse, modulus).as_expr()


def poly_mul(left: dict[int, sp.Expr], right: dict[int, sp.Expr], degree: int, q: int) -> dict[int, sp.Expr]:
    out: dict[int, sp.Expr] = {}
    for i, a in left.items():
        for j, b in right.items():
            if i + j <= degree:
                out[i + j] = field_reduce(out.get(i + j, 0) + a * b, q)
    return {k: v for k, v in out.items() if v != 0}


def compose_with_g(poly: dict[int, sp.Expr], degree: int, q: int) -> dict[int, sp.Expr]:
    germ = {1: X, 2: sp.Integer(1)}
    result: dict[int, sp.Expr] = {}
    power: dict[int, sp.Expr] = {0: sp.Integer(1)}
    for exponent, coefficient in sorted(poly.items()):
        if exponent == 0:
            result[0] = field_reduce(result.get(0, 0) + coefficient, q)
            continue
        power = poly_mul(power, germ, degree, q)
        for output_degree, value in power.items():
            result[output_degree] = field_reduce(
                result.get(output_degree, 0) + coefficient * value, q
            )
    return {k: v for k, v in result.items() if v != 0}


def iterate_g(q: int) -> dict[int, sp.Expr]:
    degree = q + 1
    current = {1: sp.Integer(1)}
    for _ in range(q):
        current = compose_with_g(current, degree, q)
    return current


def recurrence(q: int) -> tuple[list[sp.Expr], sp.Expr, sp.Expr]:
    b = [sp.Integer(0)] * (q + 1)
    b[1] = sp.Integer(1)
    for n in range(2, q + 1):
        source = sum(b[i] * b[n - i] for i in range(1, n))
        b[n] = field_reduce(source / (X**n - X), q)
    A = field_reduce(sum(b[i] * b[q + 1 - i] for i in range(1, q + 1)), q)
    predicted = field_reduce(q * X ** (q - 1) * A, q)
    return b, A, predicted


def check_order(q: int) -> dict[str, object]:
    b, A, predicted = recurrence(q)
    direct = iterate_g(q)
    actual = field_reduce(direct.get(q + 1, 0), q)
    checks = {
        "recurrence_matches_iterate": field_reduce(actual - predicted, q) == 0,
        "resonant_coefficient_nonzero": actual != 0,
        "intermediate_cancellation": all(field_reduce(direct.get(k, 0), q) == 0 for k in range(2, q + 1)),
    }
    return {
        "q": q,
        "cyclotomic_polynomial": str(sp.cyclotomic_poly(q, X)),
        "A": str(A),
        "predicted_coefficient": str(predicted),
        "direct_coefficient": str(actual),
        "checks": checks,
        "all_checks": all(checks.values()),
        "b_coefficients_through_q": [str(value) for value in b[1:]],
    }


def main() -> None:
    orders = [check_order(q) for q in range(2, 17)]
    result = {
        "certificate": "PARABOLIC_RESONANCE_RECURRENCE_FINITE_VALID",
        "orders_checked": [item["q"] for item in orders],
        "orders": orders,
        "all_checks": all(item["all_checks"] for item in orders),
        "scope": "exact finite recurrence/iterate agreement only; no all-q nondegeneracy theorem and no global MLC closure",
        "original_artifacts_written": False,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    if not result["all_checks"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
