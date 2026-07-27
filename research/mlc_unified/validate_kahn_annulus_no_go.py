"""Exact certificate for the Kahn-annulus global-injectivity no-go.

All calculations use Gaussian integers or rational arithmetic.  Sturm
chains and Rouché inequalities are recomputed exactly.  The script verifies
the explicit theorem in ``kahn_annulus_global_injectivity_no_go.md``; it
does not make the example an actual dynamically generated KL stage and
cannot promote any global MLC obligation.
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
NOTE = ROOT / "kahn_annulus_global_injectivity_no_go.md"
LATEX = ROOT / "latex" / "sections" / "10_end_rescaling_response.tex"
LEDGER = ROOT / "proof_obligations.json"
OUT = ROOT / "kahn_annulus_no_go_validation_20260725.json"

z, t = sp.symbols("z t")
ii = sp.I

R_PRIME = sp.Rational(1287, 1000)
R_TARGET = R_PRIME**16

A = [
    (1 + 6 * ii) / 10,
    (-3 - ii) / 10,
    (-7 + 2 * ii) / 10,
]
B = [
    (-6 + 2 * ii) / 10,
    4 * ii / 10,
]

N_COEFFS = [
    2000 + 4000 * ii,
    19600 + 2200 * ii,
    28460 - 23880 * ii,
    4072 - 29046 * ii,
    -6630 - 10210 * ii,
    -1950 - 1525 * ii,
]
D_COEFFS = [
    1525 + 1950 * ii,
    10210 + 6630 * ii,
    29046 - 4072 * ii,
    23880 - 28460 * ii,
    -2200 - 19600 * ii,
    -4000 - 2000 * ii,
]
N = sp.Poly.from_list(N_COEFFS, z)
D0 = sp.Poly.from_list(D_COEFFS, z)

ANGULAR_COEFFS = [
    619271,
    -5100608,
    35876739,
    -169721152,
    491196326,
    -885663808,
    1065558054,
    -957958592,
    669681731,
    -236915328,
    60062535,
]

OUTER_COEFFS = [
    11751160313656400426951788919,
    -137579839638925277492971300800,
    958901799234288449551831128476,
    -4106906924234287705167320942400,
    10779372189655006534093819771914,
    -16680328775739752952831727982400,
    14042199262274463963774353314076,
    -5586354003042199421157378340800,
    1394955241714223750805412881719,
]

CRITICAL_COEFFS = [
    -1268000 + 501000 * ii,
    -1247000 + 7116800 * ii,
    17024420 + 10563170 * ii,
    33992992 - 21977616 * ii,
    -52469243 * ii,
    -33992992 - 21977616 * ii,
    -17024420 + 10563170 * ii,
    1247000 + 7116800 * ii,
    1268000 + 501000 * ii,
]
CRITICAL_POLY = sp.Poly.from_list(CRITICAL_COEFFS, z)

CRITICAL_CENTERS = [
    (-1469179, 35737),
    (-1187253, 1185352),
    (-818448, 1003716),
    (-680250, 16547),
    (-487955, 598410),
    (-421815, 421140),
    (407227, 223067),
    (1888874, 1034668),
]
CRITICAL_MULTIPLIERS = [126, 362, 118, 451, 122, 192, 182, 144]
CRITICAL_RADIUS = sp.Rational(1, 10_000)

COLLISION_COEFFS = [
    1649705408450 + 1129218801775 * ii,
    8374862949240 - 2102550942545 * ii,
    5597363347032 - 11487498744901 * ii,
    -2960676892680 - 7024430543585 * ii,
    -1525645358450 - 501687535025 * ii,
]
COLLISION_POLY = sp.Poly.from_list(COLLISION_COEFFS, z)
COLLISION_CENTER = (
    -sp.Rational(570412, 1_000_000)
    + ii * sp.Rational(1153470, 1_000_000)
)
COLLISION_RADIUS = sp.Rational(1, 100_000)


def sign(value: sp.Expr) -> int:
    value = sp.factor(value)
    assert value != 0
    return 1 if value > 0 else -1


def sign_string(values: list[int]) -> str:
    return "".join("+" if value > 0 else "-" for value in values)


def variations(values: list[int]) -> int:
    return sum(a != b for a, b in zip(values, values[1:]))


def sturm_certificate(
    polynomial: sp.Poly,
    expected_minus: str,
    expected_plus: str,
) -> dict[str, object]:
    chain = [sp.Poly(item, t) for item in sp.sturm(polynomial.as_expr(), t)]
    degrees = [item.degree() for item in chain]
    plus = [sign(item.LC()) for item in chain]
    minus = [
        sign(item.LC()) * ((-1) ** item.degree())
        for item in chain
    ]
    minus_string = sign_string(minus)
    plus_string = sign_string(plus)
    assert minus_string == expected_minus
    assert plus_string == expected_plus
    assert variations(minus) == variations(plus)
    assert polynomial.eval(0) > 0
    assert polynomial.LC() > 0
    return {
        "degrees": degrees,
        "minus_infinity_signs": minus_string,
        "plus_infinity_signs": plus_string,
        "variations_minus": variations(minus),
        "variations_plus": variations(plus),
        "real_roots": variations(minus) - variations(plus),
    }


def lower_norm(value: sp.Expr) -> sp.Rational:
    return max(abs(sp.re(value)), abs(sp.im(value)))


def upper_norm(value: sp.Expr) -> sp.Rational:
    return abs(sp.re(value)) + abs(sp.im(value))


def rouche_ratio(
    polynomial: sp.Poly,
    center: sp.Expr,
    radius: sp.Rational,
) -> sp.Rational:
    derivative = sp.diff(polynomial.as_expr(), z)
    lhs = lower_norm(derivative.subs(z, center)) * radius
    rhs = upper_norm(polynomial.eval(center))
    for order in range(2, polynomial.degree() + 1):
        term = sp.diff(polynomial.as_expr(), z, order).subs(z, center)
        rhs += upper_norm(term) * radius**order / sp.factorial(order)
    assert lhs > rhs
    return sp.factor(lhs / rhs)


def product_identity_audit() -> dict[str, object]:
    alpha = [1 + 6 * ii, -3 - ii, -7 + 2 * ii]
    beta = [-6 + 2 * ii, 4 * ii]
    raw_num = sp.expand(
        sp.prod(10 * z - item for item in alpha)
        * sp.prod(10 - sp.conjugate(item) * z for item in beta)
    )
    raw_den = sp.expand(
        sp.prod(10 - sp.conjugate(item) * z for item in alpha)
        * sp.prod(10 * z - item for item in beta)
    )
    ratio_num = sp.cancel(N.as_expr() / raw_num)
    ratio_den = sp.cancel(D0.as_expr() / raw_den)
    expected_scaling = (1 - ii) / 8
    assert sp.simplify(ratio_num - expected_scaling) == 0
    assert sp.simplify(ratio_den - expected_scaling) == 0
    return {
        "passed": True,
        "common_scaling": str(ratio_num),
        "numerator_coefficients": [str(item) for item in N.all_coeffs()],
        "denominator_coefficients": [str(item) for item in D0.all_coeffs()],
    }


def zero_pole_audit() -> dict[str, object]:
    max_a_sq = sp.Rational(53, 100)
    max_b_sq = sp.Rational(40, 100)
    checks = {
        "source_radius_times_max_a_below_one": bool(
            R_PRIME**2 * max_a_sq < 1
        ),
        "source_radius_times_max_b_below_one": bool(
            R_PRIME**2 * max_b_sq < 1
        ),
    }
    assert all(checks.values())
    return {"passed": True, "checks": checks}


def angular_audit() -> dict[str, object]:
    cosine = (1 - t**2) / (1 + t**2)
    sine = 2 * t / (1 + t**2)

    def poisson(item: sp.Expr) -> sp.Expr:
        real = sp.re(item)
        imag = sp.im(item)
        norm_sq = real**2 + imag**2
        denominator = (
            1 + norm_sq - 2 * (real * cosine + imag * sine)
        )
        return (1 - norm_sq) / denominator

    angular = sp.factor(
        sp.together(
            sum(poisson(item) for item in A)
            - sum(poisson(item) for item in B)
        )
    )
    numerator, denominator = sp.fraction(angular)
    numerator_poly = sp.Poly(numerator, t)
    _, numerator_primitive = sp.polys.polytools.primitive(numerator_poly)
    assert numerator_primitive.all_coeffs() == ANGULAR_COEFFS
    denominator_content, denominator_factors = sp.factor_list(denominator)
    assert denominator_content > 0
    assert denominator_factors
    for factor, multiplicity in denominator_factors:
        factor_poly = sp.Poly(factor, t)
        assert multiplicity > 0
        assert factor_poly.degree() == 2
        assert factor_poly.LC() > 0
        assert sp.discriminant(factor_poly.as_expr(), t) < 0
    certificate = sturm_certificate(
        numerator_primitive,
        "+--+++--+--",
        "++--+--+++-",
    )
    assert len(A) - len(B) == 1
    return {
        "passed": True,
        "degree": len(A) - len(B),
        "coefficients": ANGULAR_COEFFS,
        "positive_denominator_factor_count": len(denominator_factors),
        "sturm": certificate,
    }


def outer_circle_audit() -> dict[str, object]:
    source_point = (
        R_PRIME * (1 - t**2 + 2 * ii * t) / (1 + t**2)
    )
    source_conjugate = sp.conjugate(source_point).subs(
        sp.conjugate(t), t
    )
    n_conjugate = sp.conjugate(N.as_expr()).subs(sp.conjugate(z), z)
    d_conjugate = sp.conjugate(D0.as_expr()).subs(sp.conjugate(z), z)
    difference = sp.cancel(
        N.as_expr().subs(z, source_point)
        * n_conjugate.subs(z, source_conjugate)
        - D0.as_expr().subs(z, source_point)
        * d_conjugate.subs(z, source_conjugate)
    )
    numerator, denominator = sp.fraction(difference)
    numerator_poly = sp.Poly(sp.expand(numerator), t)
    content, primitive = sp.polys.polytools.primitive(numerator_poly)
    assert content == 656369
    assert primitive.all_coeffs() == OUTER_COEFFS
    assert sp.factor(denominator) == (
        320000000000000000000000000 * (1 + t**2) ** 4
    )
    certificate = sturm_certificate(
        primitive,
        "+--++--++",
        "++--++--+",
    )
    return {
        "passed": True,
        "content": int(content),
        "coefficients": OUTER_COEFFS,
        "sturm": certificate,
    }


def upper_bound_audit() -> dict[str, object]:
    rational_modulus_bounds = [
        sp.Rational(61, 100),
        sp.Rational(32, 100),
        sp.Rational(73, 100),
    ]
    exact_modulus_squares = [
        sp.re(item) ** 2 + sp.im(item) ** 2
        for item in A
    ]
    assert all(
        exact_square < bound**2
        for exact_square, bound in zip(
            exact_modulus_squares, rational_modulus_bounds
        )
    )
    assert all(R_PRIME * bound < 1 for bound in rational_modulus_bounds)

    radius, modulus, cosine = sp.symbols(
        "radius modulus cosine", positive=True
    )
    factor_square = (
        radius**2
        + modulus**2
        - 2 * radius * modulus * cosine
    ) / (
        1
        + radius**2 * modulus**2
        - 2 * radius * modulus * cosine
    )
    expected_cosine_derivative = (
        -2
        * modulus
        * radius
        * (modulus - 1)
        * (modulus + 1)
        * (radius - 1)
        * (radius + 1)
        / (
            2 * cosine * modulus * radius
            - modulus**2 * radius**2
            - 1
        )
        ** 2
    )
    assert sp.factor(
        sp.diff(factor_square, cosine) - expected_cosine_derivative
    ) == 0
    expected_radius_derivative = (
        -2
        * (modulus - 1)
        * (modulus + 1)
        * (modulus - radius)
        / (modulus * radius - 1) ** 3
    )
    assert sp.factor(
        sp.diff(factor_square.subs(cosine, 1), radius)
        - expected_radius_derivative
    ) == 0
    expected_modulus_derivative = (
        2
        * (modulus - radius)
        * (radius - 1)
        * (radius + 1)
        / (modulus * radius - 1) ** 3
    )
    assert sp.factor(
        sp.diff(factor_square.subs(cosine, 1), modulus)
        - expected_modulus_derivative
    ) == 0
    product = sp.prod(
        (R_PRIME - bound) / (1 - R_PRIME * bound)
        for bound in rational_modulus_bounds
    )
    assert product == sp.Rational(5697579109375, 119480253283)
    assert product < 48 < R_TARGET
    return {
        "passed": True,
        "product_numerator": int(sp.numer(product)),
        "product_denominator": int(sp.denom(product)),
        "product_below_48": True,
        "48_below_target_radius": True,
        "exact_modulus_squares": [
            str(value) for value in exact_modulus_squares
        ],
        "factor_maximization_checked": True,
        "target_exponent": 16,
    }


def critical_point_audit() -> dict[str, object]:
    derivative_numerator = sp.Poly(
        sp.diff(N.as_expr(), z) * D0.as_expr()
        - N.as_expr() * sp.diff(D0.as_expr(), z),
        z,
    )
    scale = sp.cancel(
        derivative_numerator.LC() / CRITICAL_POLY.LC()
    )
    assert sp.expand(
        derivative_numerator.as_expr()
        - scale * CRITICAL_POLY.as_expr()
    ) == 0

    centers = [
        sp.Rational(real, 1_000_000)
        + ii * sp.Rational(imag, 1_000_000)
        for real, imag in CRITICAL_CENTERS
    ]
    ratios = [
        rouche_ratio(CRITICAL_POLY, center, CRITICAL_RADIUS)
        for center in centers
    ]
    floors = [int(sp.floor(ratio)) for ratio in ratios]
    assert floors == CRITICAL_MULTIPLIERS
    assert all(
        ratio > multiplier
        for ratio, multiplier in zip(ratios, CRITICAL_MULTIPLIERS)
    )

    for left_index, left in enumerate(centers):
        for right in centers[left_index + 1:]:
            assert (
                sp.re(left - right) ** 2
                + sp.im(left - right) ** 2
                > (2 * CRITICAL_RADIUS) ** 2
            )

    inner_indices = {3, 4, 5, 6}
    for index, center in enumerate(centers):
        center_modulus_sq = sp.re(center) ** 2 + sp.im(center) ** 2
        if index in inner_indices:
            assert center_modulus_sq < (1 - CRITICAL_RADIUS) ** 2
        else:
            assert center_modulus_sq > (
                sp.Rational(12901, 10000) + CRITICAL_RADIUS
            ) ** 2

    return {
        "passed": True,
        "degree": CRITICAL_POLY.degree(),
        "disk_count": len(centers),
        "radius": str(CRITICAL_RADIUS),
        "exact_ratio_floors": floors,
        "inside_unit_disk_indices": [4, 5, 6, 7],
        "outside_1_2901_indices": [1, 2, 3, 8],
    }


def collision_audit() -> dict[str, object]:
    z1 = -1 + sp.Rational(4, 5) * ii
    w = sp.cancel(N.eval(z1) / D0.eval(z1))
    expected_w = (
        -sp.Rational(559602300, 1858025273)
        + ii * sp.Rational(1886709225, 1858025273)
    )
    assert w == expected_w
    collision_polynomial = sp.Poly(
        sp.together(N.as_expr() - w * D0.as_expr()), z
    )
    quotient, remainder = sp.div(
        collision_polynomial,
        sp.Poly(z - z1, z),
    )
    assert remainder.is_zero
    quotient_scale = sp.cancel(quotient.LC() / COLLISION_POLY.LC())
    assert sp.expand(
        quotient.as_expr()
        - quotient_scale * COLLISION_POLY.as_expr()
    ) == 0

    ratio = rouche_ratio(
        COLLISION_POLY,
        COLLISION_CENTER,
        COLLISION_RADIUS,
    )
    ratio_floor = int(sp.floor(ratio))
    assert ratio_floor == 11
    assert ratio > 11

    center_modulus_sq = (
        sp.re(COLLISION_CENTER) ** 2
        + sp.im(COLLISION_CENTER) ** 2
    )
    assert center_modulus_sq == sp.Rational(
        413965722661, 250000000000
    )
    assert center_modulus_sq > (1 + COLLISION_RADIUS) ** 2
    assert center_modulus_sq < (R_PRIME - COLLISION_RADIUS) ** 2
    assert sp.re(z1) ** 2 + sp.im(z1) ** 2 == sp.Rational(41, 25)
    assert 1 < sp.Rational(41, 25) < R_PRIME**2
    assert (
        sp.re(COLLISION_CENTER - z1) ** 2
        + sp.im(COLLISION_CENTER - z1) ** 2
        > COLLISION_RADIUS**2
    )

    return {
        "passed": True,
        "z1": str(z1),
        "w": str(w),
        "quartic_degree": COLLISION_POLY.degree(),
        "rouche_ratio_floor": ratio_floor,
        "center_modulus_squared": str(center_modulus_sq),
        "collision_disk_inside_source_annulus": True,
    }


def ledger_and_documentation_audit() -> dict[str, object]:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    by_id = {item["id"]: item for item in obligations}
    expected_status = {
        "KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO": "proved",
        "KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION": "proved",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION": "proved",
        "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING": "open",
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT": "open",
        "VIRTUAL_WAVE_MARKED_CORRESPONDENCE": "open",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE": "open",
        "MLC": "open",
    }
    actual_status = {key: by_id[key]["status"] for key in expected_status}
    assert actual_status == expected_status
    embedding_dependencies = set(
        by_id["DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING"][
            "dependencies"
        ]
    )
    assert "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION" in (
        embedding_dependencies
    )
    counts = {
        status: sum(item["status"] == status for item in obligations)
        for status in ("imported", "proved", "open")
    }
    assert len(obligations) == 330
    assert counts == {"imported": 23, "proved": 235, "open": 72}

    note = NOTE.read_text(encoding="utf-8")
    required = [
        "Theorem 1.1",
        "Exact Sturm certificate",
        "Exact exclusion of critical points",
        "Exact self-collision",
        "abstract annulus no-go",
        "not an actual counterexample",
        "VAAPC-I, UPTCR, and MLC remain open",
    ]
    missing = [phrase for phrase in required if phrase not in note]
    assert not missing, missing

    def aligned_formula_body(document: str) -> str:
        start = document.index("P(z)={}")
        end = document.index(r"\end{aligned}", start)
        return (
            "".join(document[start:end].split())
            .replace("&", "")
            .replace("\\\\", "")
        )

    signed_critical_terms = [
        "(-1268000+501000i)z^8",
        "+(-1247000+7116800i)z^7",
        "+(17024420+10563170i)z^6",
        "+(33992992-21977616i)z^5",
        "-52469243iz^4",
        "+(-33992992-21977616i)z^3",
        "+(-17024420+10563170i)z^2",
        "+(1247000+7116800i)z",
    ]
    note_formula = aligned_formula_body(note)
    note_positions = [
        note_formula.index(term) for term in signed_critical_terms
    ]
    assert note_positions == sorted(note_positions)
    assert "+(1268000+501000i)." in note_formula

    latex = LATEX.read_text(encoding="utf-8")
    latex_formula = aligned_formula_body(latex)
    latex_positions = [
        latex_formula.index(term) for term in signed_critical_terms
    ]
    assert latex_positions == sorted(latex_positions)
    assert "+1268000+501000i." in latex_formula
    return {
        "passed": True,
        "total": len(obligations),
        "counts": counts,
        "statuses": actual_status,
        "required_documentation_phrases": required,
        "critical_polynomial_documentation_match": True,
    }


def main() -> None:
    report = {
        "scope": (
            "Exact algebraic certificate for an abstract Kahn-annulus "
            "counterexample; not an actual KL dynamical-stage collision."
        ),
        "product_identity": product_identity_audit(),
        "zero_pole_exclusion": zero_pole_audit(),
        "inner_boundary": angular_audit(),
        "outer_circle": outer_circle_audit(),
        "upper_target_bound": upper_bound_audit(),
        "critical_points": critical_point_audit(),
        "self_collision": collision_audit(),
        "ledger_and_documentation": ledger_and_documentation_audit(),
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
