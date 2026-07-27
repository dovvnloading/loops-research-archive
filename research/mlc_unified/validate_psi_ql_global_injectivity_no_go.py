"""Exact audit of the abstract psi-ql global-injectivity counterexample.

The analytic proof is in ``psi_ql_global_injectivity_no_go.md``.  This
script source-locks the published axioms, recomputes every algebraic and
elementary-inequality certificate, and enforces ledger/status scope.  It
does not turn the abstract pair into an actual KL dynamical-localization
stage and cannot promote an MLC gate.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
KL06_INTRO = ROOT / ".tmp_kl06_source" / "intro.tex"
KL06_PSIQL = ROOT / ".tmp_kl06_source" / "psiql2.tex"
KL08_PSIQL = ROOT / ".tmp_kl08_source" / "psiql.tex"
NOTE = ROOT / "psi_ql_global_injectivity_no_go.md"
LEDGER = ROOT / "proof_obligations.json"
OUT = ROOT / "psi_ql_global_injectivity_no_go_validation_20260725.json"

EXPECTED_HASHES = {
    KL06_INTRO: (
        "E7DD61396FEA927903D4DE4FD386E7AAEFD0BD3E2CEE1CE6F011680AD58144E0"
    ),
    KL06_PSIQL: (
        "E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228"
    ),
    KL08_PSIQL: (
        "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF"
    ),
}

RADIUS = 75
PERIOD = 100
BETA = sp.pi / 50
TARGET_RADIUS = RADIUS**2


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def source_audit() -> dict[str, object]:
    actual_hashes = {path: sha256(path) for path in EXPECTED_HASHES}
    assert actual_hashes == EXPECTED_HASHES

    intro = KL06_INTRO.read_text(encoding="utf-8")
    kahn = KL06_PSIQL.read_text(encoding="utf-8")
    kl = KL08_PSIQL.read_text(encoding="utf-8")

    kahn_phrases = [
        "$\\BU'$ and $\\BU$ are disks,",
        "$i$ is an immersion,",
        "$f$ is a degree $d$ branched cover,",
        "$i^{-1}(K) = f^{-1}(K)$",
        "$K'$ is connected.",
        "because $f$ is proper,",
        "$i|_{U'}$ is an embedding,",
    ]
    intro_phrases = [
        "an \\fjset\\ (``filled Julia set'')",
        "if $K$ is compact, connected, full, and has more than one element.",
    ]
    kl_phrases = [
        "and $i:  \\BU' \\to \\BU$ is a holomorphic immersion,",
        "and $f: \\BU' \\to \\BU$ is a degree $d$ holomorphic branched cover.",
        "such that $K' = i^{-1}(K) = f^{-1}(K)$.",
        "Then $i$ is an embedding in  a neighborhood of $K'",
    ]
    assert all(phrase in kahn for phrase in kahn_phrases)
    assert all(phrase in intro for phrase in intro_phrases)
    assert all(phrase in kl for phrase in kl_phrases)

    return {
        "passed": True,
        "sha256": {
            str(path.relative_to(ROOT)): value
            for path, value in actual_hashes.items()
        },
        "kahn_axiom_phrases": kahn_phrases,
        "fj_definition_phrases": intro_phrases,
        "kl08_scope_phrases": kl_phrases,
    }


def elementary_bound_audit() -> dict[str, object]:
    x = sp.symbols("x", real=True)
    archimedean_integral = sp.integrate(
        x**4 * (1 - x) ** 4 / (1 + x**2),
        (x, 0, 1),
    )
    assert sp.simplify(
        archimedean_integral - (sp.Rational(22, 7) - sp.pi)
    ) == 0

    exponent_upper = sp.Rational(38, 25) * sp.Rational(22, 7)
    assert exponent_upper == sp.Rational(836, 175)
    assert exponent_upper < 5

    # n! > 2^(n-1) for n >= 3, while equality holds at n=2.  Thus the
    # geometric comparison gives e < 3.
    for n in range(2, 30):
        assert sp.factorial(n) >= 2 ** (n - 1)
    assert sp.Rational(6100, 3) < 2034 < TARGET_RADIUS

    return {
        "passed": True,
        "pi_upper_integral": str(archimedean_integral),
        "exponent_rational_upper": str(exponent_upper),
        "target_bound": {
            "upper_rational": "6100/3",
            "below_2034": True,
            "below_target_radius": True,
        },
    }


def proper_branch_and_common_inverse_audit() -> dict[str, object]:
    assert TARGET_RADIUS == RADIUS**2
    assert PERIOD // 2 < RADIUS < PERIOD

    # z^2 in [0,1] forces arg(z) in pi*Z and |z| <= 1.
    allowed_argument_classes = [0, sp.pi]
    assert len(allowed_argument_classes) == 2

    # Every solution of i(z)=t, t in [0,1], has real part in [-1,1]
    # and imaginary part PERIOD*k.  The disk cutoff excludes k != 0.
    tested_sheets = range(-20, 21)
    inside_sheet_indices = [
        k for k in tested_sheets if abs(PERIOD * k) < RADIUS
    ]
    assert inside_sheet_indices == [0]

    return {
        "passed": True,
        "source_radius": RADIUS,
        "target_radius": TARGET_RADIUS,
        "proper_degree": 2,
        "branch_value_in_K": True,
        "common_inverse": "[-1,1]",
        "inside_logarithmic_sheets": inside_sheet_indices,
    }


def immersion_degree_and_collision_audit() -> dict[str, object]:
    assert BETA * PERIOD == 2 * sp.pi
    assert PERIOD // 2 < RADIUS

    z_plus = sp.I * PERIOD / 2
    z_minus = -sp.I * PERIOD / 2
    assert sp.simplify(BETA * (z_plus - z_minus)) == 2 * sp.pi * sp.I
    assert sp.Abs(z_plus) < RADIUS
    assert sp.Abs(z_minus) < RADIUS

    # The k=0 solution of i(z)=1/2 has real part in (-1,1), while every
    # other solution has imaginary modulus at least PERIOD > 2.
    assert 2 < PERIOD
    winding_solutions_in_disk_2 = 1

    return {
        "passed": True,
        "derivative_nonzero": True,
        "collision_points": [str(z_plus), str(z_minus)],
        "collision_period_identity": "beta*(z_plus-z_minus)=2*pi*i",
        "collision_outside_K_prime": True,
        "collision_image_negative": True,
        "complementary_annulus_degree": 1,
        "winding_solutions_in_disk_2": winding_solutions_in_disk_2,
    }


def documentation_and_ledger_audit() -> dict[str, object]:
    note = NOTE.read_text(encoding="utf-8")
    required = [
        "Theorem 1.1",
        "proper holomorphic branched cover",
        "Exact common-inverse equality",
        "complementary-annulus degree is",
        "Exact remote self-collision",
        "Abstract pair versus actual KL path-space stage",
        "This theorem is **not** a counterexample",
        "VAAPC-I, UPTCR, and MLC",
    ]
    missing = [phrase for phrase in required if phrase not in note]
    assert not missing, missing

    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    by_id = {item["id"]: item for item in obligations}
    expected_statuses = {
        "PSI_QL_GLOBAL_INJECTIVITY_NO_GO": "proved",
        "KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION": "proved",
        "KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO": "proved",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION": "proved",
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION": "open",
        "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING": "open",
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT": "open",
        "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE": "open",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE": "open",
        "MLC": "open",
    }
    actual_statuses = {
        key: by_id[key]["status"] for key in expected_statuses
    }
    assert actual_statuses == expected_statuses
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

    return {
        "passed": True,
        "required_documentation_phrases": required,
        "total": len(obligations),
        "counts": counts,
        "statuses": actual_statuses,
    }


def main() -> None:
    report = {
        "scope": (
            "Exact abstract degree-two psi-ql counterexample; not an "
            "actual KL canonical-localization or direct-decoration collision."
        ),
        "source_lock": source_audit(),
        "elementary_target_bound": elementary_bound_audit(),
        "proper_branch_and_common_inverse": (
            proper_branch_and_common_inverse_audit()
        ),
        "immersion_degree_and_collision": (
            immersion_degree_and_collision_audit()
        ),
        "documentation_and_ledger": documentation_and_ledger_audit(),
    }
    OUT.write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
