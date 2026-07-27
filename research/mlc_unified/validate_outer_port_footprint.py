"""Mechanical audit for the fixed direct-decoration outer-port pass.

This script checks source locks, ledger typing, status boundaries, and
finite set-theoretic consequences of the proved formulas.  It does not
replace the analytic proofs in the two cited Markdown notes and cannot
promote any global MLC obligation.
"""

from __future__ import annotations

import hashlib
import json
import cmath
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parent
LEDGER = ROOT / "proof_obligations.json"
ABSTRACT_NOTE = ROOT / "embedded_disk_accessible_footprint_theorem.md"
OUTER_NOTE = ROOT / "direct_decoration_outer_port_footprint.md"
OUT = ROOT / "outer_port_footprint_validation_20260725.json"


SOURCE_LOCKS = {
    ROOT / ".tmp_kl06_source" / "wad.tex":
        "B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580",
    ROOT / ".tmp_kl06_source" / "psiql2.tex":
        "E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228",
    ROOT / ".tmp_kl08_source" / "kingdom.tex":
        "5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7",
    ROOT / ".tmp_kl08_source" / "psiql.tex":
        "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF",
    ROOT / ".tmp_kl08_source" / "moduli.tex":
        "CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E",
    ROOT / ".tmp_wave_audit" / "waves-with-Misha.tex":
        "AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def source_lock_audit() -> dict[str, object]:
    actual = {str(path.relative_to(ROOT)): sha256(path) for path in SOURCE_LOCKS}
    expected = {
        str(path.relative_to(ROOT)): digest for path, digest in SOURCE_LOCKS.items()
    }
    assert actual == expected
    return {"passed": True, "sha256": actual}


def ledger_audit() -> dict[str, object]:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    by_id = {item["id"]: item for item in obligations}

    expected_status = {
        "KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY": "proved",
        "EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM": "proved",
        "DEGREE_ONE_ANNULUS_IMMERSION_INJECTIVITY_NO_GO": "proved",
        "KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO": "proved",
        "KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION": "proved",
        "TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION": "proved",
        "GENERAL_ANNULUS_IMMERSION_LOWER_STRIP_NO_GO": "proved",
        "COMMON_COORDINATE_NESTED_ANNULUS_OUTER_CAP": "proved",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION": "proved",
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION": "open",
        "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING": "open",
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT": "open",
        "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION": "open",
        "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE": "open",
        "VIRTUAL_WAVE_MARKED_CORRESPONDENCE": "open",
        "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE": "open",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE": "open",
        "MLC": "open",
    }
    actual_status = {key: by_id[key]["status"] for key in expected_status}
    assert actual_status == expected_status

    model_dependencies = set(
        by_id["COMMON_COORDINATE_NESTED_ANNULUS_OUTER_CAP"]["dependencies"]
    )
    assert model_dependencies == {
        "TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION",
        "KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY",
        "EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM",
    }

    outer_dependencies = set(
        by_id["DIRECT_DECORATION_OUTER_CAP_FOOTPRINT"]["dependencies"]
    )
    assert outer_dependencies == {
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION",
        "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION",
        "KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT",
        "RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY",
        "CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO",
        "CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION",
        "KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY",
        "GENERAL_ANNULUS_IMMERSION_LOWER_STRIP_NO_GO",
        "DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE",
    }

    open_dependencies = set(
        by_id["DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION"][
            "dependencies"
        ]
    )
    assert open_dependencies == {
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION",
        "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION",
        "KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT",
        "NONPROPER_LABEL_HULL_PULLBACK_NO_GO",
        "KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY",
        "CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO",
        "CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION",
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT",
        "DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH",
    }

    counts = {
        status: sum(item["status"] == status for item in obligations)
        for status in ("imported", "proved", "open")
    }
    assert len(obligations) == 330
    assert counts == {"imported": 23, "proved": 235, "open": 72}
    return {
        "passed": True,
        "total": len(obligations),
        "counts": counts,
        "statuses": actual_status,
    }


def documentation_audit() -> dict[str, object]:
    abstract = ABSTRACT_NOTE.read_text(encoding="utf-8")
    outer = OUTER_NOTE.read_text(encoding="utf-8")

    abstract_required = [
        "This is a maximum, not merely",
        "Repetition of the same access path is",
        "Picard is then a contradiction",
        "global interior injectivity",
        "Central \\(J\\)-seam footprint computation",
        "VAAPC-I, UPTCR, or MLC",
    ]
    outer_required = [
        "Theorem 9.1: conformal ideal-boundary identification",
        "Theorem 9.2: component properness conditional on embedding",
        "Theorem 9.3: conditional exact outer-port criterion",
        "Proposition 4.2: degree-one immersion does not imply a lower strip",
        "reflects the declared central overlap",
        "not merely the path component",
        "Restricted canonical-resolution/KL-tile correspondence and sheet-sensitive actual",
        "\\(O\\)-/\\(J\\)-footprint exhaustion",
        "Eventual residence in one tile",
    ]
    assert all(token in abstract for token in abstract_required)
    assert all(token in outer for token in outer_required)

    forbidden = [
        "direct-decoration specialization of the positive theorem remains conditional",
        "first unresolved component is adjacent to an immersed deeper-equipotential outer side",
        "possible non-singleton prime-end cluster traces",
    ]
    joined = abstract + "\n" + outer
    assert all(token not in joined for token in forbidden)
    return {
        "passed": True,
        "abstract_markers": abstract_required,
        "outer_markers": outer_required,
        "forbidden_markers_absent": forbidden,
    }


def finite_formula_audit() -> dict[str, object]:
    """Check only the finite logic of footprint containment.

    The labels stand for the relative interiors of xi, lambda, eta and
    the two wrapping corners.  This verifies the open/closed distinction
    and the monotonic safe-set rule, not the analytic footprint theorem.
    """

    xi = "xi"
    left_corner = "p-"
    outer = "lambda"
    right_corner = "p+"
    eta = "eta"
    closed_port = {left_corner, outer, right_corner}
    open_outer_atom = {outer}
    open_tile_star = {xi, left_corner, outer, right_corner, eta}

    assert not closed_port <= open_outer_atom
    assert closed_port <= open_tile_star
    assert len(open_tile_star) == 3 + 2

    footprints = {
        "outer-a": closed_port,
        "outer-b": closed_port,
        "proper-left-corner": {left_corner},
    }
    safe_open_outer = {
        point
        for point, footprint in footprints.items()
        if footprint <= open_outer_atom
    }
    safe_tile_star = {
        point
        for point, footprint in footprints.items()
        if footprint <= open_tile_star
    }
    assert "outer-a" not in safe_open_outer
    assert {"outer-a", "outer-b"} <= safe_tile_star

    for q in range(1, 65):
        target_height = 1.0
        source_height = 2.0 ** (-q) * target_height
        assert 0.0 < source_height < target_height

    return {
        "passed": True,
        "closed_port": sorted(closed_port),
        "open_outer_atom": sorted(open_outer_atom),
        "open_tile_star": [xi, left_corner, outer, right_corner, eta],
        "safe_open_outer": sorted(safe_open_outer),
        "safe_tile_star": sorted(safe_tile_star),
        "tested_depth_gaps": [1, 64],
        "scope": "conditional common-coordinate finite logic only",
    }


def noninjective_immersion_diagnostic() -> dict[str, object]:
    """Numerically instantiate the proved same-tile countermodel.

    This checks arithmetic and implementation transcription only.  The
    existence proof in the note uses exact inequalities and the
    intermediate value theorem.
    """

    h = 0.1
    a = 3.0
    assert a > math.exp(2.0 * math.pi * h)
    lower = math.exp(-2.0 * math.pi * h)
    target = 0.75

    def r(d: float) -> float:
        return math.pi * d / (a * math.sin(math.pi * d))

    lo, hi = 1.0e-8, 1.0 - 1.0e-8
    for _ in range(100):
        mid = (lo + hi) / 2.0
        if r(mid) < target:
            lo = mid
        else:
            hi = mid
    d = (lo + hi) / 2.0
    assert lower < r(d) < 1.0

    rhs = -(2.0 * math.pi * 1j * d) / (
        a * (cmath.exp(2.0 * math.pi * 1j * d) - 1.0)
    )
    z = cmath.log(rhs) / (2.0 * math.pi * 1j)
    if z.imag <= 0.0:
        z += 1.0
    assert 0.0 < z.imag < h

    def f(value: complex) -> complex:
        return value + a * cmath.exp(2.0 * math.pi * 1j * value) / (
            2.0 * math.pi * 1j
        )

    collision_error = abs(f(z + d) - f(z))
    derivative_margin = abs(a * cmath.exp(2.0 * math.pi * 1j * z)) - 1.0
    assert collision_error < 1.0e-10
    assert derivative_margin > 0.0
    return {
        "passed": True,
        "h": h,
        "a": a,
        "d": d,
        "z_imaginary_part": z.imag,
        "collision_error": collision_error,
        "derivative_modulus_margin": derivative_margin,
        "scope": "diagnostic transcription check only",
    }


def main() -> None:
    result = {
        "source_locks": source_lock_audit(),
        "ledger": ledger_audit(),
        "documentation": documentation_audit(),
        "finite_formula": finite_formula_audit(),
        "noninjective_immersion": noninjective_immersion_diagnostic(),
        "scope": (
            "mechanical audit only; analytic proofs are in the cited notes; "
            "no VAAPC-I, UPTCR, rigidity, or MLC promotion"
        ),
        "passed": True,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
