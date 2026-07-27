"""Mechanical audit for the actual KL tile/base injectivity reduction.

The analytic and covering-space proofs are in
``actual_kl_tile_injectivity_gate.md``.  This script locks the cited source
files, checks the exact source distinctions and ledger status boundary, and
tests only finite deck-algebra sanity cases.  It is not a proof of global
univalence of the KL ambient annulus immersion and cannot promote MLC.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
LEDGER = ROOT / "proof_obligations.json"
NOTE = ROOT / "actual_kl_tile_injectivity_gate.md"
OUT = ROOT / "kl_tile_injectivity_gate_validation_20260725.json"

SOURCE_LOCKS = {
    ROOT / ".tmp_kl08_source" / "macros.tex":
        "BD995DB17D787F0CCFD4DA905DC0AA54FCF00CA71AE144DCAD1C9A1FF7C134C7",
    ROOT / ".tmp_kl08_source" / "psiql.tex":
        "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF",
    ROOT / ".tmp_kl08_source" / "moduli.tex":
        "CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E",
    ROOT / ".tmp_kl06_source" / "pullback.tex":
        "7E0B43D74F2C6E4A4375F4A4F40271ABC6A289247B40FD5D0D8CB88ED6928E5C",
    ROOT / ".tmp_kl06_source" / "conclusions.tex":
        "C76471C8DB44C38A37E75AC58CCD5FE9160BE79E7E903C3FD03F861E25C34530",
    ROOT / ".tmp_kl06_source" / "psiql2.tex":
        "E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def source_lock_audit() -> dict[str, object]:
    actual = {
        str(path.relative_to(ROOT)): sha256(path)
        for path in SOURCE_LOCKS
    }
    expected = {
        str(path.relative_to(ROOT)): digest
        for path, digest in SOURCE_LOCKS.items()
    }
    assert actual == expected
    return {"passed": True, "sha256": actual}


def source_semantics_audit() -> dict[str, object]:
    macros = (ROOT / ".tmp_kl08_source" / "macros.tex").read_text(
        encoding="utf-8"
    )
    psiql = (ROOT / ".tmp_kl08_source" / "psiql.tex").read_text(
        encoding="utf-8"
    )
    pullback = (ROOT / ".tmp_kl06_source" / "pullback.tex").read_text(
        encoding="utf-8"
    )
    conclusions = (ROOT / ".tmp_kl06_source" / "conclusions.tex").read_text(
        encoding="utf-8"
    )
    psiql2 = (ROOT / ".tmp_kl06_source" / "psiql2.tex").read_text(
        encoding="utf-8"
    )

    checks = {
        "bold_U_macro": r"\def\BU{{\mathbf{U}}}" in macros,
        "tile_annulus_is_bold": (
            r"A=\BU^m  \sm K(f)" in psiql
            and "topological annulus" in psiql
        ),
        "ordinary_model_has_physical_nesting": (
            r"U^{n+1} \subset U^n" in pullback
            and "The embedding here is of course the inclusion" in pullback
        ),
        "dynamical_arrow_has_tile_isomorphisms": (
            r"isomorphism map $\hat A_i\ra \hat B_j $" in psiql
            and "branched covering" in psiql
        ),
        "inclusion_arrow_has_tile_immersions": (
            r"Given two puzzle pieces $Y\subset Z$" in psiql
            and r"extend to immersions $\hat A_i\ra \hat B_j$" in psiql
        ),
        "psiql_replaces_embedding_by_immersion": (
            "which was previously an embedding, and is now an immersion"
            in conclusions
        ),
        "source_uses_only_selected_end_properness": (
            "is still proper on the ends corresponding to" in conclusions
        ),
        "kahn_proves_only_inner_collar": (
            r"$I|_{\aa {\rho'}}$ is an embedding" in psiql2
            and r"Let $\Lambda'$ be the component" in psiql2
        ),
        "boundary_can_enter_target_interior": (
            r"$\i(\di \BY)$ is not contained in $\di\BZ$" in psiql
        ),
    }
    assert all(checks.values()), checks
    return {"passed": True, "checks": checks}


def ledger_audit() -> dict[str, object]:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    by_id = {item["id"]: item for item in obligations}

    expected_status = {
        "KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION": "proved",
        "KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO": "proved",
        "DEGREE_ONE_ANNULUS_IMMERSION_INJECTIVITY_NO_GO": "proved",
        "TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION": "proved",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION": "proved",
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION": "open",
        "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING": "open",
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT": "open",
        "VIRTUAL_WAVE_MARKED_CORRESPONDENCE": "open",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE": "open",
        "MLC": "open",
    }
    actual_status = {key: by_id[key]["status"] for key in expected_status}
    assert actual_status == expected_status

    reduction_dependencies = set(
        by_id["KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION"]["dependencies"]
    )
    assert reduction_dependencies == {"KL_DECORATION_ESCAPE_PUZZLE"}

    embedding_dependencies = set(
        by_id["DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING"][
            "dependencies"
        ]
    )
    assert embedding_dependencies == {
        "KL_DECORATION_ESCAPE_PUZZLE",
        "KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION",
        "TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION",
    }
    assert (
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION"
        not in embedding_dependencies
    )

    glue_statement = by_id[
        "TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION"
    ]["statement"]
    assert "Q intersect P_j=Q_i" in glue_statement
    assert "Full reflection over all of P_j is stronger than necessary" in (
        glue_statement
    )

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


def deck_algebra_sanity() -> dict[str, object]:
    """Check the integer cancellation used in the degree-one proof.

    A collision whose two lifted images differ by target deck shift ``k``
    is cancelled by shifting the second source lift by ``-k``.  For degree
    ``d`` the residual shift would be ``k-d*k`` if one incorrectly used
    the degree-one cancellation, demonstrating why the degree matters.
    """

    degree_one_cases = []
    for k in range(-20, 21):
        target_shift_before = k
        source_shift = -k
        target_shift_after = target_shift_before + source_shift
        assert target_shift_after == 0
        degree_one_cases.append(
            {
                "k": k,
                "source_shift": source_shift,
                "target_shift_after": target_shift_after,
            }
        )

    higher_degree_caveat = []
    for degree in (2, 3, 5):
        for k in (-3, -1, 1, 4):
            residual = k + degree * (-k)
            assert residual != 0
            higher_degree_caveat.append(
                {"degree": degree, "k": k, "residual": residual}
            )

    return {
        "passed": True,
        "degree_one_cases": degree_one_cases,
        "higher_degree_caveat": higher_degree_caveat,
    }


def documentation_audit() -> dict[str, object]:
    note = NOTE.read_text(encoding="utf-8")
    required = [
        "Tile/base equivalence",
        "Properness criterion",
        "Theorem 4.1",
        "The degree-one condition is essential",
        "Exact collision certificate",
        "Full properness is sufficient",
        "Why the physical-nesting proof does not apply",
        "Optional saturation audit: full overlap reflection",
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION",
        "kl_relative_overlap_cartesianity.md",
        "Full-overlap overconstraint",
        "Dynamical/inclusion-arrow conflation",
        "truncate to the proved embedded collar",
        "VAAPC-I, UPTCR, and MLC remain open",
    ]
    missing = [text for text in required if text not in note]
    assert not missing, missing
    return {"passed": True, "required_phrases": required}


def main() -> None:
    report = {
        "scope": (
            "Mechanical source/status/deck audit only; no proof of actual "
            "KL base-annulus univalence or any global MLC gate."
        ),
        "source_lock": source_lock_audit(),
        "source_semantics": source_semantics_audit(),
        "ledger": ledger_audit(),
        "deck_algebra": deck_algebra_sanity(),
        "documentation": documentation_audit(),
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
