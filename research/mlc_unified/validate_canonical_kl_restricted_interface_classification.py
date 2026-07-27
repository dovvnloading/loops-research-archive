"""Focused validation for the canonical/KL restricted-interface classification.

The analytic proofs are in
``canonical_kl_restricted_interface_classification.md``.  This script
locks the exact Kahn/KL source files, checks proof/document markers and
forbidden overclaims, runs finite diagnostics for the annulus-width and
base-change calculations, and audits ledger routing.  The finite checks
are diagnostics only; they do not prove the analytic theorems.
"""

from __future__ import annotations

import hashlib
import json
import math
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent
DOC = ROOT / "canonical_kl_restricted_interface_classification.md"
RESOLVED = ROOT / "resolved_intermediate_relative_ideal_boundary.md"
KAHN_PSI = ROOT / ".tmp_kl06_source" / "psiql2.tex"
KL_PSI = ROOT / ".tmp_kl08_source" / "psiql.tex"
KL_APPENDIX = ROOT / ".tmp_kl08_source" / "appendix.tex"
KL_MODULI = ROOT / ".tmp_kl08_source" / "moduli.tex"
LEDGER = ROOT / "proof_obligations.json"
OUT = ROOT / (
    "canonical_kl_restricted_interface_classification_validation_20260726.json"
)

EXPECTED_SHA = {
    KAHN_PSI: "E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228",
    KL_PSI: "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF",
    KL_APPENDIX: "05A13ED2D46CB9E2D188E6D96F4A2B639626F99657723118B4DE3479CD980916",
    KL_MODULI: "CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def require(text: str, needle: str, label: str) -> None:
    if needle not in text:
        raise AssertionError(f"missing {label}: {needle!r}")


def forbid(text: str, needle: str, label: str) -> None:
    if needle in text:
        raise AssertionError(f"forbidden {label}: {needle!r}")


def annulus_width_control() -> dict[str, object]:
    """Check the explicit unscaled degree-two width divergence."""

    rows: list[dict[str, float]] = []
    previous_gap = 0.0
    for epsilon in [1.0, 0.5, 0.1, 0.01]:
        target_width = 2.0 * math.pi / epsilon
        source_lower_bound = 4.0 * math.pi / epsilon
        gap = source_lower_bound - target_width
        if not math.isclose(gap, 2.0 * math.pi / epsilon, rel_tol=1e-12):
            raise AssertionError("annulus width identity failed")
        if gap <= previous_gap:
            raise AssertionError("width gap must increase as epsilon decreases")
        previous_gap = gap
        rows.append(
            {
                "epsilon": epsilon,
                "target_width": target_width,
                "source_collar_lower_bound": source_lower_bound,
                "unscaled_gap_lower_bound": gap,
            }
        )
    return {
        "rows": rows,
        "scope": (
            "Unscaled complete boundary-crossing widths only; this does "
            "not test a calibrated or source-specific response."
        ),
    }


def base_change_fiber_control() -> dict[str, object]:
    """Finite control for the exact fiber bijection in Proposition 8.1."""

    old_fiber = tuple(range(17))
    target_points = ("y0", "y1", "y2")
    cardinalities: dict[str, int] = {}
    for target in target_points:
        pulled_fiber = tuple((point, target) for point in old_fiber)
        if [point for point, _ in pulled_fiber] != list(old_fiber):
            raise AssertionError("base-change fiber bijection failed")
        cardinalities[target] = len(pulled_fiber)
    if set(cardinalities.values()) != {len(old_fiber)}:
        raise AssertionError("base change changed fiber cardinality")
    return {
        "old_fiber_size": len(old_fiber),
        "pulled_fiber_sizes": cardinalities,
        "scope": "Finite diagnostic for the exact set-theoretic fiber formula.",
    }


def tagged_label_control() -> dict[str, object]:
    """Check that repeated source labels are not identified."""

    source_labels = ("i0", "i1", "i2")
    target_label = {"i0": "j0", "i1": "j0", "i2": "j1"}
    local_components = {
        "i0": ("c0", "c1"),
        "i1": ("c0",),
        "i2": ("c0",),
    }
    tagged = {
        (label, component)
        for label in source_labels
        if target_label[label] == "j0"
        for component in local_components[label]
    }
    if tagged != {("i0", "c0"), ("i0", "c1"), ("i1", "c0")}:
        raise AssertionError("tagged source-label union lost multiplicity")
    return {
        "target": "j0",
        "tagged_components": sorted([list(item) for item in tagged]),
        "untagged_collision": "c0 occurs for both i0 and i1",
    }


def main() -> None:
    for path, expected in EXPECTED_SHA.items():
        actual = sha256(path)
        if actual != expected:
            raise AssertionError(
                f"source hash mismatch for {path}: {actual} != {expected}"
            )

    kahn = KAHN_PSI.read_text(encoding="utf-8", errors="replace")
    kl = KL_PSI.read_text(encoding="utf-8", errors="replace")
    appendix = KL_APPENDIX.read_text(encoding="utf-8", errors="replace")
    moduli = KL_MODULI.read_text(encoding="utf-8", errors="replace")
    doc = DOC.read_text(encoding="utf-8")
    resolved = RESOLVED.read_text(encoding="utf-8")

    for needle in [
        "Suppose that $I\\from \\aa{r'} \\to \\aa{r}$ is a holomorphic immersion",
        "$I|_{\\aa {\\rho'}}$ is an embedding",
        "uniformly greater than 1 when $r$ is bounded away from 1",
    ]:
        require(kahn, needle, "Kahn annulus source")

    for needle in [
        "$\\BY= Y \\sqcup_{e_i} \\hat A_i.$",
        "where the map $j=j(i)$ is surjective but not necessarily injective",
        "These embeddings extend to immersions $\\hat A_i\\ra \\hat B_j$",
        "extends continuously to the boundary of the",
        "$\\i(\\di \\BY)$ is not contained in $\\di\\BZ$",
    ]:
        require(kl, needle, "KL pseudo-piece source")

    require(
        appendix,
        "$\\LL(\\GG)$ and $\\WW(\\GG)=\\LL(\\GG)^{-1}$",
        "KL width convention",
    )
    for needle in [
        "uniformize $\\hat A$ by the horizontal  strip",
        "the group of deck transformations is generated by",
        "translation $z\\mapsto z+1$",
        "is represented",
        "as an interval $I$ on $\\R$",
    ]:
        require(moduli, needle, "KL strip source")

    for needle in [
        "For every supplied fixed same-source labeled canonical/Kahn--Lyubich",
        "Proposition 4.2 -- existence and based uniqueness",
        "Proposition 4.3 -- non-descent for a nontrivial kernel",
        "tagged total pullback",
        "Theorem 5.2 -- exact restriction enumeration",
        '"family" is deliberate',
        "D_{\\rm ext}=\\{\\zeta_-,\\zeta_+\\}",
        "Theorem 6.1 -- common cluster on the source-locked extension domain",
        "conservative, uncompressed candidate state",
        "C\\subset A_s",
        "Proposition 7.1 -- quadratic zero-modulus collar no-go",
        "degree-calibrated comparison",
        "Proposition 8.1 -- finite equalizer retiming preserves the defect",
        "Assume the based embedding lifts between these two covers",
        "Audit of the four nominated branches",
        "the four branches are logically exhaustive",
        "candidate retained state",
        "not asserted minimal, finite, Value-observable, or",
        "VAAPC-I",
        "UPTCR",
        "MLC.",
    ]:
        require(doc, needle, "proof document")

    for needle in [
        "\\overline K\\bigl(\\Lambda(N)\\bigr)",
        "\\overline K|_{\\Lambda(N)}",
        "unique branch constructible",
        "the only branch constructed",
        "Exhaustive four-branch audit",
        "Complete compact-path restriction groupoid",
    ]:
        forbid(doc, needle, "rejected overclaim")

    for needle in [
        "K_a",
        "L_a\\Phi_a^{-1}",
        "K_a=e_aq_a",
        "\\overline\\Phi_a(\\omega_-)=\\zeta_-",
        "\\overline\\Phi_a(\\omega_+)=\\zeta_+",
    ]:
        require(resolved, needle, "resolved-proof typing repair")

    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = ledger["obligations"]
    by_id = {item["id"]: item for item in obligations}
    theorem_id = "CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION"
    theorem = by_id[theorem_id]
    if theorem["status"] != "proved":
        raise AssertionError(f"{theorem_id} must be proved")

    expected_dependencies = {
        "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION",
        "KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT",
        "RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY",
        "CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO",
        "FINITE_HORIZON_KAHN_COLLAR_EMBEDDING",
    }
    if set(theorem["dependencies"]) != expected_dependencies:
        raise AssertionError(
            f"unexpected theorem dependencies: {theorem['dependencies']}"
        )

    for dependent in [
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT",
        "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION",
    ]:
        if by_id[dependent]["status"] != "open":
            raise AssertionError(f"{dependent} must remain open")
        if theorem_id not in by_id[dependent]["dependencies"]:
            raise AssertionError(f"{dependent} is missing {theorem_id}")

    global_ids = [
        "VIRTUAL_WAVE_MARKED_CORRESPONDENCE",
        "VIRTUAL_WAVE_HORIZON_CERTIFICATE",
        "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    ]
    for item_id in global_ids:
        if by_id[item_id]["status"] != "open":
            raise AssertionError(f"{item_id} must remain open")

    counts = Counter(item["status"] for item in obligations)
    expected_counts = Counter({"proved": 235, "open": 72, "imported": 23})
    if len(obligations) != 330 or counts != expected_counts:
        raise AssertionError(
            f"unexpected ledger state: total={len(obligations)}, counts={counts}"
        )

    diagnostics = {
        "annulus_width": annulus_width_control(),
        "base_change_fiber": base_change_fiber_control(),
        "tagged_labels": tagged_label_control(),
    }
    report = {
        "scope": (
            "Source locks, proof-marker and rejected-overclaim audit, finite "
            "annulus/base-change/tag diagnostics, ledger routing, and global "
            "status checks.  Diagnostics do not prove analytic claims."
        ),
        "sources": {
            str(path.relative_to(ROOT)): sha256(path)
            for path in EXPECTED_SHA
        },
        "proof_document_sha256": sha256(DOC),
        "resolved_proof_sha256": sha256(RESOLVED),
        "ledger_sha256": sha256(LEDGER),
        "diagnostics": diagnostics,
        "ledger": {
            "total": len(obligations),
            "counts": dict(counts),
            "theorem": theorem_id,
            "global_statuses": {
                item_id: by_id[item_id]["status"]
                for item_id in global_ids
            },
        },
        "result": "PASS",
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"result": "PASS", "output": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
