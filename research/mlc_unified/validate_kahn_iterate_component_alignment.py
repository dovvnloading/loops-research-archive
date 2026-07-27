"""Focused audit for Kahn iterate complementary-component alignment.

The analytic proof is in
kahn_iterate_complementary_component_alignment.md.  This validator locks
the primary-source files and their exact construction markers, checks a
finite set-level equalizer identity, verifies ledger routing, and preserves
all global open statuses.  It is diagnostic and does not replace the
connectedness or covering-space proof.
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent
DOC = ROOT / "kahn_iterate_complementary_component_alignment.md"
INTRO = ROOT / ".tmp_kl06_source" / "intro.tex"
KAHN = ROOT / ".tmp_kl06_source" / "psiql2.tex"
KL = ROOT / ".tmp_kl08_source" / "psiql.tex"
LEDGER = ROOT / "proof_obligations.json"
OUT = ROOT / "kahn_iterate_component_alignment_validation_20260725.json"

EXPECTED_SHA = {
    INTRO: "E7DD61396FEA927903D4DE4FD386E7AAEFD0BD3E2CEE1CE6F011680AD58144E0",
    KAHN: "E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228",
    KL: "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def require(text: str, needle: str, label: str) -> None:
    if needle not in text:
        raise AssertionError(f"missing {label}: {needle!r}")


def finite_equalizer_control() -> dict[str, object]:
    """Check only the set identity used in (4.2), not connectedness."""

    source = {"k0", "a", "b"}
    filled_source = {"k0"}
    target = {"K", "u", "v"}
    filled_target = {"K"}
    i_map = {"k0": "K", "a": "u", "b": "v"}
    f_map = {"k0": "K", "a": "v", "b": "u"}

    if {x for x in source if i_map[x] in filled_target} != filled_source:
        raise AssertionError("finite control violates i^{-1}(K)=K'")
    if {x for x in source if f_map[x] in filled_target} != filled_source:
        raise AssertionError("finite control violates f^{-1}(K)=K'")

    full_equalizer = {
        (x, y)
        for x in source
        for y in source
        if i_map[x] == f_map[y]
    }
    filled_equalizer = {
        (x, y)
        for x, y in full_equalizer
        if x in filled_source
    }
    complement_equalizer = full_equalizer - filled_equalizer
    fiber_product_of_complements = {
        (x, y)
        for x in source - filled_source
        for y in source - filled_source
        if i_map[x] == f_map[y]
    }
    if complement_equalizer != fiber_product_of_complements:
        raise AssertionError("finite complement/equalizer identity failed")

    # Pull back a surjective two-sheet map and verify the new projection is
    # still onto.  This checks the algebra in Theorem 5.1 only.
    p_space = {"p"}
    q_map = {"a": "p", "b": "p"}
    e_map = {"p": "u"}
    y_space = {"y"}
    target_map = {"y": "u"}
    resolved = {
        (p, y)
        for p in p_space
        for y in y_space
        if e_map[p] == target_map[y]
    }
    pulled = {
        (x, y)
        for x in q_map
        for y in y_space
        if e_map[q_map[x]] == target_map[y]
    }
    image = {(q_map[x], y) for x, y in pulled}
    if image != resolved:
        raise AssertionError("finite base-change surjectivity control failed")

    # For a map of annuli inducing multiplication by d on pi_1, the
    # pullback of the target universal cover has index |Z:dZ|=|d|
    # components.  Kahn's oriented degree is +1; degree two is retained as
    # an adversarial control showing why this hypothesis matters.
    annular_degree = 1
    pulled_universal_cover_components = abs(annular_degree)
    if pulled_universal_cover_components != 1:
        raise AssertionError("degree-one tile pullback should be connected")
    adversarial_degree = 2
    adversarial_components = abs(adversarial_degree)
    if adversarial_components != 2:
        raise AssertionError("degree-two annular control should split")

    return {
        "full_equalizer": sorted(map(list, full_equalizer)),
        "complement_equalizer": sorted(map(list, complement_equalizer)),
        "resolved_points": sorted(map(list, resolved)),
        "pulled_points": sorted(map(list, pulled)),
        "tile_pullback": {
            "oriented_degree": annular_degree,
            "component_index": pulled_universal_cover_components,
            "pulled_subgroup": 0,
            "degree_two_adversarial_component_index": adversarial_components,
        },
    }


def main() -> None:
    for path, expected in EXPECTED_SHA.items():
        actual = sha256(path)
        if actual != expected:
            raise AssertionError(
                f"source hash mismatch for {path}: {actual} != {expected}"
            )

    intro_text = INTRO.read_text(encoding="utf-8", errors="replace")
    kahn_text = KAHN.read_text(encoding="utf-8", errors="replace")
    kl_text = KL.read_text(encoding="utf-8", errors="replace")
    doc = DOC.read_text(encoding="utf-8")

    for needle in [
        "We will say a subset $K$ of $\\C$ is an \\fjset",
        "compact, connected, full, and has more than one element",
    ]:
        require(intro_text, needle, "Kahn FJ definition")

    for needle in [
        "exists when $g$ (or symmetrically, $h$) is an immersion",
        "underlying topological space of the (Riemann surface) pullback is the topological pullback",
        "the latter map has degree 1",
        "x \\in K' \\iff i(x) \\in K \\iff f(y) \\in K \\iff y \\in K'",
        "Therefore $\\BU''$ is connected.",
        "and hence $\\BU''$ is a disk.",
        "is itself a degree $d$  $\\psi$-polynomial-like map.",
        "$(i_n, f_n)\\from (\\BU^{n+1}, K^{n+1}) \\to (\\BU^n, K^n)",
        "we will often just denote $i_n$, $f_n$, and $K_n$ as $i$, $f$, and $K$",
        "for which $S \\sm A$ is connected",
    ]:
        require(kahn_text, needle, "Kahn source")

    for needle in [
        "There is a natural $\\psi$-ql map $\\BU^n\\ra \\BU^{n-1}$",
        "Let $(i,f) : \\BU'\\ra \\BU$ be a $\\psi$-ql map.",
        "Given a (geometric) puzzle piece $Y$ of depth $m$",
        "$\\hat A_i$ stands for a copy of $\\hat A$",
        "The embeddings $\\phi_i$ have disjoint images.",
        "where the map $j=j(i)$ is surjective but not necessarily injective.",
        "These embeddings extend to immersions $\\hat A_i\\ra \\hat B_j$",
        "$\\i(\\di \\BY)$ is not contained in $\\di\\BZ$",
        "the arcs $\\la_i$ form the {\\it outer boundary }",
    ]:
        require(kl_text, needle, "Kahn--Lyubich source")

    for needle in [
        "Theorem 4.1 -- unique complementary component",
        "Theorem 5.1 -- connected resolved base change",
        "Theorem 6.1 -- same-seed ambient component",
        "Theorem 6.2 -- tilewise resolved interior alignment",
        "j_\\iota(i)",
        "\\Phi_i",
        "family-valued over the **source** tile",
        "two labelled copies remain distinct",
        "Canonical/KL relation proper-end response",
        "CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO",
        "RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY",
        "KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT",
        "VAAPC-I",
        "UPTCR",
        "MLC",
    ]:
        require(doc, needle, "proof document")

    finite_control = finite_equalizer_control()

    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = ledger["obligations"]
    by_id = {item["id"]: item for item in obligations}
    theorem_id = "KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT"
    theorem = by_id[theorem_id]
    if theorem["status"] != "proved":
        raise AssertionError(f"{theorem_id} must be proved")
    for dependency in [
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION",
        "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION",
    ]:
        if dependency not in theorem["dependencies"]:
            raise AssertionError(f"{theorem_id} is missing {dependency}")

    for dependent in [
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT",
        "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION",
    ]:
        if by_id[dependent]["status"] != "open":
            raise AssertionError(f"{dependent} must remain open")
        if theorem_id not in by_id[dependent]["dependencies"]:
            raise AssertionError(f"{dependent} is missing {theorem_id}")

    for global_id in [
        "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    ]:
        if by_id[global_id]["status"] != "open":
            raise AssertionError(f"{global_id} must remain open")

    counts = Counter(item["status"] for item in obligations)
    expected_counts = Counter({"proved": 235, "open": 72, "imported": 23})
    if len(obligations) != 330 or counts != expected_counts:
        raise AssertionError(
            f"unexpected ledger state: total={len(obligations)}, counts={counts}"
        )

    report = {
        "scope": (
            "Diagnostic source-lock, finite equalizer identity, ledger routing, "
            "and global-status audit for the Kahn iterate complementary-component "
            "alignment theorem."
        ),
        "sources": {
            str(path.relative_to(ROOT)): sha256(path)
            for path in EXPECTED_SHA
        },
        "proof_document_sha256": sha256(DOC),
        "ledger_sha256": sha256(LEDGER),
        "finite_controls": finite_control,
        "ledger": {
            "total": len(obligations),
            "counts": dict(counts),
            "theorem": theorem_id,
            "global_statuses": {
                item_id: by_id[item_id]["status"]
                for item_id in [
                    "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE",
                    "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
                    "MLC",
                ]
            },
        },
        "result": "PASS",
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"result": "PASS", "output": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
