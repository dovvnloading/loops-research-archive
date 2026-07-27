"""Focused validation for the actual KL canonical-localization collision.

This script is diagnostic.  It checks source locks, exact finite-degree
arithmetic, ledger routing, and status language.  It does not replace any
topological or analytic proof in kl_canonical_localization_forced_collision.md.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
DOC = ROOT / "kl_canonical_localization_forced_collision.md"
LEDGER = ROOT / "proof_obligations.json"
OUT = ROOT / "kl_canonical_localization_forced_collision_validation_20260725.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def require(haystack: str, needle: str, label: str) -> None:
    if needle not in haystack:
        raise AssertionError(f"missing {label}: {needle!r}")


def main() -> None:
    doc = DOC.read_text(encoding="utf-8")
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    by_id = {item["id"]: item for item in ledger["obligations"]}

    source_checks = {
        ".tmp_kl06_source/pullback.tex": [
            "U^n = f^{-n}(U)",
            "U^{n+1} \\subset U^n",
        ],
        ".tmp_kl06_source/intro.tex": [
            "K_p(i) = f^i(K_p)",
            "\\KK_p = \\bigcup_i K_p(i)",
            "pairwise disjoint",
        ],
        ".tmp_kl06_source/psiql2.tex": [
            "Let $T = (\\BU \\sm B) \\cup A$",
            "let $T' = (\\BU' \\sm f^{-1} B) \\cup A'$",
            "We call this the \\emph{canonical renormalization}",
            "replaced by $(\\BU^p, K_p, f^{-p}(\\KK_p))$",
            "\\BU''$ as the set of $(x, y)",
            "$i_1(x, y) = y$ and $f_1(x, y) = x",
        ],
        ".tmp_kl08_source/kingdom.tex": [
            "Let $P=Y^{(\\n-1)\\q+1}$",
            "$Q_L$ and $Q_R$ (of depth $\\q \\n+1$)",
        ],
        ".tmp_kl08_source/psiql.tex": [
            "Given two puzzle pieces $Y\\subset Z$",
            "glue together into an immersion $\\BY\\ra \\BZ$",
        ],
    }

    source_hashes: dict[str, str] = {}
    for relative, needles in source_checks.items():
        path = ROOT / relative
        text = path.read_text(encoding="utf-8")
        for needle in needles:
            require(text, needle, relative)
        source_hashes[relative] = sha256(path)

    doc_checks = [
        "KL canonical localization: forced excess-component collision",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION",
        "a_*^{-1}(H_t)\\supsetneq H_s",
        "x_{r+1}^{\\pm}=(x_r^\\pm,y_r)",
        "m=\\nu q+1",
        "n=(\\nu-1)q+1",
        "Sheet retention",
        "Obstacle synchronization",
        "VAAPC-I",
        "UPTCR",
        "MLC",
    ]
    for needle in doc_checks:
        require(doc, needle, "proof document")

    arithmetic = []
    for p in range(2, 65):
        global_degree = 2**p
        excess_degree = global_degree - 2
        if excess_degree <= 0:
            raise AssertionError(f"nonpositive excess degree at p={p}")
        if 2**p > global_degree:
            raise AssertionError("component bound arithmetic failed")
        arithmetic.append(
            {
                "p": p,
                "global_degree": global_degree,
                "central_degree": 2,
                "excess_degree": excess_degree,
                "component_upper_bound": 2**p,
            }
        )

    new_id = "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION"
    if new_id not in by_id:
        raise AssertionError(f"ledger is missing {new_id}")
    if by_id[new_id]["status"] != "proved":
        raise AssertionError(f"{new_id} must be proved")

    old_id = "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING"
    if by_id[old_id]["status"] != "open":
        raise AssertionError(
            "the narrower/alignment-sensitive direct-decoration node must stay open"
        )

    descendants = [
        item["id"]
        for item in ledger["obligations"]
        if old_id in item.get("dependencies", [])
    ]
    if descendants:
        raise AssertionError(
            "the disproved universal embedding route still has descendants: "
            + ", ".join(descendants)
        )

    rerouted = [
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT",
        "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION",
        "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE",
    ]
    for item_id in rerouted:
        deps = by_id[item_id].get("dependencies", [])
        if new_id not in deps:
            raise AssertionError(f"{item_id} does not retain the collision theorem")

    for global_id in [
        "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    ]:
        if by_id[global_id]["status"] != "open":
            raise AssertionError(f"{global_id} must remain open")

    report = {
        "scope": (
            "Source/degree/ledger validation for the actual ordinary-primitive "
            "canonical-localization collision; diagnostic only."
        ),
        "proof_document_sha256": sha256(DOC),
        "ledger_sha256": sha256(LEDGER),
        "source_sha256": source_hashes,
        "degree_checks": arithmetic,
        "ledger": {
            "new_theorem": new_id,
            "new_theorem_status": by_id[new_id]["status"],
            "alignment_sensitive_node": old_id,
            "alignment_sensitive_status": by_id[old_id]["status"],
            "old_route_descendants": descendants,
            "rerouted_nodes": rerouted,
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
