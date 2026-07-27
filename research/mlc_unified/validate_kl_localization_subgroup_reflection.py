"""Mechanical audit for the KL localization subgroup-reflection criterion.

The proof is topological and appears in
``kl_localization_subgroup_reflection_gate.md``.  This script source-locks
the KL distinction between Cartesian pullback and functorial localization,
checks finite cyclic-coset models of the subgroup criterion, and enforces
the open status of the actual KL and global MLC gates.
"""

from __future__ import annotations

from collections import Counter
from math import gcd
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
KL06_ARCHIVE = ROOT / ".tmp_kl06_source.tar"
KL08_ARCHIVE = ROOT / ".tmp_kl08_source.tar"
KL06_PSIQL = ROOT / ".tmp_kl06_source" / "psiql2.tex"
KL08_PSIQL = ROOT / ".tmp_kl08_source" / "psiql.tex"
NOTE = ROOT / "kl_localization_subgroup_reflection_gate.md"
LEDGER = ROOT / "proof_obligations.json"
OUT = ROOT / "kl_localization_subgroup_reflection_validation_20260725.json"

EXPECTED_ARCHIVE_HASHES = {
    KL06_ARCHIVE: (
        "3A63FC9773DB8B60ED4A0EB9A1C551E6F66C08E66AB92C36F4E2B482570AB817"
    ),
    KL08_ARCHIVE: (
        "DA8FCF924793267421F80BE3E17CD7EB2B72CD4F5B08E3F5A38E2161EC608234"
    ),
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def source_audit() -> dict[str, object]:
    actual_hashes = {
        path: sha256(path) for path in EXPECTED_ARCHIVE_HASHES
    }
    assert actual_hashes == EXPECTED_ARCHIVE_HASHES

    kahn = KL06_PSIQL.read_text(encoding="utf-8")
    kl = KL08_PSIQL.read_text(encoding="utf-8")
    kahn_phrases = [
        "the \\emph{pullback} of these two morphisms",
        "the underlying topological space of the (Riemann surface) pullback is the topological pullback.",
        "If $g$ is injective (or surjective, or bijective),",
        "$i_n \\circ f_{n+1} = f_n \\circ i_{n+1}$",
        "These operations define a functor from marked Riemann surfaces",
        "$\\hat g$ is an immersion if $g$ is an immersion",
        "equivalent paths are mapped to equivalent paths.",
    ]
    kl_phrases = [
        "where the map $j=j(i)$ is surjective but not necessarily injective.",
        "These embeddings extend to immersions",
        "$\\i(\\di \\BY)$ is not contained in $\\di\\BZ$",
    ]
    assert all(phrase in kahn for phrase in kahn_phrases)
    assert all(phrase in kl for phrase in kl_phrases)

    return {
        "passed": True,
        "archive_sha256": {
            path.name: value for path, value in actual_hashes.items()
        },
        "kahn_pullback_localization_phrases": kahn_phrases,
        "kl_inclusion_immersion_phrases": kl_phrases,
    }


def cyclic_coset_audit() -> dict[str, object]:
    """Test H_s=mZ, H_t=nZ, a_*(k)=qk.

    Lift existence is n | q*m.  The reflected subgroup is
    (n/gcd(n,q))Z.  The induced map Z/mZ -> Z/nZ is injective exactly when
    that reflected step is m.
    """

    cases: list[dict[str, object]] = []
    for m in range(1, 13):
        for n in range(1, 13):
            for q in range(1, 8):
                if (q * m) % n:
                    continue
                reflected_step = n // gcd(n, q)
                reflection = reflected_step == m
                images = [(q * k) % n for k in range(m)]
                injective = len(set(images)) == m
                assert injective == reflection
                cases.append(
                    {
                        "m": m,
                        "n": n,
                        "q": q,
                        "reflection": reflection,
                        "injective": injective,
                    }
                )

    # First exact failure: 2Z maps into Z under the identity.  The class
    # gamma=1 is outside 2Z but maps into Z, collapsing the two source cosets.
    m, n, q, gamma = 2, 1, 1, 1
    assert (q * m) % n == 0
    assert gamma % m != 0
    assert (q * gamma) % n == 0
    assert len({(q * k) % n for k in range(m)}) == 1

    return {
        "passed": True,
        "tested_existing_lifts": len(cases),
        "reflection_injectivity_equivalence": True,
        "failure_certificate": {
            "H_s": "2Z",
            "H_t": "Z",
            "a_star": "identity",
            "gamma": 1,
        },
    }


def documentation_and_ledger_audit() -> dict[str, object]:
    note = NOTE.read_text(encoding="utf-8")
    required = [
        "Theorem 1.1",
        "subgroup-reflection criterion",
        "a_*^{-1}(H_t)=H_s",
        "Exact failure certificate",
        "Equivalent path-reflection formulation",
        "functorial, not asserted Cartesian",
        "Theorem 1.3",
        "forced canonical subgroup defect",
        "conditional revised-or-restricted route",
        "pointed coset set",
        "physical embedding",
        "VAAPC-I, UPTCR, and MLC",
    ]
    missing = [phrase for phrase in required if phrase not in note]
    assert not missing, missing

    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    by_id = {item["id"]: item for item in obligations}
    expected_statuses = {
        "KL_LOCALIZATION_SUBGROUP_REFLECTION_CRITERION": "proved",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION": "proved",
        "PSI_QL_GLOBAL_INJECTIVITY_NO_GO": "proved",
        "KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION": "proved",
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION": "open",
        "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING": "open",
        "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION": "open",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE": "open",
        "MLC": "open",
    }
    actual_statuses = {
        key: by_id[key]["status"] for key in expected_statuses
    }
    assert actual_statuses == expected_statuses
    forced_collision_dependencies = set(
        by_id["KL_CANONICAL_LOCALIZATION_FORCED_COLLISION"]["dependencies"]
    )
    assert forced_collision_dependencies == {
        "KL_LOCALIZATION_SUBGROUP_REFLECTION_CRITERION",
        "KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION",
    }
    embedding_dependencies = set(
        by_id["DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING"][
            "dependencies"
        ]
    )
    assert "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION" in (
        embedding_dependencies
    )
    counts = Counter(item["status"] for item in obligations)
    assert len(obligations) == 330
    assert counts == Counter({"proved": 235, "open": 72, "imported": 23})

    return {
        "passed": True,
        "required_documentation_phrases": required,
        "total": len(obligations),
        "counts": dict(counts),
        "statuses": actual_statuses,
    }


def main() -> None:
    report = {
        "scope": (
            "Exact cover-subgroup criterion plus the source-locked actual "
            "canonical-stage failure of reflection; no positive full "
            "embedding or global gate is proved."
        ),
        "source_lock": source_audit(),
        "cyclic_coset_regressions": cyclic_coset_audit(),
        "documentation_and_ledger": documentation_and_ledger_audit(),
    }
    OUT.write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
