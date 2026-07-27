"""Finite regressions for the conditional Kahn-collar embedding theorem.

The analytic theorem is proved in
``finite_horizon_kahn_collar_embedding.md``.  These checks source-lock the
inner-collar input, exercise finite inverse-germ coherence, reject automatic
safe-set uniqueness, and enforce the theorem's conditional/global scope.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
KAHN = ROOT / ".tmp_kl06_source" / "psiql2.tex"
KL = ROOT / ".tmp_kl08_source" / "psiql.tex"
NOTE = ROOT / "finite_horizon_kahn_collar_embedding.md"
LEDGER = ROOT / "proof_obligations.json"
OUT = ROOT / "finite_horizon_kahn_collar_validation_20260725.json"

EXPECTED_HASHES = {
    KAHN: "E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228",
    KL: "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def source_audit() -> dict[str, object]:
    hashes = {path: sha256(path) for path in EXPECTED_HASHES}
    assert hashes == EXPECTED_HASHES
    kahn = KAHN.read_text(encoding="utf-8")
    kl = KL.read_text(encoding="utf-8")
    kahn_phrases = [
        "Let $\\Lambda'$ be the component of $I^{-1}(\\Lambda)$ that is adjacent to $\\T$;",
        "is a covering map;",
        "it must have degree 1, because $I\\from \\T \\to \\T$ does.",
        "Therefore $I|_{\\Lambda'}$ is an embedding,",
    ]
    kl_phrases = [
        "$\\BY= Y \\sqcup_{e_i} \\hat A_i.$",
        "The embeddings $\\phi_i$ have disjoint images.",
        "where the map $j=j(i)$ is surjective but not necessarily injective.",
        "These embeddings extend to immersions",
    ]
    assert all(phrase in kahn for phrase in kahn_phrases)
    assert all(phrase in kl for phrase in kl_phrases)
    return {
        "passed": True,
        "sha256": {
            str(path.relative_to(ROOT)): value
            for path, value in hashes.items()
        },
        "kahn_inner_collar_phrases": kahn_phrases,
        "kl_gluing_phrases": kl_phrases,
    }


def finite_inverse_germ_audit() -> dict[str, object]:
    """Model inverse germs phi_j(x)=scale_j*x on (0,domain_j)."""

    scales = [
        Fraction(2, 3),
        Fraction(3, 5),
        Fraction(5, 7),
        Fraction(7, 11),
        Fraction(11, 13),
    ]
    domains = [
        Fraction(1, 2),
        Fraction(2, 5),
        Fraction(3, 8),
        Fraction(4, 11),
        Fraction(5, 14),
    ]

    cumulative = Fraction(1)
    admissible_base_bounds = []
    for scale, domain in zip(scales, domains):
        admissible_base_bounds.append(domain / cumulative)
        cumulative *= scale
    epsilon_0 = min(admissible_base_bounds) / 2
    assert epsilon_0 > 0

    collars = [epsilon_0]
    value = epsilon_0
    for scale, domain in zip(scales, domains):
        assert value < domain
        value *= scale
        collars.append(value)
    assert len(collars) == len(scales) + 1
    assert all(value > 0 for value in collars)

    return {
        "passed": True,
        "horizon_length": len(scales),
        "base_collar_width": str(epsilon_0),
        "collar_widths": [str(value) for value in collars],
        "finite_intersection_positive": True,
    }


def overlap_reflection_audit() -> dict[str, object]:
    """Commutation alone does not exclude a tile--central collision."""

    source_points = {"central:c", "tile:x"}
    target_quotient = {
        "central:q": "target-class:q",
        "tile:q": "target-class:q",
    }
    branch_images = {
        "central:c": "central:q",
        "tile:x": "tile:q",
    }
    source_quotient_without_reflection = {
        point: point for point in source_points
    }
    images = {
        point: target_quotient[branch_images[point]]
        for point in source_points
    }
    assert len(set(source_quotient_without_reflection.values())) == 2
    assert len(set(images.values())) == 1

    source_quotient_with_reflection = {
        "central:c": "source-class:cx",
        "tile:x": "source-class:cx",
    }
    assert len(set(source_quotient_with_reflection.values())) == 1

    return {
        "passed": True,
        "commuting_on_declared_overlap_is_insufficient": True,
        "collision_pair": sorted(source_points),
        "common_target_class": next(iter(images.values())),
        "repair": (
            "preimage of target central/tile overlap on the retained "
            "collar equals the declared source overlap"
        ),
    }


def safe_set_component_audit() -> dict[str, object]:
    """A finite circular model showing that a safe set need not be connected."""

    source_atoms = list(range(8))
    target_interval = {"a"}
    footprints = {
        0: {"a"},
        1: {"a"},
        2: {"b"},
        3: {"b"},
        4: {"a"},
        5: {"a"},
        6: {"b"},
        7: {"b"},
    }
    safe = {
        atom
        for atom in source_atoms
        if footprints[atom].issubset(target_interval)
    }
    assert safe == {0, 1, 4, 5}

    components = []
    unseen = set(safe)
    while unseen:
        seed = next(iter(unseen))
        component = {seed}
        changed = True
        while changed:
            changed = False
            for atom in list(unseen):
                neighbors = {(atom - 1) % 8, (atom + 1) % 8}
                if component.intersection(neighbors):
                    component.add(atom)
                    unseen.remove(atom)
                    changed = True
        unseen.discard(seed)
        components.append(sorted(component))
    components.sort()
    assert components == [[0, 1], [4, 5]]

    return {
        "passed": True,
        "safe_atoms": sorted(safe),
        "maximal_connected_components": components,
        "automatic_uniqueness": False,
    }


def enlargement_naturality_audit() -> dict[str, object]:
    old_points = {"p0", "p1", "p2", "p3"}
    new_points = {"q0", "q1", "q2", "q3"}
    protected_old = {"p0", "p1", "p2"}
    protected_new = {"q0", "q1", "q2"}
    a_n = {
        "q0": "p0",
        "q1": "p1",
        "q2": "p2",
        "q3": "p3",
    }
    old_footprints = {
        "p0": {"x"},
        "p1": {"x", "y"},
        "p2": {"z"},
        "p3": {"wild"},
    }
    new_footprints = {
        "q0": {"x+"},
        "q1": {"x+", "y+"},
        "q2": {"z+"},
        "q3": {"born"},
    }
    a_0 = {"x+": "x", "y+": "y", "z+": "z"}
    assert old_points == set(a_n.values())

    for q in protected_new:
        assert {a_0[x] for x in new_footprints[q]} == (
            old_footprints[a_n[q]]
        )

    old_interval = {"x", "y"}
    new_interval = {x for x, image in a_0.items() if image in old_interval}
    old_safe = {
        p
        for p, footprint in old_footprints.items()
        if p in protected_old and footprint.issubset(old_interval)
    }
    new_safe = {
        q
        for q, footprint in new_footprints.items()
        if q in protected_new and footprint.issubset(new_interval)
    }
    inverse_old_safe = {
        q
        for q, image in a_n.items()
        if q in protected_new and image in old_safe
    }
    assert new_safe == inverse_old_safe

    return {
        "passed": True,
        "protected_old": sorted(protected_old),
        "protected_new": sorted(protected_new),
        "old_safe": sorted(old_safe),
        "new_safe": sorted(new_safe),
        "unprotected_points_excluded": ["p3", "q3"],
        "safe_set_naturality": True,
    }


def documentation_and_ledger_audit() -> dict[str, object]:
    note = NOTE.read_text(encoding="utf-8")
    required = [
        "Theorem 1.1",
        "finite-horizon coherent collar embedding",
        "d_j\\geq2",
        "r_j>1",
        "Complete quotient-collision audit",
        "Collar overlap reflection",
        "relative overlap cartesianity",
        "Omitted-sheet and outer-exit ledger",
        "Conditional final-root enlargement theorem",
        "No automatic unique marked pullback",
        "prove or refute the desired period-uniform quadratic block estimate",
        "VAAPC-I",
        "MLC",
    ]
    missing = [phrase for phrase in required if phrase not in note]
    assert not missing, missing

    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    by_id = {item["id"]: item for item in obligations}
    expected_statuses = {
        "FINITE_HORIZON_KAHN_COLLAR_EMBEDDING": "proved",
        "PSI_QL_GLOBAL_INJECTIVITY_NO_GO": "proved",
        "KL_LOCALIZATION_SUBGROUP_REFLECTION_CRITERION": "proved",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION": "proved",
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION": "open",
        "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING": "open",
        "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION": "open",
        "DIRECT_DECORATION_TRACE_COLLAR_REALIZATION": "open",
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
            "Finite-horizon conditional collar embedding and safe-set "
            "regressions; no full KL pseudo-piece or uniform-width claim."
        ),
        "source_lock": source_audit(),
        "finite_inverse_germs": finite_inverse_germ_audit(),
        "overlap_reflection": overlap_reflection_audit(),
        "safe_set_components": safe_set_component_audit(),
        "enlargement_naturality": enlargement_naturality_audit(),
        "documentation_and_ledger": documentation_and_ledger_audit(),
    }
    OUT.write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
