#!/usr/bin/env python3
"""Mechanical audit for KL relative overlap cartesianity.

The analytic/topological proof is in ``kl_relative_overlap_cartesianity.md``.
This script locks the primary source files, checks finite relation models,
audits the exact ledger dependency correction, and records the result.
Finite models diagnose quotient logic; they do not prove KL base-annulus
univalence, a Wave-horizon theorem, UPTCR, or MLC.
"""

from __future__ import annotations

import cmath
import hashlib
import json
import math
from pathlib import Path
from typing import Hashable, Iterable


ROOT = Path(__file__).resolve().parent
LEDGER = ROOT / "proof_obligations.json"
NOTE = ROOT / "kl_relative_overlap_cartesianity.md"
OUT = ROOT / "kl_relative_overlap_cartesianity_validation_20260725.json"

SOURCE_LOCKS = {
    ROOT / ".tmp_kl08_source" / "psiql.tex":
        "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF",
    ROOT / ".tmp_kl08_source" / "kingdom.tex":
        "5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7",
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
    psiql = (ROOT / ".tmp_kl08_source" / "psiql.tex").read_text(
        encoding="utf-8"
    )
    kingdom = (ROOT / ".tmp_kl08_source" / "kingdom.tex").read_text(
        encoding="utf-8"
    )
    checks = {
        "path_quotient": (
            r"Let $\BY$ be the space of paths" in psiql
            and "modulo  homotopy through" in psiql
        ),
        "finite_star_gluing": (
            r"$\BY= Y \sqcup_{e_i} \hat A_i.$" in psiql
        ),
        "tiles_disjoint": (
            r"The embeddings $\phi_i$ have disjoint images." in psiql
        ),
        "exact_central_tile_overlap": (
            r"the image $\phi_i(\hat A_i)$ overlaps with  $Y$ by $Y_i$"
            in psiql
        ),
        "inclusion_component_surjective": (
            r"where the map $j=j(i)$ is surjective but not necessarily injective"
            in psiql
        ),
        "inclusion_tiles_only_immersive": (
            r"extend to immersions $\hat A_i\ra \hat B_j$" in psiql
        ),
        "direct_pair_univalent_pullbacks": (
            r"$Q_L$ and $Q_R$" in kingdom
            and r"two univalent $f^\q$-pullbacks" in kingdom
        ),
    }
    assert all(checks.values()), checks
    return {"passed": True, "checks": checks}


class UnionFind:
    def __init__(self, nodes: Iterable[Hashable]) -> None:
        self.parent = {node: node for node in nodes}

    def find(self, node: Hashable) -> Hashable:
        parent = self.parent[node]
        if parent != node:
            self.parent[node] = self.find(parent)
        return self.parent[node]

    def union(self, left: Hashable, right: Hashable) -> None:
        root_left = self.find(left)
        root_right = self.find(right)
        if root_left != root_right:
            self.parent[root_right] = root_left


def quotient_partition(
    nodes: tuple[Hashable, ...],
    relations: tuple[tuple[Hashable, Hashable], ...],
) -> dict[Hashable, Hashable]:
    uf = UnionFind(nodes)
    for left, right in relations:
        uf.union(left, right)
    return {node: uf.find(node) for node in nodes}


def induced_map_is_injective(
    source_nodes: tuple[Hashable, ...],
    source_relations: tuple[tuple[Hashable, Hashable], ...],
    target_nodes: tuple[Hashable, ...],
    target_relations: tuple[tuple[Hashable, Hashable], ...],
    piece_map: dict[Hashable, Hashable],
) -> bool:
    source_classes = quotient_partition(source_nodes, source_relations)
    target_classes = quotient_partition(target_nodes, target_relations)

    # Compatibility: one source class has one target class.
    image_by_source_class: dict[Hashable, Hashable] = {}
    for node in source_nodes:
        source_class = source_classes[node]
        target_class = target_classes[piece_map[node]]
        previous = image_by_source_class.setdefault(source_class, target_class)
        assert previous == target_class

    values = list(image_by_source_class.values())
    return len(values) == len(set(values))


def positive_nonfull_reflection_control() -> dict[str, object]:
    """Full reflection can fail while relative reflection and gluing hold."""

    cs_q = ("Cs", "q")
    ts_q = ("Ts", "q")
    ts_extra = ("Ts", "extra")
    ct_q = ("Ct", "q")
    ct_extra = ("Ct", "extra")
    tt_q = ("Tt", "q")
    tt_extra = ("Tt", "extra")

    source_nodes = (cs_q, ts_q, ts_extra)
    source_relations = ((cs_q, ts_q),)
    target_nodes = (ct_q, ct_extra, tt_q, tt_extra)
    target_relations = ((ct_q, tt_q), (ct_extra, tt_extra))
    piece_map = {
        cs_q: ct_q,
        ts_q: tt_q,
        ts_extra: tt_extra,
    }

    glued_injective = induced_map_is_injective(
        source_nodes,
        source_relations,
        target_nodes,
        target_relations,
        piece_map,
    )
    source_tile_overlap = {ts_q}
    target_full_overlap = {tt_q, tt_extra}
    target_relative_overlap = {tt_q}
    full_preimage = {
        node
        for node in (ts_q, ts_extra)
        if piece_map[node] in target_full_overlap
    }
    relative_preimage = {
        node
        for node in (ts_q, ts_extra)
        if piece_map[node] in target_relative_overlap
    }

    assert glued_injective
    assert full_preimage != source_tile_overlap
    assert relative_preimage == source_tile_overlap
    return {
        "passed": True,
        "glued_map_injective": glued_injective,
        "full_reflection": False,
        "relative_cartesianity": True,
        "extra_target_overlap_has_source_central_mate": False,
    }


def missing_relative_fiber_negative_control() -> dict[str, object]:
    """Piece embeddings and commutation do not replace relative reflection."""

    cs_overlap = ("Cs", "overlap")
    cs_extra = ("Cs", "extra")
    ts_overlap = ("Ts", "overlap")
    ts_extra = ("Ts", "extra")
    ct_overlap = ("Ct", "overlap")
    ct_extra = ("Ct", "extra")
    tt_overlap = ("Tt", "overlap")
    tt_extra = ("Tt", "extra")

    source_nodes = (cs_overlap, cs_extra, ts_overlap, ts_extra)
    source_relations = ((cs_overlap, ts_overlap),)
    target_nodes = (ct_overlap, ct_extra, tt_overlap, tt_extra)
    target_relations = (
        (ct_overlap, tt_overlap),
        (ct_extra, tt_extra),
    )
    piece_map = {
        cs_overlap: ct_overlap,
        cs_extra: ct_extra,
        ts_overlap: tt_overlap,
        ts_extra: tt_extra,
    }

    glued_injective = induced_map_is_injective(
        source_nodes,
        source_relations,
        target_nodes,
        target_relations,
        piece_map,
    )
    assert not glued_injective
    assert source_relations == ((cs_overlap, ts_overlap),)
    assert piece_map[cs_extra] == ct_extra
    assert piece_map[ts_extra] == tt_extra
    return {
        "passed": True,
        "central_piece_map_injective": True,
        "tile_piece_map_injective": True,
        "declared_overlap_commutes": True,
        "relative_cartesianity": False,
        "glued_map_injective": False,
        "first_excess_mixed_pair": [list(cs_extra), list(ts_extra)],
    }


def component_identity_audit() -> dict[str, object]:
    """Finite set model of Q intersect P_j as the union over component fibers."""

    source_components = {
        "Q0": {"q00", "q01"},
        "Q1": {"q10"},
        "Q2": {"q20", "q21", "q22"},
    }
    target_components = {
        "P0": {"q00", "q01", "p0_extra"},
        "P1": {"q10", "p1_extra"},
        "P2": {"q20", "q21", "q22", "p2_extra"},
    }
    component_map = {"Q0": "P0", "Q1": "P1", "Q2": "P2"}
    q_points = set().union(*source_components.values())

    for source_name, target_name in component_map.items():
        intersection = q_points & target_components[target_name]
        fiber_union = set().union(
            *(
                points
                for name, points in source_components.items()
                if component_map[name] == target_name
            )
        )
        assert intersection == fiber_union == source_components[source_name]

    # Noninjective component labels expose why surjectivity alone is not enough.
    noninjective_map = {"Q0": "P0", "Q1": "P0", "Q2": "P2"}
    p0_fiber_union = set().union(
        *(
            points
            for name, points in source_components.items()
            if noninjective_map[name] == "P0"
        )
    )
    assert p0_fiber_union == source_components["Q0"] | source_components["Q1"]
    assert p0_fiber_union != source_components["Q0"]

    return {
        "passed": True,
        "bijective_component_map_gives_single_component_intersection": True,
        "surjective_noninjective_control_gives_multiple_components": True,
    }


def analytic_rectangle_sanity() -> dict[str, object]:
    """Check the exact inequalities and collision in the exponential model."""

    # Heights are represented as integer multiples of pi/8.
    central_height_units = 9 - (-1)
    tile_height_units = 17 - 7
    union_height_units = 17 - (-1)
    period_units = 16
    assert central_height_units < period_units
    assert tile_height_units < period_units
    assert union_height_units > period_units

    # 0 lies central-only; 2*pi*i lies tile-only.
    zero_y_units = 0
    two_pi_y_units = 16
    assert -1 < zero_y_units < 9
    assert not (7 < zero_y_units < 17)
    assert 7 < two_pi_y_units < 17
    assert not (-1 < two_pi_y_units < 9)
    assert abs(cmath.exp(0) - cmath.exp(2j * math.pi)) < 1e-12

    # The negative-imaginary direction 3*pi/2 is outside Cs but inside Ts.
    negative_imag_units = 12
    assert not (-1 < negative_imag_units < 9)
    assert 7 < negative_imag_units < 17

    return {
        "passed": True,
        "central_and_tile_restrictions_below_one_period": True,
        "union_exceeds_one_period": True,
        "exact_collision_pair": ["0", "2*pi*i"],
        "negative_imaginary_slit_covered_by_target_tile": True,
    }


def ledger_audit() -> dict[str, object]:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    by_id = {item["id"]: item for item in obligations}

    expected_status = {
        "TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION": "proved",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION": "proved",
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION": "open",
        "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING": "open",
        "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE": "open",
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
    assert "KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION" in embedding_dependencies
    assert "TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION" in embedding_dependencies
    assert "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION" in (
        embedding_dependencies
    )
    assert (
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION"
        not in embedding_dependencies
    )

    criterion = by_id["TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION"][
        "statement"
    ]
    strong_question = by_id[
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION"
    ]["statement"]
    assert "Q intersect P_j=Q_i" in criterion
    assert "Full reflection over all of P_j is stronger than necessary" in criterion
    assert "non-gating open question" in strong_question

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
        "full_reflection_is_embedding_dependency": False,
    }


def documentation_audit() -> dict[str, object]:
    note = NOTE.read_text(encoding="utf-8")
    required = [
        "Proposition 3.0 -- equivalence-relation reflection",
        "Theorem 3.1 -- exact relative gluing criterion",
        "KL component identity",
        "Relative cartesianity follows from full tile injectivity",
        "Corrected full pseudo-piece embedding theorem",
        "Full overlap reflection is not necessary",
        "Commutation and piecewise embeddings are not sufficient",
        "Full tiles versus retained collars",
        "VAAPC-I, UPTCR, and MLC remain open",
    ]
    missing = [phrase for phrase in required if phrase not in note]
    assert not missing, missing
    return {"passed": True, "required_phrases": required}


def main() -> None:
    report = {
        "scope": (
            "Source lock, exact finite quotient regressions, analytic "
            "rectangle sanity, and ledger correction. No proof of actual "
            "KL base-annulus univalence or any global MLC gate."
        ),
        "source_lock": source_lock_audit(),
        "source_semantics": source_semantics_audit(),
        "positive_nonfull_reflection_control":
            positive_nonfull_reflection_control(),
        "missing_relative_fiber_negative_control":
            missing_relative_fiber_negative_control(),
        "component_identity": component_identity_audit(),
        "analytic_rectangle_sanity": analytic_rectangle_sanity(),
        "ledger": ledger_audit(),
        "documentation": documentation_audit(),
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
