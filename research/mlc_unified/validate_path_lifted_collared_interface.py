#!/usr/bin/env python3
"""Finite adversarial checks for a path-lifted marked interface.

These diagnostics isolate four necessary conditions for any proposed
source-realized direct-decoration trace interface:

1. a path lift is unique only after its starting sheet is fixed;
2. proper endpoint atoms do not imply properness on a whole KKL end interval;
3. a commuting non-cartesian square need not satisfy Beck--Chevalley;
4. an injective final-root enlargement can preserve the old square while
   introducing a new sheet over an old proof-used interval.

The checks are finite graph, interval, set, and dependency tests.  They do not
construct pseudo-pieces, Sobolev collars, analytic weldings, or an MLC proof.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Callable, Hashable, Mapping


HERE = Path(__file__).resolve().parent
LEDGER = HERE / "proof_obligations.json"


def based_path_lift_audit() -> dict[str, object]:
    """Use a connected two-sheet graph cover to expose unbased ambiguity."""

    # Both directed source edges project to the one target loop.  Together
    # they form the connected two-sheet cover s0 --e0--> s1 --e1--> s0.
    edges = {
        "e0": {"source": "s0", "target": "s1", "projection": "a"},
        "e1": {"source": "s1", "target": "s0", "projection": "a"},
    }
    vertices = ("s0", "s1")

    def lifts(
        target_word: tuple[str, ...], start: str | None = None
    ) -> list[tuple[str, tuple[str, ...], str]]:
        active = [
            (vertex, tuple(), vertex)
            for vertex in vertices
            if start is None or vertex == start
        ]
        for target_edge in target_word:
            successor = []
            for initial, lifted_word, current in active:
                for edge_name, edge in edges.items():
                    if (
                        edge["source"] == current
                        and edge["projection"] == target_edge
                    ):
                        successor.append(
                            (
                                initial,
                                lifted_word + (edge_name,),
                                str(edge["target"]),
                            )
                        )
            active = successor
        return active

    unbased = lifts(("a",))
    based_s0 = lifts(("a",), start="s0")
    based_s1 = lifts(("a",), start="s1")
    doubled_s0 = lifts(("a", "a"), start="s0")

    def projection(lifted_word: tuple[str, ...]) -> tuple[str, ...]:
        return tuple(str(edges[edge]["projection"]) for edge in lifted_word)

    assert len(unbased) == 2
    assert {record[1] for record in unbased} == {("e0",), ("e1",)}
    assert all(projection(record[1]) == ("a",) for record in unbased)
    assert based_s0 == [("s0", ("e0",), "s1")]
    assert based_s1 == [("s1", ("e1",), "s0")]
    assert doubled_s0 == [("s0", ("e0", "e1"), "s0")]

    return {
        "target_word": ["a"],
        "unbased_lift_count": len(unbased),
        "based_s0_lift_count": len(based_s0),
        "based_s1_lift_count": len(based_s1),
        "single_loop_changes_sheet": based_s0[0][0] != based_s0[0][2],
        "double_loop_closes": doubled_s0[0][0] == doubled_s0[0][2],
        "conclusion": (
            "the starting sheet/deck phase is necessary for a unique lift"
        ),
    }


def whole_end_interval_audit() -> dict[str, object]:
    """Distinguish endpoint-atom checks from whole-interval properness."""

    covering_intervals = ((0, 3), (3, 4), (4, 5))
    proper_atoms = (True, False, True, True, True)
    end_interval = covering_intervals[0]
    lo, hi = end_interval

    endpoint_atom_test = proper_atoms[lo] and proper_atoms[hi - 1]
    whole_interval_test = all(proper_atoms[index] for index in range(lo, hi))

    positive_control = (True, True, True, True, True)
    positive_whole_interval = all(
        positive_control[index] for index in range(lo, hi)
    )

    # This is the coherent Push-VIII obstruction r=(0, bottom, 2, 3, 4):
    # the two boundary atoms are proper but the middle of the one whole
    # covering end interval is not.
    assert endpoint_atom_test
    assert not whole_interval_test
    assert positive_whole_interval

    # An accepted component with nonproper atoms at both ends is not weldable
    # even under the submitted endpoint-atom convention.
    umbrella_component = (False, True, False)
    umbrella_endpoint_test = (
        umbrella_component[0] and umbrella_component[-1]
    )
    umbrella_whole_test = all(umbrella_component)
    assert not umbrella_endpoint_test
    assert not umbrella_whole_test

    return {
        "covering_end_interval": list(end_interval),
        "proper_atom_mask": list(proper_atoms),
        "endpoint_atom_classifier": endpoint_atom_test,
        "whole_interval_proper": whole_interval_test,
        "positive_control_whole_interval_proper": positive_whole_interval,
        "umbrella_component_weldable": umbrella_whole_test,
        "conclusion": (
            "properness must be checked on every atom/path in each whole "
            "proof-used covering end interval"
        ),
    }


def pushforward_sum(
    domain: tuple[Hashable, ...],
    codomain: tuple[Hashable, ...],
    map_to_codomain: Mapping[Hashable, Hashable],
    values: Mapping[Hashable, int],
) -> dict[Hashable, int]:
    """Finite-set pushforward by summing over fibers."""

    return {
        target: sum(
            values[source]
            for source in domain
            if map_to_codomain[source] == target
        )
        for target in codomain
    }


def pullback_function(
    domain: tuple[Hashable, ...],
    map_to_target: Mapping[Hashable, Hashable],
    values: Mapping[Hashable, int],
) -> dict[Hashable, int]:
    """Finite-set pullback by composition."""

    return {source: values[map_to_target[source]] for source in domain}


def beck_chevalley_audit() -> dict[str, object]:
    """Show that commutation without a cartesian fiber square is insufficient."""

    x = ("x0", "x1")
    y = ("y",)
    y_prime = ("y_prime",)
    x_prime = ("x0_prime",)

    f = {"x0": "y", "x1": "y"}
    vertical = {"y_prime": "y"}
    horizontal = {"x0_prime": "x0"}
    f_prime = {"x0_prime": "y_prime"}

    assert all(
        f[horizontal[source]] == vertical[f_prime[source]]
        for source in x_prime
    )

    witness = {"x0": 0, "x1": 1}
    left = pullback_function(
        y_prime,
        vertical,
        pushforward_sum(x, y, f, witness),
    )
    right = pushforward_sum(
        x_prime,
        y_prime,
        f_prime,
        pullback_function(x_prime, horizontal, witness),
    )
    assert left == {"y_prime": 1}
    assert right == {"y_prime": 0}
    assert left != right

    actual_fiber_product = {
        (source, target_prime)
        for source in x
        for target_prime in y_prime
        if f[source] == vertical[target_prime]
    }
    supplied_square = {("x0", "y_prime")}
    assert supplied_square < actual_fiber_product

    # Positive control: use the complete cartesian fiber product and verify
    # Beck--Chevalley on every basis function of R^X.
    cartesian_x_prime = ("x0_prime", "x1_prime")
    cartesian_horizontal = {
        "x0_prime": "x0",
        "x1_prime": "x1",
    }
    cartesian_f_prime = {
        "x0_prime": "y_prime",
        "x1_prime": "y_prime",
    }
    for basis_source in x:
        basis = {source: int(source == basis_source) for source in x}
        cartesian_left = pullback_function(
            y_prime,
            vertical,
            pushforward_sum(x, y, f, basis),
        )
        cartesian_right = pushforward_sum(
            cartesian_x_prime,
            y_prime,
            cartesian_f_prime,
            pullback_function(
                cartesian_x_prime,
                cartesian_horizontal,
                basis,
            ),
        )
        assert cartesian_left == cartesian_right

    return {
        "commuting_square": True,
        "cartesian_square": False,
        "actual_fiber_product_size": len(actual_fiber_product),
        "supplied_source_size": len(supplied_square),
        "witness_left": left,
        "witness_right": right,
        "beck_chevalley_holds": False,
        "cartesian_positive_control": True,
    }


def final_root_new_sheet_audit() -> dict[str, object]:
    """Expose a new enlarged sheet invisible to the restricted old square."""

    old_source = ("s0",)
    enlarged_source = ("S0", "Snew")
    old_target = ("I",)
    enlarged_target = ("I_plus",)

    source_embedding = {"s0": "S0"}
    target_embedding = {"I": "I_plus"}
    old_immersion = {"s0": "I"}
    enlarged_immersion = {
        "S0": "I_plus",
        "Snew": "I_plus",
    }
    assert set(old_immersion.values()) <= set(old_target)
    assert set(enlarged_immersion.values()) <= set(enlarged_target)

    restricted_square_commutes = all(
        target_embedding[old_immersion[source]]
        == enlarged_immersion[source_embedding[source]]
        for source in old_source
    )
    assert restricted_square_commutes

    old_pullback = {
        source for source in old_source if old_immersion[source] == "I"
    }
    embedded_old_pullback = {
        source_embedding[source] for source in old_pullback
    }
    complete_enlarged_pullback = {
        source
        for source in enlarged_source
        if enlarged_immersion[source] == target_embedding["I"]
    }
    born_sheets = complete_enlarged_pullback - embedded_old_pullback

    # Exact inverse-image transport on the old endpoint set can still hold:
    # it only checks the old embedded subdiagram.
    old_endpoints = {("s0", "left"), ("s0", "right")}
    endpoint_embedding = {
        ("s0", "left"): ("S0", "left"),
        ("s0", "right"): ("S0", "right"),
    }
    enlarged_endpoints = {
        ("S0", "left"),
        ("S0", "right"),
        ("Snew", "left"),
        ("Snew", "right"),
    }
    restricted_endpoint_inverse = {
        endpoint
        for endpoint in old_endpoints
        if endpoint_embedding[endpoint] in enlarged_endpoints
    }

    assert restricted_endpoint_inverse == old_endpoints
    assert embedded_old_pullback == {"S0"}
    assert complete_enlarged_pullback == {"S0", "Snew"}
    assert born_sheets == {"Snew"}
    assert len(old_pullback) == 1
    assert len(complete_enlarged_pullback) == 2

    collision_free_enlarged_source = ("S0",)
    collision_free_pullback = {
        source
        for source in collision_free_enlarged_source
        if enlarged_immersion[source] == target_embedding["I"]
    }
    assert collision_free_pullback == embedded_old_pullback

    return {
        "restricted_square_commutes": restricted_square_commutes,
        "restricted_old_endpoint_inverse_exact": True,
        "embedded_old_pullback": sorted(embedded_old_pullback),
        "complete_enlarged_pullback": sorted(complete_enlarged_pullback),
        "born_sheets": sorted(born_sheets),
        "old_lift_multiplicity": len(old_pullback),
        "enlarged_lift_multiplicity": len(complete_enlarged_pullback),
        "full_component_bijection": False,
        "no_birth_positive_control": True,
    }


def ledger_status_audit() -> dict[str, object]:
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = ledger["obligations"]
    by_id = {item["id"]: item for item in obligations}

    expected = {
        "DIRECT_DECORATION_PULLBACK_COMPACTIFICATION": "proved",
        "FINITE_LINEAR_LABEL_MARKING_ENUMERATOR": "proved",
        "PULL_PUSH_WELDING_WORD_COMPOSITION_NO_GO": "proved",
        "RELATIVE_COVER_LIFT": "proved",
        "PRIME_END_MARKING_ACTION_CRITERION": "proved",
        "PULLBACK_GAP_ENLARGEMENT_NATURALITY": "proved",
        "MARKED_PAIR_ENLARGEMENT_NATURALITY": "proved",
        "RETURN_ATLAS_ENLARGEMENT_NATURALITY": "proved",
        "KKL_IDEAL_PULLBACK_NATIVE": "imported",
        "DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION": "open",
        "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING": "open",
        "DEGREE_ONE_ANNULUS_IMMERSION_INJECTIVITY_NO_GO": "proved",
        "KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO": "proved",
        "KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION": "proved",
        "TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION": "proved",
        "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION": "proved",
        "KL_TILE_INTERIOR_HOMOGENEOUS_TRACE": "proved",
        "NONPROPER_LABEL_HULL_PULLBACK_NO_GO": "proved",
        "KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY": "proved",
        "EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM": "proved",
        "GENERAL_ANNULUS_IMMERSION_LOWER_STRIP_NO_GO": "proved",
        "COMMON_COORDINATE_NESTED_ANNULUS_OUTER_CAP": "proved",
        "DIRECT_DECORATION_OUTER_CAP_FOOTPRINT": "open",
        "DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION": "open",
        "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE": "open",
        "FINITE_LIVE_COMMON_REFINEMENT_FRONTIER": "open",
        "DIRECT_DECORATION_TRACE_COLLAR_REALIZATION": "open",
        "DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS": "open",
        "END_PLUMBING_TRACE_RESPONSE_CONTROL": "open",
        "H2_RESPONSE_REALIZATION": "open",
        "MBTT": "open",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE": "open",
        "MLC": "open",
    }
    actual = {item_id: by_id[item_id]["status"] for item_id in expected}
    assert actual == expected

    path_lift_dependencies = set(
        by_id["DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION"][
            "dependencies"
        ]
    )
    assert path_lift_dependencies == {
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
    all_depth_dependencies = set(
        by_id["DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE"][
            "dependencies"
        ]
    )
    assert "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION" in (
        all_depth_dependencies
    )
    assert "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION" in (
        all_depth_dependencies
    )
    assert "DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING" not in (
        all_depth_dependencies
    )

    counts = {
        status: sum(item["status"] == status for item in obligations)
        for status in ("imported", "proved", "open")
    }
    assert len(obligations) == 330
    assert counts == {"imported": 23, "proved": 235, "open": 72}

    return {
        "total": len(obligations),
        "counts": counts,
        "required_statuses": actual,
        "target": ledger["target"],
        "target_status": by_id[ledger["target"]]["status"],
    }


def main() -> None:
    checks: dict[str, Callable[[], dict[str, object]]] = {
        "based_path_lifts": based_path_lift_audit,
        "whole_end_interval": whole_end_interval_audit,
        "beck_chevalley": beck_chevalley_audit,
        "final_root_new_sheet": final_root_new_sheet_audit,
        "ledger": ledger_status_audit,
    }
    result = {name: check() for name, check in checks.items()}
    result["scope"] = (
        "finite adversarial diagnostics only; the analytic embedding, tile "
        "trace, and label-hull no-go require their written proofs; no path-lift "
        "exhaustion, welding compactness, UPTCR, or MLC theorem is promoted"
    )
    result["passed"] = True
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
