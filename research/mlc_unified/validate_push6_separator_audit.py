"""Independent checks for the Research Push VI assessment.

The positive checks validate only:

* bundle integrity;
* the abstract finite mask compiler on its declared schema;
* exact Schur-complement associativity for the submitted resistor subclass;
* repository status and dependency typing.

The adversarial checks deliberately expose cases outside that subclass.
Nothing here proves Sobolev trace realization, a finite dynamical atomization,
protected-overlay equivariance, response compactness, MBTT, or MLC.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import itertools
import json
from fractions import Fraction
from pathlib import Path
import random
import sys
from typing import Any

import sympy as sp


HERE = Path(__file__).resolve().parent
BUNDLE = HERE.parent / "mlc_research_push_6_bundle" / "push6"
LEDGER = HERE / "proof_obligations.json"
ASSESSMENT = HERE / "research_push_6_assessment_and_integration.md"
OUT = HERE / "push6_independent_audit_20260725.json"
sys.dont_write_bytecode = True


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, BUNDLE / filename)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {filename}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


cmc = load_module("push6_contact_mask_compiler", "contact_mask_compiler.py")
sca = load_module("push6_separator_contact_audit", "separator_contact_audit.py")


def manifest_checks() -> dict[str, Any]:
    expected: dict[str, str] = {}
    for line in (BUNDLE / "SHA256SUMS_PUSH6.txt").read_text(
        encoding="utf-8"
    ).splitlines():
        digest, filename = line.split(maxsplit=1)
        expected[filename] = digest

    actual = {name: sha256(BUNDLE / name) for name in expected}
    matches = {name: actual[name] == digest for name, digest in expected.items()}
    return {
        "entry_count": len(expected),
        "all_hashes_match": all(matches.values()),
        "matches": matches,
    }


def brute_scc(vertices: list[str], edges: dict[str, set[str]]) -> list[list[str]]:
    reach = {vertex: {vertex, *edges.get(vertex, set())} for vertex in vertices}
    changed = True
    while changed:
        changed = False
        for vertex in vertices:
            expanded = set().union(*(reach[target] for target in tuple(reach[vertex])))
            if not expanded <= reach[vertex]:
                reach[vertex].update(expanded)
                changed = True

    unseen = set(vertices)
    components: list[list[str]] = []
    while unseen:
        vertex = min(unseen)
        component = sorted(
            target
            for target in vertices
            if target in reach[vertex] and vertex in reach[target]
        )
        components.append(component)
        unseen.difference_update(component)
    return sorted(components, key=lambda component: (len(component), component))


def compiler_checks() -> dict[str, Any]:
    sample = json.loads(
        (BUNDLE / "contact_mask_example.json").read_text(encoding="utf-8")
    )
    expected = json.loads(
        (BUNDLE / "contact_mask_example_output.json").read_text(encoding="utf-8")
    )
    result = cmc.compile_contact(sample)

    atoms = set(sample["atoms"])
    running = set(atoms)
    partitions_hold = True
    recurrence_holds = True
    for stage, symbol in zip(result["stages"], sample["word"]):
        classes = [
            set(stage["G_genuine_glue"]),
            set(stage["T_zero_energy_transport"]),
            set(stage["O_root_side_only"]),
            set(stage["Z_double_inactive"]),
        ]
        partitions_hold &= set().union(*classes) == atoms
        partitions_hold &= sum(map(len, classes)) == len(atoms)
        recurrence_holds &= set(stage["mask_before"]) == running
        shared = set(sample["symbols"][symbol]["shared"])
        tau = sample["symbols"][symbol]["tau"]
        running = {tau[label] for label in running & shared}
        recurrence_holds &= set(stage["mask_after"]) == running

    rng = random.Random(6142026)
    graph_trials = 0
    tarjan_holds = True
    for size in range(9):
        vertices = [f"v{index}" for index in range(size)]
        for _ in range(100):
            edges = {
                vertex: {
                    target for target in vertices if rng.random() < 0.25
                }
                for vertex in vertices
            }
            tarjan_holds &= cmc.tarjan(vertices, edges) == brute_scc(
                vertices, edges
            )
            graph_trials += 1

    # This is the packet's own counterexample to its semantic label:
    # the supplied word kills the mask, although the union graph is cyclic.
    scc_overapproximation_exposed = (
        result["masks"][-1] == []
        and bool(result["recurrent_neutral_components"])
    )

    duplicate_mask = copy.deepcopy(sample)
    duplicate_mask["initial_mask"] = ["a0", "a0"]
    duplicate_initial_mask_silently_normalized = (
        cmc.compile_contact(duplicate_mask)["masks"][0] == ["a0"]
    )

    return {
        "sample_semantic_match": result == expected,
        "four_way_partition_holds_on_sample": partitions_hold,
        "declared_mask_recurrence_holds_on_sample": recurrence_holds,
        "tarjan_random_graph_trials": graph_trials,
        "tarjan_matches_reachability_oracle": tarjan_holds,
        "scc_overapproximation_exposed": scc_overapproximation_exposed,
        "sample_final_word_mask": result["masks"][-1],
        "sample_union_graph_recurrent_components": result[
            "recurrent_neutral_components"
        ],
        "duplicate_initial_mask_silently_normalized": (
            duplicate_initial_mask_silently_normalized
        ),
    }


def all_small_symbols(size: int):
    for shared_bits in itertools.product((False, True), repeat=size):
        shared = frozenset(
            index for index, bit in enumerate(shared_bits) if bit
        )
        for permutation in itertools.permutations(range(size)):
            for conductance in (
                tuple(1 for _ in range(size)),
                tuple(index + 1 for index in range(size)),
            ):
                yield sca.Symbol(shared, tuple(permutation), conductance)


def response_checks() -> dict[str, Any]:
    exhaustive_cases = 0
    exhaustive_holds = True
    for size in (1, 2):
        symbols = list(all_small_symbols(size))
        for symbol in symbols:
            for depth in range(5):
                word = [symbol] * depth
                one, one_masks = sca.one_shot_response(word, size)
                recursive, recursive_masks = sca.recursive_response(word, size)
                exhaustive_holds &= one == recursive
                exhaustive_holds &= one_masks == recursive_masks
                exhaustive_holds &= one == one.T
                exhaustive_cases += 1

        for left in symbols:
            for right in symbols:
                for bits in itertools.product((0, 1), repeat=3):
                    word = [left if bit == 0 else right for bit in bits]
                    one, one_masks = sca.one_shot_response(word, size)
                    recursive, recursive_masks = sca.recursive_response(word, size)
                    exhaustive_holds &= one == recursive
                    exhaustive_holds &= one_masks == recursive_masks
                    exhaustive_cases += 1

    random_reports = [
        sca.exact_network_trials(seed=seed, trials=100)
        for seed in (0, 1, 2, 42, 20260725, 20260726, 2**31 - 1)
    ]
    random_holds = all(report["pass"] for report in random_reports)

    geometry = sca.geom_bypass_check()

    # A floating internal zero mode has a valid minimized response, but the
    # submitted routine rejects it because it demands det(C) != 0.
    floating = sp.Matrix([[1, -1, 0], [-1, 1, 0], [0, 0, 0]])
    singular_mode_rejected = False
    try:
        sca.schur_response(floating, ground=0, terminals=[1])
    except RuntimeError:
        singular_mode_rejected = True

    # Repeating one physical terminal should impose an equality constraint,
    # not duplicate the coefficient in both rows and columns.
    edge = sp.Matrix([[1, -1], [-1, 1]])
    repeated = sca.schur_response(edge, ground=0, terminals=[1, 1])
    test_value = sp.Matrix([1, 1])
    represented_energy = (test_value.T * repeated * test_value)[0]
    repeated_terminal_bug_exposed = represented_energy == 4

    return {
        "small_exhaustive_cases": exhaustive_cases,
        "small_exhaustive_associativity_holds": exhaustive_holds,
        "additional_random_trials": sum(
            report["trials"] for report in random_reports
        ),
        "additional_random_seeds": [
            report["seed"] for report in random_reports
        ],
        "additional_random_trials_hold": random_holds,
        "rectangle_separator_example_passes": geometry[
            "separator_capture_pass"
        ],
        "floating_internal_zero_mode_rejected": singular_mode_rejected,
        "repeated_terminal_lift_matrix": str(repeated),
        "repeated_terminal_energy_on_equality_diagonal": str(
            represented_energy
        ),
        "repeated_terminal_bug_exposed": repeated_terminal_bug_exposed,
    }


def atom_map_counterexample() -> dict[str, Any]:
    # On a shared external ray the normalized height map is t -> d*t.
    # If v is the first positive cut, (0,v) is an atom, whereas its image
    # (0,d*v) crosses the cut v and cannot be one atom of the same partition.
    d = 4
    first_positive_cut_numerator = 1
    first_positive_cut_denominator = 16
    image_numerator = d * first_positive_cut_numerator
    image_denominator = first_positive_cut_denominator
    crosses_first_cut = (
        image_numerator * first_positive_cut_denominator
        > first_positive_cut_numerator * image_denominator
    )
    return {
        "degree": d,
        "first_atom": "(0,1/16)",
        "image": "(0,1/4)",
        "image_crosses_first_positive_cut": crosses_first_cut,
        "single_atom_map_impossible": crosses_first_cut,
        "correct_replacement": (
            "set-level image or one-to-many incidence plus endpoint and "
            "trace-restriction data"
        ),
    }


def relational_repair_certificate() -> dict[str, Any]:
    degree = 4
    contact_right = Fraction(1, degree)
    vertices = {
        Fraction(0),
        Fraction(1, 64),
        contact_right,
        Fraction(1),
    }

    changed = True
    while changed:
        changed = False
        additions = {
            degree * vertex
            for vertex in vertices
            if Fraction(0) <= vertex <= contact_right
        }
        if not additions <= vertices:
            vertices.update(additions)
            changed = True

    ordered = sorted(vertices)
    atoms = list(zip(ordered[:-1], ordered[1:]))
    shared_atoms = [
        atom for atom in atoms if atom[0] >= 0 and atom[1] <= contact_right
    ]
    relations: dict[str, list[str]] = {}
    endpoint_closure = True
    for left, right in shared_atoms:
        image_left = degree * left
        image_right = degree * right
        endpoint_closure &= image_left in vertices and image_right in vertices
        targets = [
            target
            for target in atoms
            if image_left <= target[0] and target[1] <= image_right
        ]
        relations[f"({left},{right})"] = [
            f"({target[0]},{target[1]})" for target in targets
        ]

    one_to_many_occurs = any(
        len(targets) > 1 for targets in relations.values()
    )
    return {
        "degree": degree,
        "forward_saturated_vertices": [str(vertex) for vertex in ordered],
        "finite_vertex_count": len(vertices),
        "all_shared_atom_image_endpoints_are_vertices": endpoint_closure,
        "one_to_many_occurs": one_to_many_occurs,
        "relations": relations,
        "scope": (
            "finite interval model for the conditional relational repair; "
            "not a source realization of the KL binary contact portrait"
        ),
    }


def ledger_checks() -> dict[str, Any]:
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = ledger["obligations"]
    by_id = {item["id"]: item for item in obligations}
    statuses = {
        status: sum(item["status"] == status for item in obligations)
        for status in ("imported", "proved", "open")
    }

    broad_open = {
        "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE",
        "FINITE_LIVE_COMMON_REFINEMENT_FRONTIER",
        "DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS",
        "DIRECT_DECORATION_TRACE_COLLAR_REALIZATION",
        "END_PLUMBING_TRACE_RESPONSE_CONTROL",
        "H2_RESPONSE_REALIZATION",
        "MBTT",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    }
    rejected_nodes = {
        "DIRECT_DECORATION_CONTACT_MASK_AUTOMATON",
        "GEOMETRIC_SEPARATOR_RESPONSE_RECURSION",
        "CO_MOVING_PHYSICAL_RESPONSE_COCYCLE",
        "CONTACT_TRANSIENT_RECURRENT_DICHOTOMY",
        "BLOCKWISE_FINITE_FEATURE_GRAMIAN_GAP",
        "CONTACT_AWARE_RESPONSE_COCYCLE_COMPACTNESS_AND_VALUE_OBSERVABILITY",
    }
    adopted = by_id["BINARY_DIRECT_DECORATION_NESTED_SEPARATOR_CALCULUS"]
    assessment = ASSESSMENT.read_text(encoding="utf-8")

    return {
        "total": len(obligations),
        **statuses,
        "adopted_node_proved": adopted["status"] == "proved",
        "adopted_node_dependencies_proved": all(
            by_id[dependency]["status"] in {"proved", "imported"}
            for dependency in adopted["dependencies"]
        ),
        "broad_gates_remain_open": all(
            by_id[node_id]["status"] == "open" for node_id in broad_open
        ),
        "rejected_nodes_absent": rejected_nodes.isdisjoint(by_id),
        "assessment_disclaims_mlc": (
            "VAAPC-I, H2, MBTT, H3, H4, UPTCR, and MLC remain open."
            in assessment
        ),
    }


def main() -> None:
    manifest = manifest_checks()
    compiler = compiler_checks()
    response = response_checks()
    atom_map = atom_map_counterexample()
    relational_repair = relational_repair_certificate()
    ledger = ledger_checks()

    required = {
        "manifest": manifest["all_hashes_match"],
        "compiler_sample": compiler["sample_semantic_match"],
        "compiler_partition": compiler["four_way_partition_holds_on_sample"],
        "compiler_recurrence": compiler[
            "declared_mask_recurrence_holds_on_sample"
        ],
        "tarjan_oracle": compiler["tarjan_matches_reachability_oracle"],
        "scc_overapproximation_exposed": compiler[
            "scc_overapproximation_exposed"
        ],
        "finite_response_associativity": response[
            "small_exhaustive_associativity_holds"
        ]
        and response["additional_random_trials_hold"],
        "separator_example": response["rectangle_separator_example_passes"],
        "singular_mode_limitation_exposed": response[
            "floating_internal_zero_mode_rejected"
        ],
        "repeated_terminal_bug_exposed": response[
            "repeated_terminal_bug_exposed"
        ],
        "single_atom_map_counterexample": atom_map[
            "single_atom_map_impossible"
        ],
        "relational_repair_finite": relational_repair[
            "all_shared_atom_image_endpoints_are_vertices"
        ]
        and relational_repair["one_to_many_occurs"],
        "adopted_node_proved": ledger["adopted_node_proved"],
        "dependencies_discharged": ledger[
            "adopted_node_dependencies_proved"
        ],
        "broad_status_boundary": ledger["broad_gates_remain_open"],
        "rejected_nodes_absent": ledger["rejected_nodes_absent"],
        "mlc_disclaimer_present": ledger["assessment_disclaims_mlc"],
    }
    all_checks = all(required.values())
    payload = {
        "artifact": "PUSH6_INDEPENDENT_SEPARATOR_AUDIT",
        "date": "2026-07-25",
        "status": (
            "PUSH6_NARROW_SEPARATOR_RESULT_VALID"
            if all_checks
            else "FAILED"
        ),
        "required_checks": required,
        "all_checks": all_checks,
        "manifest": manifest,
        "compiler": compiler,
        "finite_response": response,
        "atom_map_counterexample": atom_map,
        "relational_repair": relational_repair,
        "ledger": ledger,
        "scope": (
            "integrity, finite combinatorics, finite-network algebra, "
            "counterexamples, and ledger typing only; no analytic trace "
            "cocycle, uniform transition, UPTCR, or MLC proof"
        ),
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(payload["status"])
    print(json.dumps(payload, indent=2))
    if not all_checks:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
