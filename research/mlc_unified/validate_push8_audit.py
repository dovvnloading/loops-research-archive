#!/usr/bin/env python3
"""Adversarial validation for the conservative Push-VIII integration."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import random
import sys
from copy import deepcopy
from pathlib import Path


ROOT = Path(__file__).resolve().parent
BUNDLE = ROOT.parent / "mlc_research_push_8_bundle"


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def manifest_audit() -> dict:
    entries = {}
    for line in (BUNDLE / "SHA256SUMS_PUSH8.txt").read_text(
        encoding="utf-8"
    ).splitlines():
        digest, name = line.split(maxsplit=1)
        entries[name] = digest.lower()

    failures = {}
    for name, expected in entries.items():
        data = (BUNDLE / name).read_bytes()
        raw = hashlib.sha256(data).hexdigest()
        normalized = hashlib.sha256(data.replace(b"\r\n", b"\n")).hexdigest()
        if expected not in {raw, normalized}:
            failures[name] = {
                "expected": expected,
                "raw": raw,
                "normalized_lf": normalized,
            }
    return {"entries": len(entries), "failures": failures}


def atomwise_covering_consistent(payload: dict) -> bool:
    vertices = payload["source_vertex_cov_image"]
    return all(
        set((vertices[j], vertices[j + 1]))
        == {atom["cov_micro"], atom["cov_micro"] + 1}
        for j, atom in enumerate(payload["source_atoms"])
    )


def global_degree_one_candidate(payload: dict) -> bool:
    if not atomwise_covering_consistent(payload):
        return False
    atoms = payload["source_atoms"]
    n = payload["target_micro_count"]
    vertices = payload["source_vertex_cov_image"]
    signs = [
        1
        if (vertices[j], vertices[j + 1])
        == (atom["cov_micro"], atom["cov_micro"] + 1)
        else -1
        for j, atom in enumerate(atoms)
    ]
    return (
        len(atoms) == n
        and len({atom["cov_micro"] for atom in atoms}) == n
        and len(set(signs)) == 1
    )


def compiler_audit() -> dict:
    compiler = load_module(
        "marked_interface_compiler_v2",
        BUNDLE / "marked_interface_compiler_v2.py",
    )
    tests = load_module(
        "push8_tests", BUNDLE / "test_marked_interface_compiler_v2.py"
    )

    deterministic = tests.deterministic_tests()
    report = tests.randomized_oracle_test()
    assert report == {
        "seed": 20260725,
        "trials": 1500,
        "compiled": 1221,
        "obstructed": 279,
        "false_positive": 0,
        "false_negative": 0,
        "maximal_marking_mismatch": 0,
    }

    success = json.loads((BUNDLE / "marked_interface_success.json").read_text())
    vertices = success["source_vertex_cov_image"]
    fixture_bad_atoms = []
    for j, atom in enumerate(success["source_atoms"]):
        endpoints = (vertices[j], vertices[j + 1])
        if set(endpoints) != {atom["cov_micro"], atom["cov_micro"] + 1}:
            fixture_bad_atoms.append(
                {
                    "atom": j,
                    "covering_label": atom["cov_micro"],
                    "endpoint_images": list(endpoints),
                }
            )
    assert [x["atom"] for x in fixture_bad_atoms] == [0, 3, 6, 9]

    rng = random.Random(20260725)
    atomwise = 0
    global_candidates = 0
    accepted = 0
    accepted_inconsistent = 0
    accepted_empty = 0
    accepted_no_good = 0
    for _ in range(1500):
        payload = tests.random_payload(rng)
        coherent = atomwise_covering_consistent(payload)
        atomwise += int(coherent)
        global_candidates += int(global_degree_one_candidate(payload))
        try:
            out = compiler.compile_marked_interface(payload)
        except compiler.MarkingFailure:
            continue
        accepted += 1
        accepted_inconsistent += int(not coherent)
        records = [
            record
            for component_records in out["selected_action_details"][
                "immersion_components"
            ].values()
            for record in component_records
        ]
        accepted_empty += int(not records)
        accepted_no_good += int(
            not any(r["proper"] or r["end_proper"] for r in records)
        )

    assert (
        atomwise,
        global_candidates,
        accepted,
        accepted_inconsistent,
        accepted_empty,
        accepted_no_good,
    ) == (1, 0, 1221, 1220, 28, 402)

    mutated = deepcopy(success)
    for atom in mutated["source_atoms"]:
        atom["cov_micro"] = (atom["cov_micro"] + 3) % mutated[
            "target_micro_count"
        ]
    old = compiler.compile_marked_interface(success)
    new = compiler.compile_marked_interface(mutated)
    decision_keys = [
        "base_immersion_endpoints",
        "selected_action_endpoints",
        "selected_action_details",
        "response_only_trace_endpoints",
        "valid_action_marking_count",
    ]
    assert all(old[key] == new[key] for key in decision_keys)

    end_counterexample = {
        "target_micro_count": 5,
        "seam_vertex": 0,
        "mandatory_ideal_endpoints": [0, 3, 5],
        "trace_overlay_endpoints": [0, 3, 5],
        "source_atoms": [
            {"imm_micro": 0, "cov_micro": 0},
            {"imm_micro": None, "cov_micro": 1},
            {"imm_micro": 2, "cov_micro": 2},
            {"imm_micro": 3, "cov_micro": 3},
            {"imm_micro": 4, "cov_micro": 4},
        ],
        "source_vertex_cov_image": [0, 1, 2, 3, 4, 5],
    }
    end_out = compiler.compile_marked_interface(end_counterexample)
    first_record = end_out["selected_action_details"]["immersion_components"][
        "0"
    ][0]
    assert first_record["source_atoms"] == [0, 1, 2]
    assert first_record["proper"] is False
    assert first_record["end_proper"] is True

    umbrella_counterexample = {
        "target_micro_count": 3,
        "seam_vertex": 0,
        "mandatory_ideal_endpoints": [0, 1, 2, 3],
        "trace_overlay_endpoints": [0, 1, 2, 3],
        "source_atoms": [
            {"imm_micro": None, "cov_micro": 0},
            {"imm_micro": 1, "cov_micro": 1},
            {"imm_micro": None, "cov_micro": 2},
        ],
        "source_vertex_cov_image": [0, 1, 2, 3],
    }
    umbrella_out = compiler.compile_marked_interface(umbrella_counterexample)
    umbrella_record = umbrella_out["selected_action_details"][
        "immersion_components"
    ]["1"][0]
    assert umbrella_out["status"] == "compiled"
    assert umbrella_record["proper"] is False
    assert umbrella_record["end_proper"] is False

    return {
        "deterministic_tests": deterministic,
        "randomized_report": report,
        "success_fixture_bad_atoms": fixture_bad_atoms,
        "random_atomwise_consistent": atomwise,
        "random_global_degree_one_candidates": global_candidates,
        "accepted_atomwise_inconsistent": accepted_inconsistent,
        "accepted_empty_immersion": accepted_empty,
        "accepted_without_proper_or_end_proper": accepted_no_good,
        "covering_labels_decision_invariant_under_mutation": True,
        "end_proper_counterexample_reported_true": True,
        "umbrella_counterexample_compiles_without_weldable_component": True,
    }


def pull_push_counterexample() -> dict:
    # R1=P2=I, with P1=A and R2=B.
    A = ((1, 1), (0, 1))
    B = ((1, 0), (1, 1))

    def multiply(X, Y):
        return tuple(
            tuple(sum(X[i][k] * Y[k][j] for k in range(2)) for j in range(2))
            for i in range(2)
        )

    composite_pair = multiply(A, B)
    chronological = multiply(B, A)
    assert composite_pair == ((2, 1), (1, 1))
    assert chronological == ((1, 1), (1, 2))
    assert composite_pair != chronological
    return {
        "componentwise_composite": composite_pair,
        "chronological_product": chronological,
        "equal": False,
    }


def ledger_audit() -> dict:
    ledger = json.loads((ROOT / "proof_obligations.json").read_text())
    obligations = ledger["obligations"]
    by_id = {item["id"]: item for item in obligations}
    expected = {
        "FINITE_LINEAR_LABEL_MARKING_ENUMERATOR": "proved",
        "PULL_PUSH_WELDING_WORD_COMPOSITION_NO_GO": "proved",
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
        "DIRECT_DECORATION_TRACE_COLLAR_REALIZATION": "open",
        "DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS": "open",
        "END_PLUMBING_TRACE_RESPONSE_CONTROL": "open",
        "MBTT": "open",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE": "open",
        "MLC": "open",
    }
    statuses = {key: by_id[key]["status"] for key in expected}
    assert statuses == expected
    assert "FIXED_HORIZON_MARKED_BINARY_INTERFACE_COMPLETION" not in by_id
    assert "UNIVERSAL_MANDATORY_ENDPOINT_VISIBILITY_AND_REPAIR" not in by_id
    path_lift_dependencies = set(
        by_id["DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION"][
            "dependencies"
        ]
    )
    assert "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION" in (
        path_lift_dependencies
    )
    all_depth_dependencies = set(
        by_id["DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE"][
            "dependencies"
        ]
    )
    assert "KL_CANONICAL_LOCALIZATION_FORCED_COLLISION" in (
        all_depth_dependencies
    )
    counts = {
        status: sum(item["status"] == status for item in obligations)
        for status in ("imported", "proved", "open")
    }
    # Later hostile audits split two overbroad promotions into conditional
    # positive controls, explicit no-go theorems, and open KL-specific gates.
    assert len(obligations) == 330
    assert counts == {"imported": 23, "proved": 235, "open": 72}
    return {"total": len(obligations), "counts": counts, "statuses": statuses}


def documentation_audit() -> dict:
    assessment = (
        ROOT / "research_push_8_assessment_and_integration.md"
    ).read_text(encoding="utf-8")
    required = [
        "The submitted immersion-pullback formula is not proved",
        "The end-proper classifier is false",
        "Exact failure of word functoriality",
        "Path-lifted marked correspondence realization",
        "MLC",
    ]
    missing = [phrase for phrase in required if phrase not in assessment]
    assert not missing
    return {"required_phrases": required, "missing": missing}


def main() -> None:
    result = {
        "manifest": manifest_audit(),
        "compiler": compiler_audit(),
        "pull_push": pull_push_counterexample(),
        "ledger": ledger_audit(),
        "documentation": documentation_audit(),
    }
    assert not result["manifest"]["failures"]
    result["passed"] = True
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
