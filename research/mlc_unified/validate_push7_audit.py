#!/usr/bin/env python3
"""Reproduce the decisive finite checks in the Research Push VII audit.

This validator deliberately confirms both the positive finite-label behavior
and the current compiler's false-positive acceptance.  It does not certify
the analytic pseudo-trace or response claims.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import sys
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
UNIFIED = ROOT / "research" / "mlc_unified"
BUNDLE = ROOT / "research" / "mlc_research_push_7_bundle" / "push7"
ASSESSMENT = UNIFIED / "research_push_7_assessment_and_integration.md"
LEDGER = UNIFIED / "proof_obligations.json"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_compiler() -> Any:
    path = BUNDLE / "binary_contact_trace_compiler.py"
    spec = importlib.util.spec_from_file_location("push7_compiler", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def compile_record(module: Any, data: dict[str, Any]) -> dict[str, Any]:
    record = module.AtlasRecord.from_json(data)
    return module.BinaryContactCompiler(record).compile(
        horizon=3, functoriality_depth=3
    )


def mutate_and_compile(
    module: Any,
    source: dict[str, Any],
    mutate: Callable[[dict[str, Any]], None],
) -> dict[str, Any]:
    candidate = copy.deepcopy(source)
    mutate(candidate)
    return compile_record(module, candidate)


def main() -> None:
    checks: dict[str, Any] = {}

    manifest: dict[str, str] = {}
    for line in (BUNDLE / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        digest, name = line.split(maxsplit=1)
        manifest[name.lstrip("*")] = digest.lower()
    mismatches = {
        name: {"expected": expected, "actual": sha256(BUNDLE / name)}
        for name, expected in manifest.items()
        if sha256(BUNDLE / name) != expected
    }
    checks["manifest_entries"] = len(manifest)
    checks["manifest_mismatches"] = mismatches
    assert len(manifest) == 15
    assert not mismatches

    module = load_compiler()
    source = json.loads(
        (BUNDLE / "source_binary_contact_example.json").read_text(encoding="utf-8")
    )
    baseline = compile_record(module, source)
    checks["baseline_passed"] = baseline["passed"]
    checks["baseline_required_parent_subdivisions"] = sum(
        len(graph["required_parent_subdivisions"])
        for graph in baseline["source_boundary_graph"].values()
    )
    checks["baseline_required_child_subdivisions"] = sum(
        len(graph["required_child_subdivisions"])
        for graph in baseline["source_boundary_graph"].values()
    )
    assert baseline["passed"]
    assert checks["baseline_required_parent_subdivisions"] == 24
    assert checks["baseline_required_child_subdivisions"] == 8

    false_positive_results: dict[str, Any] = {}

    def remove_boundary_words(data: dict[str, Any]) -> None:
        data["boundary_words"] = {"parent": [], "children": {}}

    report = mutate_and_compile(module, source, remove_boundary_words)
    false_positive_results["missing_boundary_words"] = report["passed"]

    def corrupt_short_vertex(data: dict[str, Any]) -> None:
        data["vertex_by_word"]["L"] = "bogus_not_a_shift_image"

    report = mutate_and_compile(module, source, corrupt_short_vertex)
    false_positive_results["false_vertex_shift"] = report["passed"]

    def duplicate_lift(data: dict[str, Any]) -> None:
        data["branches"]["L"]["child_parent"]["L_duplicate"] = "r_LLL"

    report = mutate_and_compile(module, source, duplicate_lift)
    maximum_lifts = max(len(lifts) for lifts in report["one_to_many_atlas"].values())
    false_positive_results["multiple_same_branch_lifts"] = {
        "passed": report["passed"],
        "maximum_total_lifts": maximum_lifts,
    }

    def erase_flags(data: dict[str, Any]) -> None:
        data["root_flags"] = []
        data["branches"]["L"]["flag_image"] = {}
        data["branches"]["R"]["flag_image"] = {}

    report = mutate_and_compile(module, source, erase_flags)
    false_positive_results["empty_flag_atlas"] = report["passed"]

    def empty_refinement(data: dict[str, Any]) -> None:
        for branch in data["refinement"]["branches"].values():
            branch["refined_child_parent"] = {}

    report = mutate_and_compile(module, source, empty_refinement)
    false_positive_results["empty_refinement_relations"] = report["passed"]

    checks["confirmed_false_positives"] = false_positive_results
    assert false_positive_results["missing_boundary_words"]
    assert false_positive_results["false_vertex_shift"]
    assert false_positive_results["multiple_same_branch_lifts"]["passed"]
    assert maximum_lifts == 3
    assert false_positive_results["empty_flag_atlas"]
    assert false_positive_results["empty_refinement_relations"]

    parent = module.EquipotentialEdge(
        edge_id="parent",
        level=4,
        potential=module.frac("1/2"),
        theta_start=module.frac("0"),
        theta_end=module.frac("1/4"),
        start_flag="p0",
        end_flag="p1",
    )
    child = module.EquipotentialEdge(
        edge_id="child",
        level=4,
        potential=module.frac("1/4"),
        theta_start=module.frac("0"),
        theta_end=module.frac("1/4"),
        start_flag="c0",
        end_flag="c1",
    )
    erroneous_overlap = module.match_boundary_contacts([parent], [child])
    checks["same_level_distinct_potential_false_match"] = bool(erroneous_overlap)
    assert erroneous_overlap

    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    by_id = {item["id"]: item for item in ledger["obligations"]}
    checks["required_statuses"] = {
        key: by_id[key]["status"]
        for key in (
            "FIXED_BLOCK_BINARY_CONTACT_AUTOMATON",
            "FIXED_KKL_PAIR_STATE_MOMENT_FACTORIZATION",
            "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE",
            "DIRECT_DECORATION_TRACE_COLLAR_REALIZATION",
            "END_PLUMBING_TRACE_RESPONSE_CONTROL",
            "MBTT",
            "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
            "MLC",
        )
    }
    assert checks["required_statuses"]["FIXED_BLOCK_BINARY_CONTACT_AUTOMATON"] == "proved"
    assert (
        checks["required_statuses"]["FIXED_KKL_PAIR_STATE_MOMENT_FACTORIZATION"]
        == "proved"
    )
    for key in (
        "DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE",
        "DIRECT_DECORATION_TRACE_COLLAR_REALIZATION",
        "END_PLUMBING_TRACE_RESPONSE_CONTROL",
        "MBTT",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    ):
        assert checks["required_statuses"][key] == "open"

    assessment = ASSESSMENT.read_text(encoding="utf-8")
    for required in (
        "The submitted boundary compiler is not source-complete",
        "Pseudo-boundary topology is not Sobolev trace theory",
        "The omitted pulled-versus-immersed correspondence",
        "FIXED_BLOCK_BINARY_CONTACT_AUTOMATON",
        "FIXED_KKL_PAIR_STATE_MOMENT_FACTORIZATION",
        "VAAPC-I, H2, MBTT, H3, H4, UPTCR, and MLC remain open",
    ):
        assert required in assessment

    checks["passed"] = True
    print(json.dumps(checks, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
