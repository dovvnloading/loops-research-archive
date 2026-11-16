#!/usr/bin/env python3
"""Additive primitive v1.1: finite one-slit side atlas, never a fake KKL Wave.

The legacy generator, input and immutable refusal remain untouched. The
source's prime/ψ-ql ambient edge and whole-Wave hypotheses are not inferred
from a central return's one invariant interval. Python standard library only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import regenerate_near_parabolic as old
from regenerate import Box, HERE, REPO, SCALE, canonical, ensure, load, sha256

CONTRACT = HERE / "source_contracts/primitive_v1_1_field_sources.json"
SPEC = HERE / "SPECIFICATION_v1_1.md"
MANIFEST = HERE / "experiment_manifests/near_parabolic_primitive_v1_1.json"
CODE_PATH = "research/native_wave_transfer/regenerate_primitive_v1_1.py"
MODE = "v1.1-one-inner-return-slit"
TARGET = ("I_upper", "I_lower")
SOURCE = (
    "S_upper_negative", "S_upper_positive",
    "S_lower_positive", "S_lower_negative",
)
# Cyclic source order: upper(-a,0), upper(0,a), lower(a,0), lower(0,-a).
COVER = (1, 0, 1, 0)     # G reverses side on its negative monotone half.
IMMERSION = (0, 0, 1, 1) # physical inclusion preserves real-side access.


def legacy_embed(record: dict) -> dict:
    """A disjoint tagged union: no rewriting of an existing v1 record."""
    return {"mode": "v1-three-inner-phase", "v1_record": record}


def legacy_project(tagged: dict) -> dict:
    ensure(set(tagged) == {"mode", "v1_record"}
           and tagged["mode"] == "v1-three-inner-phase",
           "not an unchanged v1 record")
    return tagged["v1_record"]


def source_local_geometry(member: dict) -> None:
    """Recheck central branch sign and isolated tips on the *whole* interval.

    The old exact Rouché and phase-disk certificates were already recomputed
    by old.make_manifest before reaching this function.
    """
    p = member["physical_return"]
    pb = member["parameter_bracket"]
    denominator = 1 << pb["denominator_power_of_two"]
    lo = old.Q(int(pb["lower_numerator"]), denominator)
    hi = old.Q(int(pb["upper_numerator"]), denominator)
    c = Box(Box.rational(lo).low, Box.rational(hi).high)
    orbit = old.bracket(c, 2 * p)
    a = -orbit[p]
    radius = Box.rational(old.Q(member["target_radius"]))
    ensure(a.low > 0 and a.high < radius.low
           and orbit[2 * p].low > 0
           and (orbit[2 * p] + orbit[p]).low <= 0
           <= (orbit[2 * p] + orbit[p]).high,
           "not a contained, certified one-slit Chebyshev return")
    # A real negative derivative would reverse the claimed source-side map.
    # There are no other turning points because every f^j(V), 1<=j<p,
    # excludes the critical point (certified by old.complex_phase_bounds).
    terminal = old.multiplier_at(a, c, p)
    ensure(terminal.low > 3 * SCALE,
           "positive-branch orientation/terminal multiplier drift")
    ensure(member["complex_phases_pairwise_disjoint"]
           and member["all_noncentral_phase_disks_avoid_critical_point"]
           and member["real_inner_geometry"]["G_inverse_of_K_in_central_V_equals_K"]
           and member["real_inner_geometry"]["new_inverse_tree_attachments"] == 0,
           "unproved local inverse tree or primitive phase geometry")


def member_record(member: dict) -> dict:
    source_local_geometry(member)
    p = member["physical_return"]
    pb = member["parameter_bracket"]
    geometry = member["real_inner_geometry"]
    ensure(geometry["number_of_inner_G_phase_intervals"] == 1,
           "v1.1 requires exactly one invariant G-return interval")
    result = {
        "p": p,
        "ambient_phase_count": p,   # pairwise disjoint f^j(K0), NOT G-cycled.
        "inner_return_interval_count": 1,
        "parameter_bracket": {
            "lower_numerator": pb["lower_numerator"],
            "upper_numerator": pb["upper_numerator"],
            "denominator_power_of_two": pb["denominator_power_of_two"],
        },
        "complex_certificates": {
            "restricted_degree": member["restricted_degree"],
            "global_degree": member["global_degree"],
            "target_radius": member["target_radius"],
            "rouche_margin_strict_enclosure":
                member["central_rouche_margin_strictly_between"],
            "phase_gap_strict_enclosure":
                member["primitive_phase_disk_gap_strictly_between"],
        },
        "local_tree": {
            "hull": "K0=[-a,a]",
            "preimage_hull_in_V": "K0=[-a,a]",
            "new_attachment_components": [],
            "new_attachment_count": 0,
            "complete_for_central_return": True,
            "ambient_KKL_attachment_census": None,
        },
        "ideal_boundary": {
            "marking": "chosen-real-slit-upper-lower/v1.1",
            "target_side_atoms": list(TARGET),
            "target_inner_atom_count": 2,
            "covering_source_side_atoms": list(SOURCE),
            "covering_source_inner_atom_count": 4,
            "outer_component_atom_count": 1,
            "tip_accesses_per_slit": 2,
            "count_invariant_under_refinement": False,
        },
        "operations": {
            "covering_f_star": {
                "map": "G=f_c^p:V\\K0 -> U\\K0",
                "source_to_target": list(COVER),
                "degree": 2,
                "preimages_per_target_side": [2, 2],
            },
            "immersion_iota_star": {
                "map": "iota:V\\K0 -> U\\K0 (inclusion)",
                "source_to_target_pullback": list(IMMERSION),
                "target_to_source_blocks": [[0, 1], [2, 3]],
                "attached_component_boundary_blocks": [],
            },
        },
        "restrictions": {
            "local_covering_side_germs": 2,
            "local_inclusion_side_germs": 1,
            "specified_whole_target_path": None,
            "filtered_restriction_counts": None,
        },
        "local_edges": {
            "local_complementary_edge_count": 0,
            "local_complementary_incidence_matrix": [],
            "local_perron_root": None,
            "zero_local_edge_side_atoms": list(TARGET),
            "ambient_KKL_old_edge_matrix": None,
            "ambient_KKL_perron_root": None,
            "KKL_closed_wave_crests": None,
        },
        "wave": {
            "parent_width": None,
            "child_widths": None,
            "harmonic_equality": None,
            "width_degeneracy_status": None,
        },
        "collar": {
            "round_quadratic_like_modulus_lower_bound": "log(8/7)/(2*pi)",
            "canonical_attachment_h": None,
            "canonical_attachment_ell": None,
        },
        "resistance": {
            "h_times_log_inverse_ell": None,
            "contact_resistance_test": None,
            "rouche_margin_order_is_wave_width_order": None,
        },
    }
    validate_member(result)
    return result


def validate_member(item: dict) -> None:
    """Fail closed on conflated actions, invented spectrum, widths or collar."""
    bd, ops, tree = item["ideal_boundary"], item["operations"], item["local_tree"]
    cov, imm = ops["covering_f_star"], ops["immersion_iota_star"]
    ensure(item["ambient_phase_count"] == item["p"]
           and item["inner_return_interval_count"] == 1,
           "ambient and inner arities confused")
    ensure(tree["hull"] == tree["preimage_hull_in_V"] == "K0=[-a,a]"
           and tree["new_attachment_components"] == []
           and tree["new_attachment_count"] == 0
           and tree["complete_for_central_return"] is True
           and tree["ambient_KKL_attachment_census"] is None,
           "local attachment mistaken for ambient KKL attachment")
    ensure(bd["marking"] == "chosen-real-slit-upper-lower/v1.1"
           and bd["target_side_atoms"] == list(TARGET)
           and bd["covering_source_side_atoms"] == list(SOURCE)
           and bd["target_inner_atom_count"] == 2
           and bd["covering_source_inner_atom_count"] == 4
           and bd["outer_component_atom_count"] == 1
           and bd["tip_accesses_per_slit"] == 2
           and bd["count_invariant_under_refinement"] is False,
           "real-slit marking or chosen-atom counts drifted")
    ensure(cov["map"] == "G=f_c^p:V\\K0 -> U\\K0"
           and cov["source_to_target"] == list(COVER)
           and cov["degree"] == 2
           and cov["preimages_per_target_side"] ==
                [list(COVER).count(0), list(COVER).count(1)] == [2, 2],
           "covering f_* not the two-sheet side lift")
    ensure(imm["map"] == "iota:V\\K0 -> U\\K0 (inclusion)"
           and imm["source_to_target_pullback"] == list(IMMERSION)
           and imm["target_to_source_blocks"] == [[0, 1], [2, 3]]
           and imm["attached_component_boundary_blocks"] == []
           and cov["source_to_target"] != imm["source_to_target_pullback"],
           "immersion iota^* conflated with covering f_*")
    restrict = item["restrictions"]
    ensure(restrict == {
        "local_covering_side_germs": 2,
        "local_inclusion_side_germs": 1,
        "specified_whole_target_path": None,
        "filtered_restriction_counts": None,
    }, "local lift germs are not filtered whole-path multiplicities")
    edges = item["local_edges"]
    ensure(edges["local_complementary_edge_count"] == 0
           and edges["local_complementary_incidence_matrix"] == []
           and edges["local_perron_root"] is None
           and edges["zero_local_edge_side_atoms"] == list(TARGET)
           and edges["ambient_KKL_old_edge_matrix"] is None
           and edges["ambient_KKL_perron_root"] is None
           and edges["KKL_closed_wave_crests"] is None,
           "empty local tree is not a certified KKL Perron/Wave matrix")
    ensure(all(value is None for value in item["wave"].values()),
           "unsupported parent/child Wave widths or harmonic assertion")
    ensure(item["collar"] == {
        "round_quadratic_like_modulus_lower_bound": "log(8/7)/(2*pi)",
        "canonical_attachment_h": None, "canonical_attachment_ell": None,
    }, "round subcollar is not measured attachment h or ell")
    ensure(all(value is None for value in item["resistance"].values()),
           "contact resistance cannot be inferred without h, ell and Waves")


def leaf_fields(value, path: str = "") -> dict[str, object]:
    """Each scalar and each homogeneous array is one leaf; members[] is indexed."""
    if isinstance(value, dict):
        out = {}
        for name, child in value.items():
            out.update(leaf_fields(child, (path + "." if path else "") + name))
        return out
    if path == "members":
        ensure(isinstance(value, list) and len(value) == 3,
               "must have three physical records")
        merged = {}
        for member in value:
            one = leaf_fields(member, "members[]")
            ensure(not (set(merged) - set(one) or set(one) - set(merged)),
                   "inconsistent per-member leaf schema") if merged else None
            merged.update(one)
        return merged
    ensure(not isinstance(value, float), "untrusted binary-float certification")
    return {path: value}


def valid_type(value, t: str) -> bool:
    if t == "null":
        return value is None
    if t == "integer":
        return type(value) is int
    if t == "boolean":
        return type(value) is bool
    if t == "string":
        return type(value) is str
    if t == "string-list":
        return type(value) is list and all(type(x) is str for x in value)
    if t == "integer-list":
        return type(value) is list and all(type(x) is int for x in value)
    if t == "integer-list-list":
        return type(value) is list and all(
            type(x) is list and all(type(y) is int for y in x)
            for x in value)
    return False


def check_contract(outputs: dict, contract: dict) -> None:
    ensure(contract.get("format") == "native-wave-primitive-v1.1-field-sources"
           and contract.get("schema_version") == "1.1",
           "v1.1 field registry header drift")
    sources, fields = contract.get("sources"), contract.get("fields")
    ensure(isinstance(sources, dict) and isinstance(fields, dict)
           and sources and fields,
           "missing source-to-field coverage")
    actual = leaf_fields(outputs)
    ensure(set(actual) == set(fields),
           "unknown/uncited v1.1 output field or missing cited field: "
           + str(sorted(set(actual) ^ set(fields))))
    valid_status = {"exact-finite", "conditional-slit",
                    "not-defined", "declared-choice"}
    for path, value in actual.items():
        info = fields[path]
        ensure(isinstance(info, dict) and set(info) ==
               {"type", "source", "status"}
               and isinstance(info["source"], str)
               and info["source"] in sources
               and isinstance(sources[info["source"]], str)
               and len(sources[info["source"]]) > 15
               and info["status"] in valid_status
               and valid_type(value, info["type"]),
               "invalid type, citation or status: " + path)
        ensure((value is None) == (info["type"] == "null"),
               "null must have a refusal annotation: " + path)
        if value is None:
            ensure(info["status"] == "not-defined",
                   "null lacks explicit unresolved status: " + path)
    # Non-null statuses cannot mark missing quantities as exact witnesses.
    ensure(set(contract) == {"format", "schema_version", "sources", "fields"},
           "unreviewed v1.1 field registry additions")


def make_outputs(fixture: dict) -> dict:
    # Full existing exact engine and Git-blob source locks; compare old bytes,
    # never rewrite or relax the original three-phase semantic refusal.
    old_manifest = old.make_manifest(fixture)
    ensure(old.MANIFEST.read_bytes() == canonical(old_manifest),
           "preexisting near-parabolic refusal manifest byte drift")
    base = old_manifest["outputs"]
    members = [member_record(row) for row in base["finite_selected_members"]]
    ensure([m["p"] for m in members] == [24, 27, 30]
           and base["finite_parameter_order"] == "-7/4 < c30 < c27 < c24",
           "incorrect primitive branch selection/order")
    for label, name in (("p3", "tip_pr68"), ("p4", "primitive4_tip12")):
        v1 = load(HERE / ("experiment_manifests/" + name + ".json"))
        ensure(canonical(legacy_project(legacy_embed(v1))) == canonical(v1)
               and base["prior_primitive_comparison"][label]["target_atoms"] == 10
               and base["prior_primitive_comparison"][label]["source_atoms"] == 20,
               "v1 legacy embedding must be byte-identity")
    return {
        "mode": MODE,
        "finite_parameter_order": base["finite_parameter_order"],
        "legacy_v1_inclusion": "identity-only; no v1 reserialization",
        "members": members,
    }


def make_manifest(fixture: dict, contract: dict | None = None) -> dict:
    if contract is None:
        contract = load(CONTRACT)
    outputs = make_outputs(fixture)
    check_contract(outputs, contract)
    return {
        "format": "native-wave-primitive-one-slit-manifest/v1.1",
        "schema_version": "1.1",
        "experiment_id": "native-near-parabolic-primitive-Chebyshev-tips-v1.1",
        "code": {"path": CODE_PATH, "sha256": sha256(Path(__file__))},
        "inputs": {
            "existing_near_parabolic_fixture_sha256": sha256(old.INPUT),
            "existing_refusal_manifest_sha256": sha256(old.MANIFEST),
            "v1_1_spec_sha256": sha256(SPEC),
            "v1_1_field_contract_sha256": sha256(CONTRACT),
            "locked_legacy_git_blobs": old.SOURCE_LOCKS,
        },
        "outputs": outputs,
        "outputs_sha256": hashlib.sha256(canonical(outputs)).hexdigest(),
        "proof_status": {
            "certified_exact": [
                "unchanged finite dyadic root, Rouché, phase-gap and return-inverse certificates",
                "local return-slit T_G'=T_G, zero local attachments/edges",
                "branch orientation and return degree two",
                "explicit annular quadratic-like modulus lower bound",
            ],
            "conditional_analytic_and_chosen": [
                "whole little Julia set equals real Chebyshev interval, including slit prime ends",
                "2/4 side-access atoms are for one declared refinement, not canonical",
            ],
            "numerical_only": [],
            "open_or_undefined": [
                "full ambient KKL prime ψ-ql tree, attachments and core Perron matrix",
                "globally filtered proper paths, KKL Wave crests and harmonic widths",
                "canonical attachment h and ell, crossover scale and wave-width trend",
                "infinite parabolic accumulation theorem",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--print-manifest", action="store_true")
    args = parser.parse_args()
    ensure(sum((args.check, args.write, args.print_manifest)) <= 1,
           "select only one manifest action")
    payload = canonical(make_manifest(load(old.INPUT)))
    if args.print_manifest:
        print("NATIVE_V1_1_MANIFEST_BEGIN")
        print(payload.decode("ascii"), end="")
        print("NATIVE_V1_1_MANIFEST_END")
    elif args.write:
        MANIFEST.write_bytes(payload)
        print("WROTE:", MANIFEST)
    else:
        ensure(MANIFEST.read_bytes() == payload,
               "near-parabolic v1.1 immutable manifest drift")
        print("PASS: 3 primitive local return-slit side atlases; KKL Waves unasserted")


if __name__ == "__main__":
    main()
