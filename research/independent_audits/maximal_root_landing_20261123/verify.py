#!/usr/bin/env python3
"""Exact source bookkeeping; the topological theorem is written in NOTE.md."""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def read_json(relative: str):
    return json.loads((ROOT / relative).read_text())


def reduce_word(word):
    out = []
    for letter in word:
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return out


def inverse(word):
    return [-letter for letter in reversed(word)]


def packet():
    previous_path = "research/independent_audits/issue62_connector_words_20261116/word_status.json"
    previous = read_json(previous_path)
    source = read_json("results/tip_rooted_native_KL_section_20261108.json")
    wake = read_json("results/tip_native_C4_wake_root_matrix_20261109.json")
    angles = {
        row["name"]: row
        for row in source["actual_source_G_KL_atlas"]["angle_rows"]
    }
    pR, pL = angles["pR"], angles["pL"]
    assert Fraction(pR["Pi3"]) == Fraction(2, 7)
    assert Fraction(pL["Pi3"]) == Fraction(5, 7)
    assert pR["physical_K9_target"] == pL["physical_K9_target"] == "right_tip"
    assert pR["Pi9"] == pL["Pi9"] == "0"
    assert (pR["W_tile"], pL["W_tile"]) == (1, 2)
    assert Fraction(53, 192) < Fraction(2, 7) < Fraction(55, 192)
    assert Fraction(137, 192) < Fraction(5, 7) < Fraction(139, 192)
    assert Fraction(5, 7) < Fraction(149, 192)  # the native tile-3 xi witness
    edge = next(row for row in wake["original_angular_wake_edges"] if row["rays"] == ["pR", "pL"])
    assert (edge["extra_phase_winding_D01"], edge["extra_phase_winding_D02"]) == (1, 0)
    assert edge["transverse_delta"] == 1
    assert Fraction(edge["start_G_angle"]) < Fraction(1, 2) < Fraction(edge["end_G_angle_unwrapped"])

    # Keep complete path order: c r^-1 = (c C^-1)(C rt^-1)(rt r^-1).
    # c, C, rt and r are independent oriented edges, not commuting scalars.
    c, C, rt, r = [1], [2], [3], [4]
    assert reduce_word(c + inverse(C) + C + inverse(rt) + rt + inverse(r)) == c + inverse(r)
    assert reduce_word(C + inverse(rt)) != reduce_word(inverse(rt) + C)

    rows = []
    counts = Counter()
    for old in previous["rows"]:
        j = old["source_W_tile"]
        parent = j // 2
        assert parent == old["source_V_parent"]
        assert old["based_F9_defect_word"] is None
        assert old["coarse_polygon_or_ray_equipotential"] is None
        rooted = old["prior_fine_sheet_footprint"] == "marked_root"
        assert (old["conditional_required_F9_root_subgroup_membership"] == "in_H") == rooted
        counts[parent, rooted] += 1
        rows.append({
            "anchor_ray": old["anchor_ray"],
            "source_W_tile": j,
            "original_ideal_side": old["original_ideal_side"],
            "native_integer_shift": old["native_integer_shift"],
            "unwrapped_G_angle": old["unwrapped_G_angle"],
            "source_V_parent": parent,
            "native_fine_footprint": old["prior_fine_sheet_footprint"],
            "single_rooted_parent0_coarse_source_faithful_path_exists": parent == 0,
            "single_rooted_parent1_coarse_source_faithful_path_exists": parent == 1,
            "fine_W_prefix_source_faithful_path_exists": True,
            "old_literal_F9_word_still_uncomputed": True,
            "analytic_status": "conditional_on_written_native_geometry_and_NOTE_theorems",
        })
    assert len(rows) == 88
    assert counts == Counter({(0, True): 4, (0, False): 40, (1, True): 4, (1, False): 40})
    for base_parent in (0, 1):
        key = f"single_rooted_parent{base_parent}_coarse_source_faithful_path_exists"
        assert sum(row[key] for row in rows) == 44
        assert sum(not row[key] and row["native_fine_footprint"] == "marked_root" for row in rows) == 4

    wrong_root_rows = [row for row in rows if not row["single_rooted_parent0_coarse_source_faithful_path_exists"] and row["native_fine_footprint"] == "marked_root"]
    assert {(row["anchor_ray"], row["source_W_tile"], row["original_ideal_side"]) for row in wrong_root_rows} == {
        ("pL", 3, "xi"), ("a", 3, "xi"), ("b", 2, "eta"), ("qL", 2, "eta")
    }
    return {
        "schema_version": 1,
        "status": "written_conditional_native_component_obstruction_not_MLC",
        "source_manifest": previous_path,
        "source_manifest_sha256": hashlib.sha256((ROOT / previous_path).read_bytes()).hexdigest(),
        "basepoint": "short positive-height pR G-ray tail, parent 0; rooted fine sheet",
        "component_partition": [[0, 1], [2, 3]],
        "minimal_number_of_initial_coarse_components": 2,
        "explicit_native_ideal_witness": {
            "ray": "pL", "source_W_tile": 3, "side": "xi", "unwrapped_G_angle": "5/7",
            "native_fine_image": "rooted", "coarse_only_defect_Delta_for_every_common_base_path": 1,
        },
        "counts": {
            "source_rows": 88, "coarse_source_faithful_from_parent0": 44,
            "coarse_source_faithful_from_parent1": 44,
            "parent0_coarse_forbidden_native_root_rows": 4,
            "parent0_coarse_forbidden_native_nonroot_rows": 40,
            "literal_archived_F9_words_computed": 0,
        },
        "rows": rows,
        "not_machine_proved": [
            "physical rays and their common landing", "Jordan wake separation",
            "same-root holomorphic immersion", "native KL path subordination and geometry",
            "covering-space existence and component theorem", "MLC",
        ],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = packet()
    destination = HERE / "coarse_component_feasibility.json"
    expected = json.dumps(result, indent=2) + "\n"
    if args.check:
        assert destination.read_text() == expected, "Regenerate manifest before checking."
    else:
        destination.write_text(expected)
    print(json.dumps(result["counts"], sort_keys=True))
    print("PASS: native source rows and exact path-order controls; analytic proof remains written.")


if __name__ == "__main__":
    main()
