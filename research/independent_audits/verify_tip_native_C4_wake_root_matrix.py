#!/usr/bin/env python3
"""Exact source-manifest regression for the native C4 wake / KL rooted matrix.

The real-symmetric external-ray Jordan wake calculation and the holomorphic
naturality/root-extension theorem are written analytic proofs, NOT certified
by this finite Python program. It checks their exact source-locked inputs
and consequence matrix; it does not manufacture physical connector words.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ATLAS = ROOT / "results/tip_kl_side_atlas.json"
PR60 = ROOT / "results/tip_rooted_native_KL_section_20261108.json"
PR63 = ROOT / "results/tip_native_root_deck_monodromy_20261109.json"
PHASE = ROOT / "results/tip_root_interval_geometry.json"
OUT = ROOT / "results/tip_native_C4_wake_root_matrix_20261109.json"


def enc_lo(phase):
    x = phase["left_endpoint_enclosure"]
    return F(x["lower_numerator"], 1 << x["denominator_power_of_two"])


def enc_hi(phase):
    x = phase["right_endpoint_enclosure"]
    return F(x["upper_numerator"], 1 << x["denominator_power_of_two"])


def source_data():
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    old = json.loads(PR60.read_text(encoding="utf-8"))["actual_source_G_KL_atlas"]
    prior = json.loads(PR63.read_text(encoding="utf-8"))
    phase = json.loads(PHASE.read_text(encoding="utf-8"))
    assert atlas["source_boundary_identity"] == "partial^v_i Psi(Y) = eta_i union xi_(i+1)"
    stage = next(s for s in atlas["stages"] if s["stage"] == "G")
    tiles = stage["pieces"]["W"]["tiles"]
    assert len(tiles) == 4 and stage["pieces"]["W"]["depth"] == 6
    assert stage["pieces"]["V0"]["depth"] == 3
    routes = stage["inclusions"]["W_into_V0"]["tile_routes"]
    assert sorted((r["source_tile"], r["target_tile"], r["angular_integer_shift"]) for r in routes) == [
        (f"G:W:tile{i}", f"G:V0:tile{i // 2}", 0) for i in range(4)
    ]
    phases = {p["physical_phase"]: p for p in phase["phase_intervals"]}
    assert phase["inner_root_exact_interval"] == "[x9,x18]"
    assert phase["phase_intervals_pairwise_disjoint"]
    assert enc_hi(phases[6]) < enc_lo(phases[0]) < 0 < enc_hi(phases[0]) < enc_lo(phases[3])
    assert phases[3]["coarse_phase"] == phases[6]["coarse_phase"] == 0
    rows = sorted(old["angle_rows"], key=lambda x: (x["W_tile"], x["slot"]))
    assert len(rows) == 8
    assert len(prior["anchor_rows"]) == 8
    assert {(x["tile"], x["slot"], x["ray"]) for x in prior["anchor_rows"]} == {
        (x["W_tile"], x["slot"], x["name"]) for x in rows
    }
    for x in rows:
        tile = tiles[x["W_tile"]]
        a, b = map(F, tile["seam_stage_angles"])
        assert a < F(x["Pi3"]) < b
        assert tile["id"] == x["source_tile_id"]
    return stage, tiles, rows, old


def compute():
    stage, tiles, rays, old = source_data()
    by_name = {x["name"]: x for x in rays}
    expected = [("d", "e", "zero_lower", "3/4"),
                ("pR", "pL", "right_tip", "0"),
                ("a", "b", "zero_upper", "1/4"),
                ("qL", "qR", "left_tip", "1/2")]
    edge_rows = []
    potentials = [0]
    for i, e in enumerate(sorted(old["adjacent_W_tile_fine_end_edges"],
                                 key=lambda x: x["from_W_tile"])):
        first, second, landing, fine = expected[i]
        assert e["from_W_tile"] == i and e["to_W_tile"] == (i + 1) % 4
        assert e["two_source_rays"] == [first, second]
        assert e["physical_target"] == landing and e["fine_angle"] == fine
        assert by_name[first]["physical_K9_target"] == by_name[second]["physical_K9_target"] == landing
        assert by_name[first]["Pi9"] == by_name[second]["Pi9"] == fine
        assert e["same_V0_parent"] == (i // 2 == ((i + 1) % 4) // 2)
        assert e["source_incidence_side_names"] == [
            f"G:W:tile{i}:eta", f"G:W:tile{(i + 1) % 4}:xi"
        ]
        a = F(by_name[first]["Pi3"])
        b = F(by_name[second]["Pi3"]) + (1 if i == 3 else 0)
        assert a < b
        # Source-defined real-symmetric G orientation; finite angular bracketing
        # ONLY, NOT a machine proof of the physical wake inclusion.
        if i == 0:
            assert 0 < a < b < F(1, 2)
        elif i == 1:
            assert a < F(1, 2) < b < 1
        elif i == 2:
            assert F(1, 2) < a < b < 1
        else:
            assert F(1, 2) < a < 1 < b < F(3, 2)
        w01, w02 = (1, 0) if i == 1 else (0, 1) if i == 3 else (0, 0)
        delta = w01 - w02
        edge_rows.append({
            "from_tile": i, "to_tile": (i + 1) % 4,
            "rays": [first, second],
            "start_G_angle": str(a), "end_G_angle_unwrapped": str(b),
            "landing": landing, "fine_prime_end": fine,
            "real_axis_marker": "1/2" if i == 1 else "1" if i == 3 else None,
            "extra_phase_winding_D01": w01, "extra_phase_winding_D02": w02,
            "transverse_delta": delta, "same_V0_parent": e["same_V0_parent"],
        })
        if i < 3:
            potentials.append(potentials[-1] + delta)
    assert len(edge_rows) == 4 and potentials == [0, 0, 1, 1]
    assert potentials[3] + edge_rows[3]["transverse_delta"] == potentials[0]
    assert [x["transverse_delta"] for x in edge_rows] == [0, 1, 0, -1]
    results = []
    sample_count = 0
    for r in rays:
        i, theta = r["W_tile"], F(r["Pi3"])
        for j, target in enumerate(tiles):
            lo, hi = map(F, target["seam_stage_angles"])
            side = "xi" if theta < lo else "eta" if theta > hi else "open_gluing_seam"
            assert (side == "open_gluing_seam") == (i == j)
            same = (i // 2 == j // 2)
            expected_delta = j // 2 - i // 2
            assert expected_delta == potentials[j] - potentials[i]
            if j != i and same:
                assert ((i % 2 == 0 and side == "xi") or
                        (i % 2 == 1 and side == "eta"))
            if j != i and not same:
                assert side in ("xi", "eta")
                assert abs(expected_delta) == 1
            for n in range(-20, 21):
                if n == 0:
                    continue
                new_x = theta + n
                assert new_x < lo or new_x > hi
                # Each coarse deck turn shifts both fine charges equally;
                # delta cannot be repaired by native integer winding.
                assert (potentials[j] + n) - (potentials[i] + n) == expected_delta
                # For same-parent n != 0, w_D01 changes by n and disallows H.
                assert n != 0
                sample_count += 1
            results.append({
                "ray": r["name"], "anchor_tile": i, "other_tile": j,
                "G_angle": str(theta), "Pi9": r["Pi9"],
                "physical_K9_target": r["physical_K9_target"],
                "anchor_V0_parent": i // 2, "other_V0_parent": j // 2,
                "root_sheet_transverse_delta": expected_delta,
                "source_side_at_zero_deck": side,
                "zero_deck_root_compatible": same,
                "root_deck_shift": 0 if same else None,
                "proof_class": ("source_gluing_root" if i == j else
                                "source_naturality_rooted_finite_Jside" if same else
                                "wake_charge_nonroot_all_deck_shifts"),
            })
    assert len(results) == 32 and sample_count == 1280
    counts = {
        "original_root_ray_anchors": len(rays), "original_W_tiles": len(tiles),
        "cohort_ray_tile_pairs": len(results),
        "rooted_source_open_seam_points": sum(x["proof_class"] == "source_gluing_root" for x in results),
        "rooted_same_parent_original_Jside_points": sum(x["proof_class"] == "source_naturality_rooted_finite_Jside" for x in results),
        "opposite_parent_original_Jside_cohorts_no_root_shift": sum(x["proof_class"] == "wake_charge_nonroot_all_deck_shifts" for x in results),
        "sampled_nonzero_deck_shifts_per_cohort": 40, "sampled_nonzero_lifts": sample_count,
    }
    assert [counts[x] for x in ("rooted_source_open_seam_points",
                                "rooted_same_parent_original_Jside_points",
                                "opposite_parent_original_Jside_cohorts_no_root_shift")] == [8, 8, 16]
    return {
        "schema_version": 1,
        "scope": "Source G=f^3 original W=Y_G^6 native universal tiles, eight physically certified fine-root rays and all integer deck shifts in each of four source tiles; NOT whole KL groupoid or general KKL restriction",
        "edge_winding_scope": "Real-symmetric G external-angle wake / source-local connector; phase winding conclusion is written planar proof and not Lean-formalized",
        "original_source_inclusion": "W_into_V0 with tile routes [0,1]->0 and [2,3]->1, all integer shifts zero",
        "original_angular_wake_edges": edge_rows,
        "source_tile_transverse_potential": potentials,
        "root_ray_tile_cases": results,
        "counts": counts,
        "analytic_inputs_not_formalized": [
            "Real-symmetric order-reversing physical G straightening, noncrossing external rays, and the positive/negative real ray identification",
            "Actual G ray landings and the Jordan wake separation of positive D_(0,1) and negative D_(0,2)",
            "KL source Lemma 3.4 naturality and actual W->V0 universal-tile zero-shift inclusions",
            "Kahn root-neighborhood biholomorphism, source same-root immersion and marked-sheet convergence",
            "Caratheodory local connectivity for full continuous ideal subarc extension",
        ],
        "unresolved": [
            "Literal nine-generator connector words for cross-parent paths (the transverse obstruction is decisive for this cohort without them)",
            "All other KL proof-used rays, arbitrary ideal J-side intervals, full proper-end groupoid/KKL unique restriction",
            "H1-H4 UPTCR MLC and ledger remain unchanged",
        ],
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    x = p.add_mutually_exclusive_group()
    x.add_argument("--check-manifest", action="store_true")
    x.add_argument("--write-manifest", action="store_true")
    opts = p.parse_args()
    result = compute()
    if opts.write_manifest:
        OUT.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8")
        print("WROTE", OUT)
    elif opts.check_manifest:
        assert json.loads(OUT.read_text(encoding="utf-8")) == result, "manifest drift"
        print("PASS: native source 4 wake edges, 8 positive J-side root witnesses, "
              "16 opposite-parent nonroot cohorts, 32 full tile classes, 1280 deck samples")
    else:
        print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
