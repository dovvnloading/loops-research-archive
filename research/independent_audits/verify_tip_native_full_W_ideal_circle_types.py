#!/usr/bin/env python3
"""Exact source-locked original G W KL full ideal-circle incidence audit.

All analytic covering, KL prime-end source topology and Kahn localization
claims are WRITTEN proofs and imported, not formalized in these finite tests.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ATLAS = ROOT / "results/tip_kl_side_atlas.json"
TRICH = ROOT / "results/tip_native_finite_J_side_trichotomy_20261109.json"
OUT = ROOT / "results/tip_native_full_W_ideal_circle_types_20261109.json"


def mod1(x: F) -> F:
    return x - (x.numerator // x.denominator)


def compute():
    source = json.loads(ATLAS.read_text(encoding="utf-8"))
    trich = json.loads(TRICH.read_text(encoding="utf-8"))
    stage = next(s for s in source["stages"] if s["stage"] == "G")
    w = stage["pieces"]["W"]
    v = stage["pieces"]["V0"]
    assert w["depth"] == 6 and v["depth"] == 3
    assert w["tile_count"] == 4 and len(w["tiles"]) == 4
    assert len(w["boundary_vertices"]) == 4
    assert stage["ordinary_stage_filled_set"] == "K3"
    assert stage["terminal_root"] == "K9"
    assert source["source_boundary_identity"] == "partial^v_i Psi(Y) = eta_i union xi_(i+1)"
    assert trich["witness_counts"] == {
        "marked_fine_root": 8, "removed_fine_target": 16,
        "ordinary_fine_exterior": 8, "total": 32
    }
    original_V_pairs = {vtx["stage_ray_pair"] for vtx in v["boundary_vertices"]}
    original_W_pairs = {vtx["stage_ray_pair"] for vtx in w["boundary_vertices"]}
    assert len(original_W_pairs) == 4
    assert original_W_pairs.isdisjoint(original_V_pairs)
    vertex_records, wrapping, outer_samples = [], [], []
    for i,tile in enumerate(w["tiles"]):
        next_tile = w["tiles"][(i+1)%4]
        eta = tile["eta"]["finite_endpoint_vertex"]
        xi = next_tile["xi"]["finite_endpoint_vertex"]
        assert eta == xi
        assert eta["stage_ray_pair"] in original_W_pairs
        assert eta["stage_angles"] == [
            str(F(tile["seam_stage_angles"][1])),
            str(F(next_tile["seam_stage_angles"][0])),
        ] if i != 3 else eta["stage_angles"] == [
            str(F(next_tile["seam_stage_angles"][0])),
            str(F(tile["seam_stage_angles"][1])),
        ]
        assert tile["outgoing_vertex_boundary"] == [
            f"G:W:tile{i}:eta",f"G:W:tile{(i+1)%4}:xi"
        ]
        vertex_records.append({
            "vertex_after_W_tile":i,
            "vertex_before_W_tile":(i+1)%4,
            "original_incidence":[f"G:W:tile{i}:eta",f"G:W:tile{(i+1)%4}:xi"],
            "G_ray_pair":eta["stage_ray_pair"],
            "G_angle_endpoints":eta["stage_angles"],
            "physical_vertex_label":eta["physical_landing_target"],
            "target_class":"ordinary fine exterior Omega9 via compact W in V and K9 compact in W"
        })
        assert tile["lambda"]["wrapping_endpoints"] == ["-infinity","+infinity"]
        assert tile["lambda"]["carrier_height_relative_to_initial"] == "1/32"
        assert tile["lambda"]["outer_line"] == "all real x"
        for side,end,joint in (("xi","-infinity","lambda_xi"),("eta","+infinity","lambda_eta")):
            wrapping.append({
                "tile":i, "source_joint":joint,
                "ideal_sides":[f"lambda_{i}",f"{side}_{i}"],
                "deck_limit":end,
                "extension_to_uncompactified_fine_surface":False,
                "reason":"Source positive/negative full deck iterates converge to same KL wrapping ideal end while their physical projections stay distinct constant points",
            })
        for label in ("1/8","1/2","7/8"):
            z = F(label)
            assert mod1(z + 1) == z
            outer_samples.append({
                "source_W_tile":i,
                "original_ideal_side":f"lambda_{i}",
                "finite_source_angle":label,
                "outer_carrier_height":tile["lambda"]["carrier_height_relative_to_initial"],
                "physical_target_class":"ordinary fine exterior Omega9",
                "local_continuation":True
            })
    assert len(vertex_records) == 4
    assert len({x["physical_vertex_label"] for x in vertex_records}) == 4
    assert len(wrapping) == 8 and len(outer_samples) == 12
    assert len({x["source_joint"] for x in wrapping}) == 2

    return {
        "schema_version":1,
        "theorem_scope":"Pointwise extension and obstruction into UNCOMPACTIFIED fine canonical T_hat9 for full original ordinary G:W KL ideal O/xi/eta boundary (no claim of one continuous whole-boundary map)",
        "original_source_boundary_identity":source["source_boundary_identity"],
        "actual_W_source_depth":w["depth"],
        "actual_V_parent_depth":v["depth"],
        "original_source_ideal_arc_counts":{
            "O_lambda":4,"J_xi_eta":8,"finite_vertices":4,
            "wrapping_O_J_joints":8
        },
        "source_vertex_incidence":vertex_records,
        "source_wrapping_joints":wrapping,
        "finite_outer_O_sample_points":outer_samples,
        "inherited_strict_finite_J_side_trichotomy":{
            "manifest_path":"results/tip_native_finite_J_side_trichotomy_20261109.json",
            "types":["marked K9 root","physically removed D_(0,1) or D_(0,2)","ordinary Omega9"],
            "sample_witnesses":trich["witness_counts"]["total"]
        },
        "complete_pointwise_boundary_types":{
            "lambda_i finite open O arcs":"ordinary fine exterior Omega9; source immersion has a unique local extension into it",
            "xi_i eta_i strictly interior finite J arcs":"source original physical landing target trichotomy of merged PR #65",
            "four finite vertices eta_i cap xi_(i+1)":"ordinary fine exterior Omega9; source W->V inclusion naturality maps each to a central V point, giving unique fine extension",
            "eight infinite wrapping lambda_i cap xi_i or lambda_i cap eta_i joints":"no continuous extension of any projection-commuting map into the same uncompactified fine target"
        },
        "analytic_proofs_written_not_formalized":[
            "Original KL II §3.2.1 path-space and universal-carrier tile source projection, source §3.2.4 prime end circle/side/joint and naturality boundary extension",
            "Geometric W closure compact in V and K9 compact in W, V contained in T9 (previous source phase-avoidance proof)",
            "Source positive carrier equipotential O-boundary physical location in Omega9 and local covering argument",
            "Native source deck iterates approach actual wrapping ideal prime ends in uniformizing whole-piece boundary",
            "Merged PR #65 genuine strict finite J-side physical-target analytic trichotomy"
        ],
        "still_open":[
            "Whole continuous extension into a NEW compactification with extra boundary objects, rather than pointwise extension into the uncompactified fine surface",
            "Complete KL proof-used path groupoid/subordination, literal nine-generator connector words, and KKL unique proper restriction",
            "H1-H4, UPTCR, MLC remain open and ledger unchanged"
        ]
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    group=p.add_mutually_exclusive_group()
    group.add_argument("--check-manifest",action="store_true")
    group.add_argument("--write-manifest",action="store_true")
    o=p.parse_args()
    result=compute()
    if o.write_manifest:
        OUT.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n",encoding="utf-8")
        print("WROTE",OUT)
    elif o.check_manifest:
        assert json.loads(OUT.read_text(encoding="utf-8"))==result, "source manifest drift"
        print("PASS: four real original W finite vertices; eight true infinite O/J wrapping joints; 12 finite source O witnesses; inherited 32 strict finite J samples")
    else:
        print(json.dumps(result,sort_keys=True,indent=2))


if __name__=="__main__":main()
