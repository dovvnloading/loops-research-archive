#!/usr/bin/env python3
"""Source-backed finite test of genuine KL strict J-side target trichotomy.

Analytic universal quantifier belongs to the written source-dependent proof,
not to bounded enumeration. This regression reads BOTH independent source
families (PR #61 omitted/exterior and merged PR #64 rooted J-side).
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ATLAS = ROOT / "results/tip_kl_side_atlas.json"
PHASE = ROOT / "results/tip_root_interval_geometry.json"
PREVIOUS_X = ROOT / "results/tip_native_ideal_side_exclusions_20261108.json"
PREVIOUS_R = ROOT / "results/tip_native_C4_wake_root_matrix_20261109.json"
OUT = ROOT / "results/tip_native_finite_J_side_trichotomy_20261109.json"


def modulo_one(x: F) -> F:
    return x - (x.numerator // x.denominator)


def side_of(x: F, lo: F, hi: F) -> str:
    if x < lo:
        return "xi"
    if x > hi:
        return "eta"
    return "glued_seam_or_vertex"


def compute():
    source = json.loads(ATLAS.read_text(encoding="utf-8"))
    stage = next(s for s in source["stages"] if s["stage"] == "G")
    tiles = stage["pieces"]["W"]["tiles"]
    assert len(tiles) == 4 and stage["pieces"]["W"]["depth"] == 6
    assert source["source_boundary_identity"] == "partial^v_i Psi(Y) = eta_i union xi_(i+1)"
    intervals = [tuple(map(F, t["seam_stage_angles"])) for t in tiles]
    assert intervals == [
        (F(41,192),F(43,192)), (F(53,192),F(55,192)),
        (F(137,192),F(139,192)), (F(149,192),F(151,192)),
    ]
    phase = json.loads(PHASE.read_text(encoding="utf-8"))
    assert phase["phase_intervals_pairwise_disjoint"]
    assert phase["inner_root_exact_interval"] == "[x9,x18]"
    by_p = {x["physical_phase"]: x for x in phase["phase_intervals"]}
    assert len(by_p) == 9 and [p for p,x in by_p.items() if x["coarse_phase"] == 0] == [0,3,6]
    assert by_p[0]["exact_interval"] == "[x9,x18]"
    assert by_p[3]["exact_interval"] == "[x12,x3]"
    assert by_p[6]["exact_interval"] == "[x6,x15]"
    assert all(x["coarse_phase"] in (1,2) for i,x in by_p.items() if i not in (0,3,6))

    x = json.loads(PREVIOUS_X.read_text(encoding="utf-8"))
    r = json.loads(PREVIOUS_R.read_text(encoding="utf-8"))
    assert len(x["canonical_strict_open_J_side_witnesses"]) == 16
    assert len(x["canonical_fine_exterior_extension_witnesses"]) == 8
    assert len(r["root_ray_tile_cases"]) == 32
    assert r["source_tile_transverse_potential"] == [0,0,1,1]
    assert r["counts"]["rooted_same_parent_original_Jside_points"] == 8

    root = []
    for item in r["root_ray_tile_cases"]:
        if item["proof_class"] != "source_naturality_rooted_finite_Jside":
            continue
        j = item["other_tile"]
        theta = F(item["G_angle"])
        lo,hi = intervals[j]
        side = side_of(theta,lo,hi)
        assert side == item["source_side_at_zero_deck"] != "open_gluing_seam"
        assert (j//2) == (item["anchor_tile"]//2)
        assert j != item["anchor_tile"]
        assert item["root_deck_shift"] == 0
        root.append({
            "source_W_tile": j,
            "ideal_side": side,
            "G_angle": str(theta),
            "ray": item["ray"],
            "physical_target": item["physical_K9_target"],
        })
    removed = []
    for item in x["canonical_strict_open_J_side_witnesses"]:
        j = item["W_tile"]
        z = F(item["lifted_stage_G_angle"])
        lo,hi = intervals[j]
        assert side_of(z,lo,hi) == item["ideal_side"]
        assert modulo_one(z) == F(item["stage_G_angle_mod_one"])
        assert (item["physical_landing_point"],item["excluded_fine_phase"]) in [
            ("x3","D_(0,1)"),("x6","D_(0,2)")
        ]
        removed.append({
            "source_W_tile":j,"ideal_side":item["ideal_side"],
            "G_angle_unwrapped":str(z),
            "angle_mod_one":str(modulo_one(z)),
            "physical_target":item["physical_landing_point"],
            "removed_fine_phase":item["excluded_fine_phase"],
        })
    ordinary = []
    for item in x["canonical_fine_exterior_extension_witnesses"]:
        j=item["W_tile"]
        z=F(item["lifted_stage_G_angle"])
        lo,hi=intervals[j]
        assert side_of(z,lo,hi)==item["ideal_side"]
        assert modulo_one(z)==F(1,3)
        assert item["fine_target_location"].startswith("Omega9")
        ordinary.append({
            "source_W_tile":j,"ideal_side":item["ideal_side"],
            "G_angle_unwrapped":str(z),"angle_mod_one":"1/3",
            "physical_target":"a","fine_target":"Omega9"
        })
    assert len(root)==8 and len(removed)==16 and len(ordinary)==8
    assert {y["ideal_side"] for y in root}=={"xi","eta"}
    assert {y["source_W_tile"] for y in root}=={0,1,2,3}
    assert sorted({y["source_W_tile"] for y in ordinary})==[0,1,2,3]
    assert sorted({y["source_W_tile"] for y in removed})==[0,1,2,3]
    # At each source tile, every category has an explicitly strictly finite witness.
    assert all(
        any(y["source_W_tile"]==i for y in c)
        for i in range(4) for c in (root,removed,ordinary)
    )

    return {
        "schema_version":1,
        "scope":"Strict INTERIORS of finite original G:W KL xi/eta J-side arcs, excluding source vertices, gluing seams, wrapping O/J joints, and entire O sides",
        "mathematical_case_by_physical_G_ray_landing":{
            "K9":"marked root: exactly theta in source E_i and tile j=mate(i) with zero integer native deck shift extends to marked fine root; other strict J-side K9 accesses proper/nonroot",
            "D01_or_D02":"removed fine physical phase: all side lifts proper in full fine surface, no extension into it",
            "K3_minus_three_fine_coarse_root_phases":"ordinary fine exterior Omega9: all side lifts locally extend uniquely to an interior fine-cover point"
        },
        "original_source_phase_sets":{
            "K9":"D_(0,0)", "excluded_left":"D_(0,2)",
            "excluded_right":"D_(0,1)",
            "other_six":"D_(r,j),r=1 or 2, lie outside K3"
        },
        "printed_source":"Kahn-Lyubich II Decorations §§3.2.1-3.2.4, Lemmas 3.3-3.4; Kahn I §7.4.1",
        "sample_exact_witnesses":{
            "marked_fine_root":root,
            "removed_fine_target":removed,
            "ordinary_fine_exterior":ordinary
        },
        "witness_counts":{
            "marked_fine_root":len(root),
            "removed_fine_target":len(removed),
            "ordinary_fine_exterior":len(ordinary),
            "total":len(root)+len(removed)+len(ordinary)
        },
        "finite_source_angle_comparison":"All witness angles are strictly inside genuine original xi/eta J-side half-lines; none is an original vertex or glued seam point",
        "proof_trust_boundary":[
            "K3=J(G) locally connected and its G external Caratheodory landing map is continuous (imported classical analytic theorem)",
            "K3 phase separation: all six fine phases with physical coarse index r=1,2 are disjoint from K3 (previously sourced complex phase argument)",
            "source-native Psi_G(W) holomorphic immersion and continuous physical side-angle landing (Kahn-Lyubich path-space and naturality)",
            "source-native C4 wake transverse character and parameterized K9 root-sheet selection (merged PR #64 written analytic theorem, not Lean)",
            "covering local triviality near ordinary fine exterior and unique marked-root chart near K9 (Kahn I theorem)"
        ],
        "explicitly_open":[
            "Original KL finite vertices at xi/eta endpoint, infinite wrapping O/J joints, full O-lambda sides, and boundary maps to alternate compactifications",
            "Full nine-generator based words for remaining actual KL paths, source path groupoid and KKL unique proper restriction",
            "H1-H4, UPTCR, MLC and all ledger statuses unchanged"
        ]
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    group=p.add_mutually_exclusive_group()
    group.add_argument("--check-manifest",action="store_true")
    group.add_argument("--write-manifest",action="store_true")
    o=p.parse_args()
    result=compute()
    payload=json.dumps(result,sort_keys=True,indent=2)+"\n"
    if o.write_manifest:
        OUT.write_text(payload,encoding="utf-8")
        print("WROTE", OUT)
    elif o.check_manifest:
        assert OUT.read_text(encoding="utf-8")==payload, "manifest drift"
        print("PASS: 8 fine-root, 16 excluded-phase, 8 ordinary-fine interior strict finite KL J-side samples; 3 analytic target classes unchanged")
    else: print(payload,end="")


if __name__=="__main__":
    main()
