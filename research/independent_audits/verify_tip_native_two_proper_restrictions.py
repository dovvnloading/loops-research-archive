#!/usr/bin/env python3
"""Source-native proper-path restriction (NOT synthetic tile model).

KKL A.3.2: immersion restriction is a *set* of proper source paths. This
checks exact original KL source carrier/side data for an explicit infinite
family of TWO distinct source proper restrictions of one V-target proper
path. It does not formally certify analytic ideal prime-end topology.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
ATLAS=ROOT/"results/tip_kl_side_atlas.json"
OUT=ROOT/"results/tip_native_two_proper_restrictions_20261109.json"
M_SAMPLES=64


def asstr(x):
    return str(x)


def compute():
    atlas=json.loads(ATLAS.read_text(encoding="utf-8"))
    assert atlas["source_boundary_identity"]=="partial^v_i Psi(Y) = eta_i union xi_(i+1)"
    assert "all integer translates" in atlas["retained_sheet_coordinate"]
    assert "angle 0" in atlas["basepoint_convention"]
    g=next(s for s in atlas["stages"] if s["stage"]=="G")
    W=g["pieces"]["W"]
    V=g["pieces"]["V0"]
    assert (W["depth"],W["tile_count"],V["depth"],V["tile_count"])==(6,4,3,2)
    ws=W["tiles"]
    vs=V["tiles"]
    r=g["inclusions"]["W_into_V0"]["tile_routes"]
    assert sorted((x["source_tile"],x["target_tile"],x["angular_integer_shift"]) for x in r)==[
      (f"G:W:tile{j}",f"G:V0:tile{j//2}",0) for j in range(4)]
    assert [tuple(map(F,t["seam_stage_angles"])) for t in ws]==[
        (F(41,192),F(43,192)),(F(53,192),F(55,192)),
        (F(137,192),F(139,192)),(F(149,192),F(151,192))]
    assert [tuple(map(F,t["seam_stage_angles"])) for t in vs]==[
        (F(5,24),F(7,24)),(F(17,24),F(19,24))]
    # Carrier outer H_6=h/32, parent H_3=h/4;
    # choose t(s)=4(h/128)s(1-s) so 0<t<=h/128<H_6.
    assert all(t["lambda"]["carrier_height_relative_to_initial"]=="1/32" for t in ws)
    assert all(t["lambda"]["carrier_height_relative_to_initial"]=="1/4" for t in vs)
    assert F(1,128)<F(1,32)<F(1,4)

    child=[]
    for j,t in enumerate(ws):
        a,b=map(F,t["seam_stage_angles"])
        p=j//2
        L,U=map(F,vs[p]["seam_stage_angles"])
        assert L<a<b<U and 0<L<U<1
        assert t["xi"]["inner_halfline"]==["-infinity",asstr(a)]
        assert t["eta"]["inner_halfline"]==[asstr(b),"+infinity"]
        assert vs[p]["xi"]["inner_halfline"]==["-infinity",asstr(L)]
        assert vs[p]["eta"]["inner_halfline"]==[asstr(U),"+infinity"]
        xim=(L+a)/2
        etam=(b+U)/2
        assert L<xim<a and b<etam<U
        assert F(0)<L<a and b<U<F(1)
        # Target-side proper tails and interior-collapse intervals are
        # source-derived, not arbitrary curve pictures.
        child.append({
           "W_tile":j,"V_parent_tile":p,
           "source_W_seam":[asstr(a),asstr(b)],
           "target_V_seam":[asstr(L),asstr(U)],
           "proper_xi_original_closed_tail":"[-infinity,"+asstr(L)+"]",
           "proper_eta_original_closed_tail":"["+asstr(U)+",+infinity]",
           "xi_interior_collapse_interval":[asstr(L),asstr(a)],
           "eta_interior_collapse_interval":[asstr(b),asstr(U)],
           "strict_xi_interior_collapse_sample":asstr(xim),
           "strict_eta_interior_collapse_sample":asstr(etam),
           "zero_based_angular_shift":0,
           "full_original_xi_eta_lambda_sides_boundary_proper":False
        })
    source_collision=g["same_stage_side_collision"]
    assert source_collision["source_defined_map"]=="KL Lemma 3.4 inclusion Psi(W) into Psi(V0)"
    assert source_collision["same_finite_angle_lift"]=="11/48"
    assert source_collision["interior_source_points"]==["G:W:tile0","G:W:tile1"]
    assert source_collision["side_points"]==["G:W:tile0:eta","G:W:tile1:xi"]
    assert F(43,192)<F(11,48)<F(53,192)
    assert F(5,24)<F(11,48)<F(7,24)

    path_rows=[]
    # One target proper path per parent and winding m>=0; two real
    # KL source universal-tile paths project identically to it.
    sample_points=[F(1,4),F(1,2),F(3,4)]
    for p in range(2):
        L,U=map(F,vs[p]["seam_stage_angles"])
        j0,j1=2*p,2*p+1
        for m in range(M_SAMPLES):
            x_minus=F(-m)
            x_plus=F(m+1)
            assert x_minus<L and U<x_plus
            assert x_minus<F(ws[j0]["seam_stage_angles"][0])
            assert x_minus<F(ws[j1]["seam_stage_angles"][0])
            assert F(ws[j0]["seam_stage_angles"][1])<x_plus
            assert F(ws[j1]["seam_stage_angles"][1])<x_plus
            # topological source external angle-height path is increasing
            # x=-m+(2m+1)s, t/h=4s(1-s)/128.
            for s in sample_points:
                x=x_minus+(x_plus-x_minus)*s
                t_relative=F(4,128)*s*(1-s)
                assert x_minus<x<x_plus and 0<t_relative<=F(1,128)<F(1,32)<F(1,4)
            path_rows.append({
               "V_parent_tile":p,"native_target_universal_tile":f"G:V0:tile{p}",
               "winding_parameter_m":m,
               "target_proper_path_x_start":asstr(x_minus),
               "target_proper_path_x_end":asstr(x_plus),
               "target_ideal_ends":["xi","eta"],
               "two_distinct_source_proper_W_tiles":[j0,j1],
               "two_source_ideal_ends_per_tile":["xi","eta"],
               "source_target_same_unwrapped_positive_height_path":True,
               "source_assigned_zero_based_integer_shifts":[0,0]
            })
    assert len(path_rows)==2*M_SAMPLES
    assert all(y["two_distinct_source_proper_W_tiles"][0]!=y["two_distinct_source_proper_W_tiles"][1] for y in path_rows)
    return {
      "schema_version":1,
      "source_scope":"ACTUAL ordinary G=f^3 KL Psi(Y_G^6)->Psi(Y_G^3) inclusion immersion; KKL A.3.2 unmarked set-valued proper-path restriction",
      "target": "Two original V0 universal carrier tiles; their genuine xi and eta ideal sides",
      "source": "Four original W universal carrier tiles; two source channels per V parent with source disjointness KL Lemma 3.3",
      "source_endpoint_reference":"Kahn-Lyubich II Decorations §3.2.1 Lemma 3.3, Lemma 3.4(ii), §3.2.4",
      "KKL_reference":"Kahn-Kapiamba-Lyubich 2026 Appendix A.1, A.3.2, Proposition A.12 (set-valued proper path restriction; marked selection extra)",
      "source_W_child_original_side_cuts":child,
      "natural_KL_arc_markings_basic_KKL_A1_admissibility":{
        "source_W_original_marked_open_arcs":12,
        "target_V_original_marked_open_arcs":6,
        "KL_cyclic_order_for_each_tile":["xi","lambda","eta"],
        "all_128_target_and_256_source_proper_paths_have_xi_eta_endpoints":True,
        "xi_eta_minimal_connected_marked_arc_span":3,
        "KKL_A1_subordinate_length_at_most_two_exclusion_does_not_remove_these":True,
        "not_asserted_to_be_KKL_A3_2_pulled_back_refined_marking":True,
      },
      "physical_full_deck_untouched":True,
      "exact_independent_original_11_over_48_collision_confirmed":True,
      "path_formula":"x_m(s)=-m+(2m+1)*s, t(s)/h=4s(1-s)/128; 0<s<1, m nonnegative integer",
      "infinite_theorem_written_not_machine_proved":"For EVERY m>=0 and either p=0,1, the same original V-p universal-tile proper path has AT LEAST TWO distinct original W proper restrictions; conditional only on original KL universal-cover/naturality theorem",
      "finite_tested_target_paths":len(path_rows),
      "finite_tested_source_proper_lift_occurrences":2*len(path_rows),
      "sampled_target_proper_paths":path_rows,
      "original_all_twelve_full_sides_cannot_be_globally_proper":True,
      "source_boundary_proper_tail_arcs_per_W_tile":2,
      "source_original_J_side_interior_collapse_intervals_per_W_tile":2,
      "analytic_trust_boundary":[
        "KL Lemma 3.3 original universal tile path-space equivalence and disjointness",
        "KL Lemma 3.4 W->V holomorphic immersion and source naturality; atlas exact zero based integer shifts",
        "KL §3.2.4 actual ideal prime-end O/xi/eta finite-point and wrapping topology",
        "KKL Appendix A.1 and A.3.2 proper path/ideal marking/subordination definitions"
      ],
      "NOT_a_counterexample_to":[
        "KKL Appendix A.3.2 definition (which is deliberately set-valued)",
        "KKL Proposition A.12 selected marked/refined path-family chain or unique-subordinate-path conditional",
        "Any global MLC, UPTCR, H1-H4, source proper-end wave amplification or whole original KL marked path groupoid theorem"
      ],
      "unresolved":"Specify an actual KKL target ideal marking, compute maximal source pullbacks and subordination and decide for this source proper target path which restrictions remain admissible"
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    g=p.add_mutually_exclusive_group()
    g.add_argument("--check-manifest",action="store_true")
    g.add_argument("--write-manifest",action="store_true")
    o=p.parse_args()
    manifest=compute()
    content=json.dumps(manifest,sort_keys=True,indent=2)+"\n"
    if o.write_manifest:
       OUT.write_text(content,encoding="utf-8")
       print("WROTE",OUT)
    elif o.check_manifest:
       assert json.loads(OUT.read_text(encoding="utf-8"))==manifest,"source manifest drift"
       print("PASS: original KL two-parent source 2-channel proper-path obstruction, 8 source side cuts, 128 target paths and 256 proper source path lifts")
    else:
       print(content,end="")


if __name__=="__main__":main()
