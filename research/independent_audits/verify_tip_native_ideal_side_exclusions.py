#!/usr/bin/env python3
"""Exact finite-angle first-failure certificate for native G:W KL J-sides.

This checker imports the existing source-defined KL atlas, the certified
3-to-9 Levin ray table, and the exact real fine-phase manifest. It checks
rational identities, tile/ideal-side placement, and integer-translate tests.
The analytic ray-landing, prime-end model, and non-extension lemma are
WRITTEN mathematical arguments, not proved by this program.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ATLAS = ROOT / "results/tip_kl_side_atlas.json"
LEV = ROOT / "results/tip_nested_full_ray_census_20261107.json"
PHASES = ROOT / "results/tip_root_interval_geometry.json"
OUT = ROOT / "results/tip_native_ideal_side_exclusions_20261108.json"


def mod1(x: Q) -> Q:
    return x - (x.numerator // x.denominator)


def side_of(lift: Q, low: Q, high: Q) -> str:
    if lift < low:
        return "xi"
    if lift > high:
        return "eta"
    return "glued_seam_or_vertex"


def compute() -> dict:
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    stage = next(s for s in atlas["stages"] if s["stage"] == "G")
    W = stage["pieces"]["W"]
    assert (W["depth"], W["tile_count"]) == (6, 4)
    assert stage["ordinary_stage_filled_set"] == "K3"
    assert stage["terminal_root"] == "K9"
    assert atlas["source_boundary_identity"] == "partial^v_i Psi(Y) = eta_i union xi_(i+1)"
    seams = [tuple(map(Q, tile["seam_stage_angles"])) for tile in W["tiles"]]
    assert seams == [
        (Q(41, 192), Q(43, 192)), (Q(53, 192), Q(55, 192)),
        (Q(137, 192), Q(139, 192)), (Q(149, 192), Q(151, 192)),
    ]

    rays = json.loads(LEV.read_text(encoding="utf-8"))[
        "actual_Levin_3_to_9_ladder"]
    Pi3 = rays["Pi3_outer_internal"]
    critical = [Q(Pi3[k]) for k in ("d", "e", "a", "b")]
    assert critical == [Q(25, 112), Q(31, 112), Q(81, 112), Q(87, 112)]
    assert rays["outer_critical_quartet"] == {
        "a": "81/112", "b": "87/112", "d": "25/112", "e": "31/112"
    }
    # G doubles marked external angles on the polynomial-like K3 stage.
    value = sorted({mod1(2 * angle) for angle in critical})
    second = sorted({mod1(2 * angle) for angle in value})
    assert value == [Q(25, 56), Q(31, 56)]
    assert second == [Q(3, 28), Q(25, 28)]

    phases = json.loads(PHASES.read_text(encoding="utf-8"))
    # Source G dividing-fixed-point rays, used as locally extendible
    # counterpoints to the x3/x6 omitted-phase ideal J-side rays.
    p_boundary = stage["pieces"]["P"]["boundary_vertices"]
    assert "1/3,2/3" in {v["stage_ray_pair"] for v in p_boundary}
    assert "1/3" not in {str(x) for seam in seams for x in seam}

    assert phases["phase_intervals_pairwise_disjoint"] is True
    assert phases["inner_root_exact_interval"] == "[x9,x18]"
    physical = {row["physical_phase"]: row for row in phases["phase_intervals"]}
    assert len(physical) == 9
    assert physical[0]["exact_interval"] == "[x9,x18]"
    assert physical[3]["exact_interval"] == "[x12,x3]"
    assert physical[6]["exact_interval"] == "[x6,x15]"
    assert physical[3]["coarse_phase"] == physical[6]["coarse_phase"] == 0

    # All these sides are TRUE ideal J-sides: the open W seam is removed by
    # gluing, and the rays used here lie strictly outside it.
    targets = [(angle, "x3", "D_(0,1)") for angle in value] + [
        (angle, "x6", "D_(0,2)") for angle in second]
    canonical = []
    positive = []
    exhaustive_finite = 0
    positive_tail_finite = 0
    for i, ((lo, hi), tile) in enumerate(zip(seams, W["tiles"])):
        assert tile["index"] == i and tile["id"] == f"G:W:tile{i}"
        assert tile["xi"]["inner_halfline"] == ["-infinity", str(lo)]
        assert tile["eta"]["inner_halfline"] == [str(hi), "+infinity"]
        assert "not a remaining ideal J side" in tile["central_seam_warning"]
        assert Q(0) < lo < hi < Q(1)
        for angle, point, phase in targets:
            assert side_of(angle, lo, hi) != "glued_seam_or_vertex"
            assert mod1(angle) == angle
            for k in range(-16, 0):
                assert side_of(angle + k, lo, hi) == "xi"
                exhaustive_finite += 1
            for k in range(1, 17):
                assert side_of(angle + k, lo, hi) == "eta"
                exhaustive_finite += 1
        # The original dividing fixed point a, reached by source rays 1/3
        # and 2/3, cannot belong to a disjoint G-three-cycle phase D_(0,j).
        # Its prime-end tails therefore have ordinary fine-cover limits.
        for side, stage_lift in (("xi", Q(1, 3) - 1), ("eta", Q(1, 3) + 1)):
            assert side_of(stage_lift, lo, hi) == side
            assert mod1(stage_lift) == Q(1, 3)
            positive.append({"W_tile": i, "ideal_side": side,
                             "lifted_stage_G_angle": str(stage_lift),
                             "stage_G_angle_mod_one": "1/3",
                             "physical_landing_point": "a (G-fixed dividing point)",
                             "fine_target_location": "Omega9 (nonroot exterior)"})
        for k in list(range(-16, 0)) + list(range(1, 17)):
            assert side_of(Q(1, 3) + k, lo, hi) == ("xi" if k < 0 else "eta")
            positive_tail_finite += 1
        # A very small canonical witness set: every source W tile has both
        # excluded fine-phase landing targets on EACH open J-side.
        examples = [
            ("xi", Q(25, 56) - 1, "x3", "D_(0,1)"),
            ("xi", Q(3, 28), "x6", "D_(0,2)"),
            ("eta", Q(25, 56) + 1, "x3", "D_(0,1)"),
            ("eta", Q(25, 28), "x6", "D_(0,2)"),
        ]
        for side, angle_lift, point, phase in examples:
            assert side_of(angle_lift, lo, hi) == side
            assert (mod1(angle_lift), point, phase) in targets
            canonical.append({
                "W_tile": i, "ideal_side": side,
                "lifted_stage_G_angle": str(angle_lift),
                "stage_G_angle_mod_one": str(mod1(angle_lift)),
                "physical_landing_point": point,
                "excluded_fine_phase": phase,
            })
    assert len(canonical) == 16 and exhaustive_finite == 512
    assert len(positive) == 8 and positive_tail_finite == 128
    assert {r["ideal_side"] for r in canonical} == {"xi", "eta"}

    return {
        "schema_version": 1,
        "scope": "finite points strictly inside every native G:W xi/eta ideal side; not central glued seams or a global KL proper-path theorem",
        "source_stage": "G=f^3; ordinary K3 Julia set with fine K9 marked root",
        "original_KL_source": "Kahn--Lyubich II Decorations, section 3.2.1, Lemmas 3.3/3.4, section 3.2.4",
        "outer_K3_critical_point_angles": [str(x) for x in critical],
        "G_critical_value_x3_angles": [str(x) for x in value],
        "G_second_critical_value_x6_angles": [str(x) for x in second],
        "excluded_fine_phases": ["D_(0,1)=G(K9)", "D_(0,2)=G^2(K9)"],
        "canonical_strict_open_J_side_witnesses": canonical,
        "canonical_fine_exterior_extension_witnesses": positive,
        "positive_witness_count": len(positive),
        "positive_integer_tail_regression_count": positive_tail_finite,
        "canonical_witness_count": len(canonical),
        "translated_side_regression_count": exhaustive_finite,
        "all_integer_tail_statement": "each of the four postcritical angles theta has theta+n strictly in xi_i for all n<=-1 and strictly in eta_i for all n>=1, for every original W tile i",
        "written_analytic_consequence_not_machine_proved": "x3/x6 excluded-phase ideal side points cannot extend into T_hat9; by covering local triviality, each source ray at the G-fixed dividing point a outside all fine phases has a unique local extension into T_hat9, with source sheet retained",
        "not_claimed": [
            "no impossibility for other target compactifications or protected side subarcs",
            "no proof of the remaining KL-prescribed connector defect words",
            "no unique proper restriction, UPTCR, H1-H4 or MLC proof",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check-manifest", action="store_true")
    mode.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()
    output = json.dumps(compute(), sort_keys=True, indent=2) + "\n"
    if args.write_manifest:
        OUT.write_text(output, encoding="utf-8")
        print("WROTE", OUT)
    elif args.check_manifest:
        assert OUT.read_text(encoding="utf-8") == output, "manifest mismatch"
        print("PASS: 16 excluded-phase and 8 locally extendible native J-side witnesses; 640 exact translated-side checks")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
