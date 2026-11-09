#!/usr/bin/env python3
"""Exact, source-locked native W tile deck monodromy and root-selector regression.

Written analytic proofs (source tile prime ends, Kahn localization and proper
escape) are NOT machine-proved. This checks exact rational/source data and
freely reduced word implications, including a zero-winding commutator trap.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ATLAS = ROOT / "results/tip_kl_side_atlas.json"
RAY = ROOT / "results/tip_nested_full_ray_census_20261107.json"
PR60 = ROOT / "results/tip_rooted_native_KL_section_20261108.json"
ROOT_INTERVAL = ROOT / "results/tip_root_interval_geometry.json"
OUT = ROOT / "results/tip_native_root_deck_monodromy_20261109.json"

BETA = (1, 2, 3)  # b00, b01, b02: archived global based convention
N_TEST = 20


def reduce_word(word):
    stack = []
    for g in word:
        assert isinstance(g, int) and 1 <= abs(g) <= 9
        if stack and stack[-1] == -g:
            stack.pop()
        else:
            stack.append(g)
    return tuple(stack)


def power_beta(n):
    return BETA * n if n >= 0 else tuple(-x for x in reversed(BETA)) * (-n)


def winding(word, generator):
    return sum((1 if g > 0 else -1) for g in word if abs(g) == generator)


def in_root_subgroup(word):
    return all(abs(g) == 1 for g in reduce_word(word))


def root_shift_selector(g):
    """Root iff reduced(beta**n * g) belongs to H=<b00>."""
    g = reduce_word(g)
    n = -winding(g, 2)
    return n if in_root_subgroup(power_beta(n) + g) else None


def reduced_words(limit=5):
    yield ()
    for n in range(1, limit + 1):
        for w in product((-3, -2, -1, 1, 2, 3), repeat=n):
            if all(a != -b for a, b in zip(w, w[1:])):
                yield w


def test_free_word_selector():
    checked = 0
    for g in reduced_words(5):
        predicted = root_shift_selector(g)
        exact = [n for n in range(-8, 9) if in_root_subgroup(power_beta(n) + g)]
        assert len(exact) <= 1
        assert exact == ([] if predicted is None else [predicted]), (g, exact, predicted)
        checked += 1
    assert checked == 4687
    commutator = (2, 3, -2, -3)
    assert winding(commutator, 2) == winding(commutator, 3) == 0
    assert root_shift_selector(commutator) is None
    for k in range(-12, 13):
        for m in range(-5, 6):
            g = power_beta(-k) + ((1,) * m if m >= 0 else (-1,) * (-m))
            assert root_shift_selector(g) == k
    return checked


def compute():
    a = json.loads(ATLAS.read_text(encoding="utf-8"))
    r = json.loads(RAY.read_text(encoding="utf-8"))["actual_Levin_3_to_9_ladder"]
    old = json.loads(PR60.read_text(encoding="utf-8"))["actual_source_G_KL_atlas"]
    root = json.loads(ROOT_INTERVAL.read_text(encoding="utf-8"))
    assert root["inner_root_exact_interval"] == "[x9,x18]"
    assert root["phase_intervals_pairwise_disjoint"]
    assert a["source_boundary_identity"] == "partial^v_i Psi(Y) = eta_i union xi_(i+1)"
    stage = next(x for x in a["stages"] if x["stage"] == "G")
    w = stage["pieces"]["W"]
    assert w["depth"] == 6 and len(w["tiles"]) == 4
    original = sorted(old["angle_rows"], key=lambda x: (x["W_tile"], x["slot"]))
    assert len(original) == 8
    rows = []
    for i, row in enumerate(original):
        tile, slot = divmod(i, 2)
        assert row["W_tile"] == tile and row["slot"] == slot
        source = w["tiles"][tile]
        theta = F(row["Pi3"])
        lo, hi = map(F, source["seam_stage_angles"])
        assert lo < theta < hi and F(0) < lo < hi < F(1)
        assert r["Pi3_outer_internal"][row["name"]] == row["Pi3"]
        assert r["Pi9_inner_internal"][row["name"]] == row["Pi9"]
        assert source["id"] == row["source_tile_id"] == f"G:W:tile{tile}"
        assert source["xi"]["inner_halfline"][1] == str(lo)
        assert source["eta"]["inner_halfline"][0] == str(hi)
        assert "not a remaining ideal J side" in source["central_seam_warning"]
        for n in range(-N_TEST, N_TEST + 1):
            if not n:
                continue
            x = theta + n
            assert (x < lo if n < 0 else x > hi)
            assert winding(power_beta(n), 2) == n
            assert winding(power_beta(n), 3) == n
            assert not in_root_subgroup(power_beta(n))
            assert root_shift_selector(power_beta(n)) == -n
        rows.append({
            "tile": tile, "slot": slot, "ray": row["name"],
            "anchor_G_angle": str(theta),
            "fine_Pi9": row["Pi9"], "physical_K9_target": row["physical_K9_target"],
            "minus_one_source_xi_angle": str(theta - 1),
            "plus_one_source_eta_angle": str(theta + 1),
            "zero_shift_root": True, "nonzero_integer_shift_root": False,
        })
    return {
        "schema_version": 1,
        "theorem_scope": "Native original G=f^3 W=Y_G^6 universal tiles; exact own-seam root anchors and all nonzero integer deck translates. Not all source prescribed KL connectors.",
        "canonical_root_subgroup": "H=<b00> in F(b00,b01,b02,b10,...,b22)",
        "archived_based_coarse_meridian_word": ["b00", "b01", "b02"],
        "winding_D01_per_positive_native_tile_deck": 1,
        "winding_D02_per_positive_native_tile_deck": 1,
        "anchor_rows": rows,
        "certified_finite_source_side_witnesses": 16,
        "source_anchor_count": 8,
        "sampled_nonzero_deck_shifts_per_anchor": 40,
        "sampled_nonroot_lifts": 320,
        "free_word_selector_reduced_samples_length_le_5": test_free_word_selector(),
        "commutator_zero_abelianization_nonroot": True,
        "analytic_proofs_not_formalized": [
            "KL universal-tile ideal-side prime ends and carrier-annulus source deck normalization",
            "The native tile generator winds once about excluded fine D_(0,1) and D_(0,2)",
            "Kahn root-biholomorphic chart and the previously source-certified marked holomorphic immersion",
            "Infinite distinctness, nonroot convergence obstruction and proper escape from all compacta",
        ],
        "unresolved": [
            "Other-tile prescribed KL coarse connectors g_theta are not computed",
            "Full source-native whole-side ideal circle map and unique KKL proper restriction not proved",
            "H1-H4, UPTCR, MLC unchanged and open",
        ],
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--check-manifest", action="store_true")
    mode.add_argument("--write-manifest", action="store_true")
    options = p.parse_args()
    result = compute()
    if options.write_manifest:
        OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print("WROTE", OUT)
    elif options.check_manifest:
        assert json.loads(OUT.read_text(encoding="utf-8")) == result, "manifest drift"
        print("PASS: 8 actual G W seam anchors; 16 named-root J-side witnesses; 320 deck checks; 4,687 free-word selectors")
    else:
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
