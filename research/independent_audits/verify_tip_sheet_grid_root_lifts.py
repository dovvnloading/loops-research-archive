#!/usr/bin/env python3
"""Exact nine-meridian free-word and actual 3/9 ray-cohort audit.

This *does not* prove analytic covering, compactness, or physical ray landing:
those have separate written proofs with explicitly cited imported results.

python research/independent_audits/verify_tip_sheet_grid_root_lifts.py --check-manifest
"""
from __future__ import annotations

import argparse
from itertools import product
from fractions import Fraction as Q
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "results" / "tip_sheet_grid_root_lifts_20261108.json"
SOURCE = ROOT / "results" / "tip_levin_composition_escape_20261108.json"
ATLAS = ROOT / "results" / "tip_actual_coarse_only_ray_pairing_20261107.json"

# True source based meridians b_(r,j) occupy the 9 free generators 1..9.
HGEN = 1
BETA = ((1, 2, 3), (4, 5, 6), (7, 8, 9))

def inv(w: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(-x for x in reversed(w))

def red(w: tuple[int, ...]) -> tuple[int, ...]:
    out = []
    for a in w:
        assert 1 <= abs(a) <= 9
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)

def mul(*ws: tuple[int, ...]) -> tuple[int, ...]:
    return red(tuple(a for w in ws for a in w))

def poww(w: tuple[int, ...], m: int) -> tuple[int, ...]:
    return mul(*([w if m >= 0 else inv(w)] * abs(m)))

def wind(w: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * 9
    for a in w:
        out[abs(a)-1] += 1 if a > 0 else -1
    return tuple(out)

def charge(w: tuple[int, ...]) -> tuple[int, int]:
    x = wind(w)
    return x[1] - x[2], x[2]

def h_member(w: tuple[int, ...]) -> bool:
    return all(abs(x) == HGEN for x in red(w))

def left_H_equal(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    return h_member(mul(a, inv(b)))

def sheet(k: int, n: int) -> tuple[int, ...]:
    return mul(poww((2,), k), poww(BETA[0], n))

def grid_test() -> dict:
    nodes = {}
    for k, n in product(range(-8, 9), repeat=2):
        w = sheet(k, n)
        assert charge(w) == (k, n)
        # H-invariance, coarse-loop shift, and component invariance.
        assert charge(mul((1, 1), w)) == (k, n)
        assert charge(mul(w, BETA[0])) == (k, n+1)
        assert charge(mul(w, BETA[1])) == (k, n)
        assert charge(mul(w, BETA[2])) == (k, n)
        nodes[(k, n)] = w
    comparisons = 0
    for x, y in product(nodes, repeat=2):
        assert left_H_equal(nodes[x], nodes[y]) == (x == y)
        comparisons += 1
    assert comparisons == 83521
    for k in range(-8, 9):
        assert {charge(nodes[(k,n)])[0] for n in range(-8,9)} == {k}
    return {"window": [-8, 8], "source_grid_sheets": len(nodes),
            "exact_pairwise_left_coset_tests": comparisons,
            "two_characters": ["w01-w02", "w02"],
            "grid_word": "H*b01^k*(b00*b01*b02)^n",
            "coarse_peripheral": "right beta0 adds one to winding n"}

def universal_cover_test() -> dict:
    # For all nonzero integers m, beta0^m has nonzero winding about D_01
    # and D_02. Every conjugate of H=<b00> has zero winding there.
    tests = 0
    for m in range(-128, 129):
        if m == 0:
            continue
        v = poww(BETA[0], m)
        assert wind(v)[1] == wind(v)[2] == m
        assert not h_member(v)
        for k in (-5, 0, 2, 7):
            g = poww((3,), k)
            conj = mul(g, poww((1,), m), inv(g))
            assert wind(conj)[1] == wind(conj)[2] == 0
            assert wind(v)[1] != wind(conj)[1]
            tests += 1
    assert tests == 1024
    return {"coarse_generator_words": [list(w) for w in BETA],
            "fine_H_generator": 1,
            "certified_nonzero_core_vs_conjugate_checks": tests,
            "full_theorem": "Gamma_coarse intersect g^-1 H g = {1} for all g in F9; injective coarse free-product map needed",
            "lifting_consequence": "any connected coarse cover admitting a based fine lift must be the universal cover"}

def ray_type_test() -> dict:
    d = json.loads(SOURCE.read_text(encoding="utf-8"))
    atlas = json.loads(ATLAS.read_text(encoding="utf-8"))
    g = d["geometric_32_8_24"]
    coarse = sorted(g["coarse32_numerators"])
    fine = sorted(g["fine8_numerators"])
    escaped = sorted(g["excluded24_numerators"])
    assert (len(coarse), len(fine), len(escaped)) == (32, 8, 24)
    assert len(set(coarse)) == 32 and set(coarse) == set(fine) | set(escaped)
    assert set(fine).isdisjoint(set(escaped))
    assert fine == [116736,116791,144841,144896,
                    378368,378423,406473,406528]
    groups = atlas["complete_15_landing_points"]
    fin = [x for x in groups if x["G_top_critical_Y3_face"]]
    loss = [x for x in groups if not x["G_top_critical_Y3_face"]]
    assert (len(fin),len(loss)) == (3,12)
    assert sorted(a for x in fin for a in x["ambient_523264_numerators"]) == fine
    assert sorted(a for x in loss for a in x["ambient_523264_numerators"]) == escaped
    assert sorted(len(x["ambient_523264_numerators"]) for x in fin) == [2,2,4]
    assert all(len(x["ambient_523264_numerators"]) == 2 for x in loss)
    faces = {}
    for x in loss:
        key = x["G_original_depth3_alpha_face_signature"]
        faces[key] = faces.get(key, 0) + 1
    assert sorted(faces.values()) == [2,2,4,4]
    return {
        "ambient_denominator":523264, "source_ray_count":len(coarse),
        "fine_survivors":fine, "interior_escapes":escaped,
        "fine_physical_landing_points":3,
        "coarse_only_interior_points":12,
        "coarse_only_original_face_counts":dict(sorted(faces.items())),
        "root_compatible_lifts_per_surviving_ray":1,
        "proper_fine_exterior_lifts_per_surviving_ray":"countably infinite",
        "proper_fine_exterior_lifts_per_escaped_ray":0,
        "interior_convergent_fine_lifts_per_escaped_ray":"countably infinite",
        "source_of_analytic_lift_claims":"Kahn marked local cover, local inverse and evenly-covered disks: written proof, not machine certification"
    }

def compute() -> dict:
    return {"schema_version":1,
            "scope":"ACTUAL based 3/9 canonical-localization sheets and specified physical ray cohort; MLC open",
            "grid":grid_test(),"universal_cover":universal_cover_test(),
            "physical_8_24_types":ray_type_test(),
            "slit_transport":"radial slit in finite-modulus coarse annulus makes each universal pullback component biholomorphic",
            "nonimplication":"one ROOT-compatible lift is NOT one proper lift"}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    q=p.add_mutually_exclusive_group()
    q.add_argument("--check-manifest",action="store_true")
    q.add_argument("--write-manifest",action="store_true")
    args=p.parse_args()
    payload=compute()
    if args.write_manifest:
        OUT.write_text(json.dumps(payload,indent=2,sort_keys=True)+"\n",encoding="utf-8")
        print("WROTE",OUT)
    elif args.check_manifest:
        expected=json.loads(OUT.read_text(encoding="utf-8"))
        assert expected == payload, "manifest mismatch"
        print("PASS: Z^2 grid, 83521 left-coset checks, universal lift obstruction, and 8/24 types")
    else:
        print(json.dumps(payload,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
