#!/usr/bin/env python3
"""Fail-closed Issue 62 word audit. Exact finite statements only.

This cannot certify a physical path not represented by interval/geometry data.
Prior sheet labels are imported analytic-conditional claims, not newly proved.
"""
from __future__ import annotations

import argparse
import copy
import json
import subprocess
import sys
from fractions import Fraction
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = ROOT / "research/independent_audits/issue62_connector_defects_20261116/finite_j_side_footprints.json"
OUTPUT = HERE / "word_status.json"
BETA = (1, 2, 3)  # b00*b01*b02, not b00
ANCHORS = {
    "qR": (0, "3/14", "1/2", "left_tip"),
    "d": (0, "25/112", "3/4", "zero_lower"),
    "e": (1, "31/112", "3/4", "zero_lower"),
    "pR": (1, "2/7", "0", "right_tip"),
    "pL": (2, "5/7", "0", "right_tip"),
    "a": (2, "81/112", "1/4", "zero_upper"),
    "b": (3, "87/112", "1/4", "zero_upper"),
    "qL": (3, "11/14", "1/2", "left_tip"),
}
SEAMS = tuple((Fraction(a), Fraction(b)) for a, b in (
    ("41/192", "43/192"), ("53/192", "55/192"),
    ("137/192", "139/192"), ("149/192", "151/192"),
))
V_SEAMS = ((Fraction(40, 192), Fraction(56, 192)),
           (Fraction(136, 192), Fraction(152, 192)))
NULL_FIELDS = (
    "coarse_polygon_or_ray_equipotential",
    "rooted_polygon_or_ray_equipotential",
    "nine_signed_cut_crossings",
    "basis_change_certificate",
    "based_F9_defect_word",
)


def check(ok, reason):
    if not ok:
        raise AssertionError(reason)


def reduced(word):
    stack = []
    for letter in word:
        check(type(letter) is int and 1 <= abs(letter) <= 9,
              f"invalid F9 letter: {letter!r}")
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def inv(word):
    return tuple(-a for a in reversed(word))


def hpow(n):
    return ((1,) * n) if n >= 0 else ((-1,) * (-n))


def betapow(n):
    return (BETA * n) if n >= 0 else (inv(BETA) * (-n))


def in_h(word):
    return all(abs(a) == 1 for a in reduced(word))


def same_left_coset(u, v):
    return in_h(tuple(u) + inv(tuple(v)))


def wind(word, generator):
    return sum((1 if a == generator else -1 if a == -generator else 0)
               for a in word)


def select_shift(g):
    n = -wind(g, 2)
    return n if in_h(betapow(n) + tuple(g)) else None


def sample_words():
    yield ()
    letters = tuple(range(-9, 0)) + tuple(range(1, 10))
    for n in (1, 2):
        for word in product(letters, repeat=n):
            if all(a != -b for a, b in zip(word, word[1:])):
                yield word


def verify_free_words():
    """325 complete freely reduced words of length <=2 in F9; no geometry."""
    check(BETA == (1, 2, 3) and not in_h(BETA), "beta0 conflated with b00")
    check(reduced(BETA + inv(BETA)) == (), "beta cancellation")
    check(reduced(BETA + (4,)) != reduced((4,) + BETA),
          "noncommutative prefix/suffix collapsed")
    commutator = (2, 3, -2, -3)
    check(all(wind(commutator, j) == 0 for j in range(1, 10))
          and not in_h(commutator) and select_shift(commutator) is None,
          "zero-homology commutator is not a rooted word")
    nchecked = 0
    for g in sample_words():
        check(reduced(g) == g, "word generator did not enumerate reduced words")
        # Free cancellation models endpoint-fixed homotopy ONLY AFTER an
        # actual based nine-cut system and physical path have been certified.
        for a in range(-9, 10):
            if a == 0:
                continue
            for k in range(len(g) + 1):
                check(reduced(g[:k] + (a, -a) + g[k:]) == g,
                      "adjacent inverse insertion changed the class")
        for m in (-2, -1, 0, 1, 2):
            moved = reduced(g + hpow(-m))
            check(in_h(moved) == in_h(g),
                  "changing rooted W reference changed H membership")
            if not in_h(g) and m != 0:
                check(not same_left_coset(g, moved),
                      "malnormal nonroot right-H gauge was silently collapsed")
            if in_h(g):
                check(same_left_coset(g, moved),
                      "rooted right-H gauge changed the H sheet")
        # Check left coset equality with the CORRECT order, not right cosets.
        for n in (-2, -1, 0, 1, 2):
            for m in (-2, -1, 0, 1, 2):
                check(same_left_coset(betapow(n) + g, betapow(m) + g)
                      == (n == m), "distinct based coarse prefixes collapsed")
        expected = [n for n in range(-3, 4) if in_h(betapow(n) + g)]
        selected = select_shift(g)
        check(expected == ([] if selected is None else [selected]),
              "F9 root shift cannot be selected just from winding")
        # A basepoint path u changes the based group AND H by conjugacy.
        u = (4, -5, 6)
        transported = reduced(u + g + inv(u))
        restored = reduced(inv(u) + transported + u)
        check(restored == g and in_h(restored) == in_h(g),
              "based transport must carry H, not retain old generators")
        nchecked += 1
    check(nchecked == 325, "wrong complete F9 length<=2 census")
    # Exact finite counterexample: coarse g fixed, fine root kappa changed
    # by b00. The literal word and nonroot left-coset coordinate both change.
    check(reduced((2,) + hpow(-1)) == (2, -1) and
          not same_left_coset((2,), (2, -1)) and
          not in_h((2, -1)) and not in_h((2,)),
          "nonroot root-reference gauge example")
    return nchecked


def expected_manifest(source):
    rows = source["rows"]
    check(len(rows) == 88 and source["counts"]["marked_fine_root"] == 8
          and source["counts"]["proper_fine_nonroot"] == 80
          and source["full_KL_prescribed_based_F9_words"] is None,
          "original audit counts/word gate changed")
    result_rows = []
    seen = set()
    nroot = 0
    for row in rows:
        ray = row["anchor_ray"]
        check(ray in ANCHORS, "unrecognized certified source anchor")
        i, angle, fine, target = ANCHORS[ray]
        j = row["source_W_tile"]
        n = row["native_integer_shift"]
        check(type(j) is int and 0 <= j < 4 and n in (-1, 0, 1),
              "not an original finite W row")
        key = (ray, j, n)
        check(key not in seen, "duplicate anchored KL J-side point")
        seen.add(key)
        theta = Fraction(angle)
        x = Fraction(row["unwrapped_G_angle"])
        check(row["anchor_W_tile"] == i
              and SEAMS[i][0] < theta < SEAMS[i][1]
              and row["physical_G_angle_mod_one"] == angle
              and x == theta + n and row["fine_Pi9"] == fine
              and row["physical_K9_target"] == target
              and row["source_V_parent"] == j // 2,
              "source G physical/access/parent mismatch")
        lo, hi = SEAMS[j]
        check(x != lo and x != hi, "vertex is not strict J")
        check(not (n == 0 and j == i), "open seam is not a J side")
        side = "xi" if x < lo else "eta" if x > hi else None
        check(side is not None and side == row["original_ideal_side"],
              "source original xi/eta halfline wrong")
        vl, vu = V_SEAMS[j // 2]
        collapse = (side == "xi" and vl < x < lo) or (
            side == "eta" and hi < x < vu)
        should_root = (n == 0 and j == (i ^ 1))
        check(collapse == should_root, "source W->V rational gap mismatch")
        check(row["fine_sheet_footprint"] ==
              ("marked_root" if should_root else "proper_nonroot")
              and row["KL_W_to_V_boundary_footprint"] ==
              ("V_interior_collapse" if should_root
               else "V_boundary_proper_tail"),
              "prior analytic-conditional fine/V labels mismatch")
        check(row["based_F9_defect_word"] is None,
              "original audit supplied a word; update evidence before reuse")
        nroot += int(should_root)
        rec = {
            "anchor_ray": ray,
            "source_W_tile": j,
            "native_integer_shift": n,
            "original_ideal_side": side,
            "unwrapped_G_angle": row["unwrapped_G_angle"],
            "prior_fine_sheet_footprint": row["fine_sheet_footprint"],
            "conditional_required_F9_root_subgroup_membership":
                "in_H" if should_root else "outside_H",
        }
        rec.update({key: None for key in NULL_FIELDS})
        result_rows.append(rec)
    check(nroot == 8 and len(seen) == 88 and
          all((ray, j, n) in seen for ray, (i, *_) in ANCHORS.items()
              for j in range(4) for n in (-1, 0, 1)
              if not (j == i and n == 0)),
          "not precisely the 88 original KL finite-side positions")
    return {
        "schema_version": 1,
        "source_manifest": str(SOURCE.relative_to(ROOT)),
        "status": "no_physical_KL_connector_words_certified",
        "gauge_convention":
            "g=kappa_prime*kappa_inverse; left H\\F9 cosets/right monodromy; beta0=b00*b01*b02",
        "counts": {
            "certified_exact_based_F9_words": 0,
            "remaining_null_words": 88,
            "prior_analytic_conditional_root_rows": 8,
            "prior_analytic_conditional_nonroot_rows": 80,
        },
        "rows": result_rows,
    }


def reject_uncertified_words(manifest):
    """Intentionally fail closed until a real geometric certificate verifier exists."""
    check(manifest["counts"]["certified_exact_based_F9_words"] == 0,
          "nonzero words certified without a geometric verifier")
    check(manifest["counts"]["remaining_null_words"] == 88,
          "the original cohort has been silently shortened")
    for row in manifest["rows"]:
        for name in NULL_FIELDS:
            check(name in row and row[name] is None,
                  f"uncertified geometry or based F9 word: {name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-manifest", action="store_true")
    opts = parser.parse_args()
    # Trust but independently rerun the upstream original-source checks.
    upstream = ROOT / "research/independent_audits/issue62_connector_defects_20261116/verify_issue62.py"
    subprocess.run([sys.executable, str(upstream), "--check-manifest"],
                   cwd=ROOT, check=True)
    expected = expected_manifest(json.loads(SOURCE.read_text(encoding="utf-8")))
    reject_uncertified_words(expected)
    altered = copy.deepcopy(expected)
    altered["rows"][0]["based_F9_defect_word"] = []  # even identity is unproved
    try:
        reject_uncertified_words(altered)
    except AssertionError:
        pass
    else:
        raise AssertionError("failed to reject a fabricated identity word")
    count = verify_free_words()
    if opts.check_manifest:
        actual = json.loads(OUTPUT.read_text(encoding="utf-8"))
        reject_uncertified_words(actual)
        check(actual == expected, "88-row word-status manifest mismatch")
        print(f"PASS: 88 null words, 8 conditional roots, 80 conditional nonroots; {count} F9 words; fail-closed injection test")
    else:
        print(json.dumps(expected, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
