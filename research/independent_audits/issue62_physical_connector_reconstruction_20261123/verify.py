#!/usr/bin/env python3
"""Exact crossing certificate for actual G-ray cuts and native KL tile paths.

The physical realization is proved in NOTE.md. This file checks exact
rational intersections in that certified homeomorphic carrier chart; it
does not numerically approximate the straightening or prove ray landing.
Only the Python standard library is used. Historical manifests are read,
never changed, and their root classifications are used only for comparison.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
DEFAULT_REPO = HERE.parents[2]
MANIFEST = HERE / "certificate.json"
SOURCE_WORDS = Path("research/independent_audits/issue62_connector_words_20261116/word_status.json")
SOURCE_ROWS = Path("research/independent_audits/issue62_connector_defects_20261116/finite_j_side_footprints.json")
SOURCE_ATLAS = Path("results/tip_kl_side_atlas.json")
NAMES = ("b00", "b01", "b02", "b10", "b11", "b12", "b20", "b21", "b22")
CUTS = ((F(249, 896), 1), (F(25, 56), 2), (F(25, 28), 3))
SEAMS = tuple((F(a, 192), F(b, 192)) for a, b in ((41, 43), (53, 55), (137, 139), (149, 151)))
MIDPOINTS = tuple((a + b) / 2 for a, b in SEAMS)
BETA = (1, 2, 3)
P = ((), (1,), (1, 2), (1, 2))
OCTAL_OFFSETS = (3, 4, 11, 12)
HEIGHT = F(1, 256)
SECOND_HEIGHT = F(1, 512)
ENDPOINT_HEIGHT = F(1, 1024)
ANCHORS = {
    "qR": (F(3, 14), 0, "1/2", "left_tip"),
    "d": (F(25, 112), 0, "3/4", "zero_lower"),
    "e": (F(31, 112), 1, "3/4", "zero_lower"),
    "pR": (F(2, 7), 1, "0", "right_tip"),
    "pL": (F(5, 7), 2, "0", "right_tip"),
    "a": (F(81, 112), 2, "1/4", "zero_upper"),
    "b": (F(87, 112), 3, "1/4", "zero_upper"),
    "qL": (F(11, 14), 3, "1/2", "left_tip"),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def reduce_word(word):
    out = []
    for letter in word:
        require(isinstance(letter, int) and 1 <= abs(letter) <= 9, "invalid F9 letter")
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def inverse(word):
    return tuple(-letter for letter in reversed(word))


def product(*words):
    return reduce_word(letter for word in words for letter in word)


def power(word, n):
    return reduce_word((word if n >= 0 else inverse(word)) * abs(n))


def names(word):
    return [NAMES[abs(i) - 1] + ("^-1" if i < 0 else "") for i in word]


def in_root_subgroup(word):
    return all(abs(i) == 1 for i in reduce_word(word))


def winding(word):
    ans = [0] * 9
    for i in word:
        ans[abs(i) - 1] += 1 if i > 0 else -1
    return ans


def direct_crossings(start, end):
    """Signed crossings of the physical horizontal path in its exact chart.

    Start/end must be off cuts. Only integer translates in the finite
    coordinate range are examined; no rounded coordinate is used.
    """
    for a, _ in CUTS:
        require((start - a).denominator != 1, "start lies on a cut")
        require((end - a).denominator != 1, "end lies on a cut")
    lo, hi = sorted((start, end))
    crossings = sorted(
        (a + k, letter, k)
        for a, letter in CUTS
        for k in range(lo.__floor__() - 1, hi.__ceil__() + 1)
        if lo < a + k < hi
    )
    if end < start:
        crossings.reverse()
    sign = 1 if end >= start else -1
    return [
        {"unwrapped_crossing_angle": str(a), "cut": NAMES[letter - 1],
         "cut_translate": k, "sign": sign, "signed_letter": sign * letter}
        for a, letter, k in crossings
    ]


def q_word(theta):
    """Baseline sector word, with a declared lower-angle bank root-cut convention."""
    require(0 <= theta < 1, "theta must be represented in [0,1)")
    if theta <= CUTS[0][0]:
        return ()
    if theta < CUTS[1][0]:
        return (1,)
    if theta < CUTS[2][0]:
        return (1, 2)
    return (1, 2, 3)


def formula_word(j, theta, n):
    return product(inverse(P[j]), power(BETA, n), q_word(theta))


def address_word(j, i, first_octal_digit, n):
    """Full word from a physical root-angle address, including irrationals.

    The exact physical domain is theta=(C+OCTAL_OFFSETS[i])/16. Only
    C's first octal symbol is needed; its remaining infinite tail is
    irrelevant to this relative word. The unbounded integer n is retained.
    """
    require(i in range(4) and j in range(4), "invalid native tile")
    require(first_octal_digit in (3, 4), "invalid Cantor octal symbol")
    q = () if i == 0 or (i == 1 and first_octal_digit == 3) else (1,) if i == 1 else (1, 2)
    return product(inverse(P[j]), power(BETA, n), q)


def native_deck_word(j):
    return product(inverse(P[j]), BETA, P[j])


def second_crossings(j, theta, n):
    """A different actual path: return to m0, make n turns, go to theta.

    These three horizontal legs are at h/512, rather than h/256. Their
    unwrapped endpoints are m_j, m0, m0+n, theta+n. Their lift is homotopic
    relative endpoints to the first monotone horizontal leg in the strip.
    Crossings need not be reduced before concatenation, so this also
    exercises the full noncommutative order and cancellations.
    """
    vertices = (MIDPOINTS[j], MIDPOINTS[0], MIDPOINTS[0] + n, theta + n)
    out = []
    for leg, (start, end) in enumerate(zip(vertices, vertices[1:])):
        for crossing in direct_crossings(start, end):
            out.append({"leg": leg, **crossing})
    return out


def schema_source_rows(repo):
    old = json.loads((repo / SOURCE_WORDS).read_text())
    source = json.loads((repo / SOURCE_ROWS).read_text())
    require(len(old["rows"]) == len(source["rows"]) == 88, "historical cohort changed")
    key = lambda r: (r["anchor_ray"], r["source_W_tile"], r["native_integer_shift"])
    old_by_key = {key(r): r for r in old["rows"]}
    require(len(old_by_key) == 88, "duplicate historical word rows")
    expected_keys = {
        (name, j, n) for name, (_, i, _, _) in ANCHORS.items()
        for j in range(4) for n in (-1, 0, 1) if not (j == i and n == 0)
    }
    require(set(old_by_key) == expected_keys, "historical native cohort coordinates changed")
    require({key(r) for r in source["rows"]} == expected_keys, "source native cohort coordinates changed")
    for row in source["rows"]:
        other = old_by_key[key(row)]
        theta, i, fine_angle, physical_target = ANCHORS[row["anchor_ray"]]
        require(F(row["physical_G_angle_mod_one"]) == theta and row["anchor_W_tile"] == i,
                "authenticated anchor coordinate changed")
        require(row["fine_Pi9"] == fine_angle and row["physical_K9_target"] == physical_target,
                "authenticated anchor target changed")
        require(row["source_V_parent"] == row["source_W_tile"] // 2, "source parent route changed")
        for field in ("anchor_W_tile", "unwrapped_G_angle", "original_ideal_side", "fine_Pi9", "physical_K9_target"):
            require(row[field] == other[field], f"historical source mismatch: {field}")
        require(other["based_F9_defect_word"] is None, "historical null was overwritten")
    atlas = json.loads((repo / SOURCE_ATLAS).read_text())
    stage = next(s for s in atlas["stages"] if s["stage"] == "G")
    tiles = stage["pieces"]["W"]["tiles"]
    require(len(tiles) == 4, "native W tile count changed")
    for j, tile in enumerate(tiles):
        require(tuple(map(F, tile["seam_stage_angles"])) == SEAMS[j], "native seam changed")
        require(F(tile["seam_midpoint_lift"]) == MIDPOINTS[j], "native midpoint changed")
        require(F(tile["basepoint_height_relative_to_initial"]) == HEIGHT, "native base height changed")
        require(F(tile["tile_mark_height_relative_to_initial"]) == F(1, 128), "native tile mark changed")
        require(F(tile["finite_gluing_height_relative_to_initial"]) == F(1, 64), "native glue height changed")
    return source["rows"], old_by_key


def check_structure():
    require(MIDPOINTS == (F(7, 32), F(9, 32), F(23, 32), F(25, 32)), "midpoints")
    alpha, a1, a2 = (a for a, _ in CUTS)
    require(SEAMS[1][0] < alpha < MIDPOINTS[1] < SEAMS[1][1], "root cut location")
    require((8 * alpha) % 1 == F(25, 112), "root cut is not the certified d-ray pullback")
    require(a1 == 2 * F(25, 112) and a2 == 2 * a1, "forward omitted-phase cut ray ladder")
    require(MIDPOINTS[0] < alpha < a1 < a2 < 1, "positive carrier cut order")
    require(all(not (a < a1 < b or a < a2 < b) for a, b in SEAMS), "nonroot cut enters W")
    require(0 < ENDPOINT_HEIGHT < SECOND_HEIGHT < HEIGHT < F(1, 64) < F(1, 32), "physical heights")
    # Exact Cantor endpoints, not floating-point comparisons with an
    # irrational input. The chosen root cut is 0.3(4)^infinity in C.
    c_min, c_max = F(3, 7), F(4, 7)
    c3 = ((3 + c_min) / 8, (3 + c_max) / 8)
    c4 = ((4 + c_min) / 8, (4 + c_max) / 8)
    require(c3 == (F(3, 7), F(25, 56)) and c4 == (F(31, 56), F(4, 7)), "Cantor first cylinders")
    require((4 + c3[1]) / 16 == alpha, "root cut octal authentication")
    require(c3[1] == F(3, 8) + F(4, 64) / (1 - F(1, 8)), "root cut address 3 then all 4")
    require(alpha < MIDPOINTS[1] == F(252, 896) < (4 + c4[0]) / 16 == F(255, 896), "actual A1 gap")
    for i, offset in enumerate(OCTAL_OFFSETS):
        for digit, bounds in ((3, c3), (4, c4)):
            lo, hi = ((offset + c) / 16 for c in bounds)
            require(SEAMS[i][0] < lo <= hi < SEAMS[i][1], "physical Cantor cylinder outside seam")
            require(q_word(lo) == q_word(hi), "transducer cylinder crosses its reference threshold")
            for j in range(4):
                require(address_word(j, i, digit, 0) == formula_word(j, lo, 0) == formula_word(j, hi, 0),
                        "first-octal-symbol transducer disagreement")
    for j in range(4):
        measured = tuple(x["signed_letter"] for x in direct_crossings(MIDPOINTS[0], MIDPOINTS[j]))
        require(measured == P[j], "incorrect baseline calibration")
        turn = tuple(x["signed_letter"] for x in direct_crossings(MIDPOINTS[j], MIDPOINTS[j] + 1))
        require(turn == native_deck_word(j), "incorrect native deck conjugator")
    require(tuple(native_deck_word(j) for j in range(4)) == ((1, 2, 3), (2, 3, 1), (3, 1, 2), (3, 1, 2)), "deck cyclic words")

    # The exhaustive sector cells prove the finite part of the all-integer
    # theorem: on a root sector, Q has no b02 and w01(Q)=parent(i).
    # The arbitrary integer n contributes exactly n to w02 in the formula.
    cells = ((0, SEAMS[0][0], SEAMS[0][1], ()),
             (1, SEAMS[1][0], alpha, ()),
             (1, alpha, SEAMS[1][1], (1,)),
             (2, SEAMS[2][0], SEAMS[2][1], (1, 2)),
             (3, SEAMS[3][0], SEAMS[3][1], (1, 2)))
    for i, lo, hi, q in cells:
        theta = (lo + hi) / 2
        require(q_word(theta) == q, "sector Q word")
        require(not any(lo < a < hi for a, _ in CUTS), "unaccounted cut within a sector cell")
        require(winding(q)[1:3] == [i // 2, 0], "sector transverse charge")
        for j in range(4):
            w = product(inverse(P[j]), q)
            require(in_root_subgroup(w) == (i // 2 == j // 2), "zero-shift parent criterion")
            require(winding(w)[1:3] == [i // 2 - j // 2, 0], "signed transverse charge")

    # The unique cut angle is not deleted. Cancel its prescribed common
    # terminal W1 segment, leaving a lower-angle bank endpoint with no cut tie.
    epsilon = (alpha - SEAMS[1][0]) / 8
    surrogate = alpha - epsilon
    for j in range(4):
        require(q_word(alpha) == q_word(surrogate), "root-cut lower-angle bank gauge")
        for n in (-1, 0, 1):
            measured = tuple(x["signed_letter"] for x in direct_crossings(MIDPOINTS[j], surrogate + n))
            require(reduce_word(measured) == formula_word(j, alpha, n), "root-cut endpoint cancellation")
    return cells


def build_manifest(repo):
    check_structure()
    source_rows, old_by_key = schema_source_rows(repo)
    out = []
    counts = Counter()
    zero_count = Counter()
    for row in source_rows:
        j = row["source_W_tile"]
        i = row["anchor_W_tile"]
        n = row["native_integer_shift"]
        end = F(row["unwrapped_G_angle"])
        theta = F(row["physical_G_angle_mod_one"])
        c_coordinate = 16 * theta - OCTAL_OFFSETS[i]
        first_octal_digit = (8 * c_coordinate).__floor__()
        require(end == theta + n, "source unwrapped coordinate changed")
        require(SEAMS[i][0] < theta < SEAMS[i][1], "anchor outside original seam")
        require(not (SEAMS[j][0] <= end <= SEAMS[j][1]), "row is not a strict native J side")
        require(row["original_ideal_side"] == ("xi" if end < SEAMS[j][0] else "eta"), "source side changed")
        first = direct_crossings(MIDPOINTS[j], end)
        # A second representative takes three distinct horizontal legs
        # at a lower height. NOTE.md proves its actual endpoint-fixed
        # homotopy through the KL admissible path space.
        second = second_crossings(j, theta, n)
        w = reduce_word(c["signed_letter"] for c in first)
        require(w == reduce_word(c["signed_letter"] for c in second), "second representative differs")
        require(w == formula_word(j, theta, n), "direct crossings disagree with based formula")
        require(w == address_word(j, i, first_octal_digit, n), "physical octal transducer disagreement")
        require(w == product(power(native_deck_word(j), n), formula_word(j, theta, 0)), "native deck law")
        root = in_root_subgroup(w)
        require(root == (n == 0 and i // 2 == j // 2), "all-sector root criterion")
        prior = old_by_key[(row["anchor_ray"], j, n)]
        expected = prior["conditional_required_F9_root_subgroup_membership"] == "in_H"
        require(root == expected, "NEW WORD DISAGREES WITH HISTORICAL ROOT CLASSIFICATION")
        require(winding(w)[1:3] == [n + i // 2 - j // 2, n], "physical winding formula")
        require(winding(w)[3:] == [0] * 6, "unexpected outside-carrier generator")
        counts["in_H" if root else "outside_H"] += 1
        if n == 0:
            zero_count["in_H" if root else "outside_H"] += 1
        copied = {k: v for k, v in row.items() if k != "based_F9_defect_word"}
        copied.update({
            "source_instance_id": f"{row['anchor_ray']}:W{j}:n{n:+d}",
            "endpoint_height_relative_to_h": str(ENDPOINT_HEIGHT),
            "physical_C_coordinate": str(c_coordinate),
            "first_octal_digit": first_octal_digit,
            "KL_prefix": {"definition": "unique hyperbolic geodesic in D=W minus (K9 union root ray cut) from x to phi(m_j,h/256)", "contained_in_W_minus_K9": True, "required_to_lie_in_Omega3": False},
            "KL_annular_part": {"horizontal_start": str(MIDPOINTS[j]), "horizontal_end": str(end), "horizontal_height_relative_to_h": str(HEIGHT), "terminal_vertical_angle": str(theta)},
            "root_reference": {"definition": "unique hyperbolic geodesic in D from x to phi(theta,h/1024)", "root_cut_endpoint_rule": "lower-angle bank common terminal segment, if theta=249/896"},
            "ordered_signed_physical_crossings": first,
            "second_representative_height_relative_to_h": str(SECOND_HEIGHT),
            "second_representative_unwrapped_horizontal_vertices": [str(MIDPOINTS[j]), str(MIDPOINTS[0]), str(MIDPOINTS[0] + n), str(theta + n)],
            "second_representative_crossings": second,
            "nine_generator_winding": winding(w),
            "based_F9_defect_word_signed": list(w),
            "based_F9_defect_word": names(w),
            "root_subgroup_membership": "in_H" if root else "outside_H",
            "prior_membership_agrees": True,
            "basis_realization": "actual three G-ray cut-dual meridians; any compatible completion by six cuts outside the G carrier",
            "basis_change_on_occurring_generators": {"b00": ["b00"], "b01": ["b01"], "b02": ["b02"]},
        })
        out.append(copied)
    require(counts == {"in_H": 8, "outside_H": 80}, "unexpected 88-row membership totals")
    require(zero_count == {"in_H": 8, "outside_H": 16}, "unexpected zero-shift totals")
    sources = {}
    for p in (SOURCE_WORDS, SOURCE_ROWS, SOURCE_ATLAS):
        sources[str(p)] = hashlib.sha256((repo / p).read_bytes()).hexdigest()
    return {
        "schema_version": 1,
        "scope": "actual ray-cut realization of one compatible physical based F9 gauge; all 88 archived strict J witnesses; theorem for every actual root angle and every integer deck coordinate",
        "status": "written_analytic_physical_construction_with_exact_chart_crossing_certificate",
        "not_claimed": ["numerical or Lean proof of physical straightening and ray landing", "recovery of uniquely archived whiskers (none were specified)", "Omega3-only initial prefixes", "KKL unique proper restriction", "closure of full issue62 or global MLC gates"],
        "source_sha256": sources,
        "gauge": {"basepoint_angle": str(MIDPOINTS[0]), "basepoint_height_relative_to_h": str(HEIGHT), "root_reference_domain": "D=W minus (K9 union root ray at 249/896)", "root_cut_endpoint_bank": "lower_angle", "path_product": "g=kappa_prime * inverse(kappa), in traversal order", "cosets": "left H\\F9 with right monodromy", "basis": list(NAMES), "root_subgroup": "<b00>", "coarse_peripheral": names(BETA)},
        "cuts_within_actual_G_carrier": [{"angle": str(a), "generator": NAMES[k - 1], "physical_landing": ("G^3-preimage of 0 in K9" if k == 1 else "x3 in D01" if k == 2 else "x6 in D02"), "positive_crossing": "increasing unwrapped angle"} for a, k in CUTS],
        "remaining_six_cuts": {"region": "outside the closed G carrier N", "disjoint_completion": "proved in NOTE.md, Section 3", "crossings_by_every_constructed_loop": 0, "word_independent_of_completion": True},
        "baseline_words_P_j": [names(w) for w in P],
        "native_deck_words_D_j": [names(native_deck_word(j)) for j in range(4)],
        "all_integer_formula": "red(P_j^{-1} * (b00*b01*b02)^n * Q(theta))",
        "physical_octal_transducer": {
            "source": "research/independent_audits/issue62_octal_reconstruction_20261123/README.md",
            "exact_domain": "theta=(sum_{k>=1} a_k*8^(-k)+u_i)/16, a_k in {3,4}, u=(3,4,11,12)",
            "required_input": ["source tile j", "physical root seam i", "first octal digit a_1", "unbounded integer n"],
            "remaining_infinite_digits_needed": False,
            "C_first_digit_3_hull": ["3/7", "25/56"],
            "C_first_digit_4_hull": ["31/56", "4/7"],
            "A1_first_digit_3_hull": ["31/112", "249/896"],
            "A1_first_digit_4_hull": ["255/896", "2/7"],
            "A1_gap_with_midpoint": ["249/896", "252/896", "255/896"],
            "root_cut_C_address": "3 followed by 4 forever",
            "Q_table": [{"physical_seam_i": i, "first_octal_digit": digit,
                         "Q_word": names(address_word(0, i, digit, 0))}
                        for i in range(4) for digit in (3, 4)],
            "finite_sheet_quotient_claimed": False,
        },
        "all_integer_winding_formula": {"w01": "n + parent(i) - parent(j)", "w02": "n"},
        "all_integer_root_criterion": "n=0 and parent(i)=parent(j); on strict original J sides this means j is the same-parent mate of i",
        "coarse_only_prefix_obstruction": {
            "common_basepoint_seam": 0,
            "all_Omega3_paths_to_physical_Ai": "delta=p(i); follows from constancy of winding on connected K3",
            "consequence": "no Omega3-only path from this x is root-compatible at any A2 or A3 endpoint",
            "authenticated_native_counterexample_to_extra_requirement": {
                "source": "pL:W3:n+0", "theta": "5/7", "native_word": [],
                "every_Omega3_only_connector_delta": 1,
            },
            "proof": "NOTE.md, Section 8, A concrete impossibility for the extra coarse-only prefix condition",
        },
        "orientation_note": "For the explicit g=kappa_prime*kappa^{-1}, delta=w01-w02=parent(i)-parent(j). The historical C4 source comparison printed the opposite sign; its nonzero/root decisions agree.",
        "counts": {"source_rows": len(out), "in_H": counts["in_H"], "outside_H": counts["outside_H"], "zero_shift_in_H": zero_count["in_H"], "zero_shift_outside_H": zero_count["outside_H"], "nonzero_shift_outside_H": 64, "historical_null_rows_unchanged": 88},
        "rows": out,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=DEFAULT_REPO)
    parser.add_argument("--write", action="store_true", help="write this packet's deterministic certificate")
    parser.add_argument("--check-manifest", action="store_true", help="compare all certificate fields with the existing file")
    args = parser.parse_args()
    require(not (args.write and args.check_manifest), "choose write or check, not both")
    result = build_manifest(args.repo.resolve())
    if args.write:
        MANIFEST.write_text(json.dumps(result, indent=2) + "\n")
    elif args.check_manifest or MANIFEST.exists():
        require(json.loads(MANIFEST.read_text()) == result, "stored physical connector certificate differs")
    print(json.dumps({"status": "PASS", **result["counts"], "native_deck_words": result["native_deck_words_D_j"]}, indent=2))


if __name__ == "__main__":
    main()
