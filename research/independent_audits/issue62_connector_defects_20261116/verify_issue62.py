#!/usr/bin/env python3
"""Issue #62: exact native J-side / W-to-V footprint and free-word audit.

Every rational calculation is exact (fractions.Fraction). This program verifies
the finite original-source data and the algebraic consequences of *stated*
analytic inputs. It does NOT reconstruct an unspecified physical KL connector,
certify a Jordan wake, or prove Caratheodory / Kahn root-chart theorems.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent / "finite_j_side_footprints.json"
BETA0 = (1, 2, 3)  # the archived b00*b01*b02, NOT the fine b00
EXPECTED = (
    ("qR", 0, "3/14", "1/2", "left_tip"),
    ("d", 0, "25/112", "3/4", "zero_lower"),
    ("e", 1, "31/112", "3/4", "zero_lower"),
    ("pR", 1, "2/7", "0", "right_tip"),
    ("pL", 2, "5/7", "0", "right_tip"),
    ("a", 2, "81/112", "1/4", "zero_upper"),
    ("b", 3, "87/112", "1/4", "zero_upper"),
    ("qL", 3, "11/14", "1/2", "left_tip"),
)
SOURCE_W_SEAMS = (
    ("41/192", "43/192"),
    ("53/192", "55/192"),
    ("137/192", "139/192"),
    ("149/192", "151/192"),
)
SOURCE_V_SEAMS = (("5/24", "7/24"), ("17/24", "19/24"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def load(relative_path: str):
    return json.loads((ROOT / relative_path).read_text(encoding="utf-8"))


def rat(value: str) -> Fraction:
    return Fraction(value)


def interval(tile):
    return tuple(map(rat, tile["seam_stage_angles"]))


def remaining_side(tile, angle: Fraction) -> str:
    lo, hi = interval(tile)
    return "xi" if angle < lo else "eta" if angle > hi else "open_seam_or_vertex"


def w_to_v_type(tile, parent, angle: Fraction) -> str:
    side = remaining_side(tile, angle)
    lo, hi = interval(parent)
    if side == "xi":
        return "V_boundary_proper_tail" if angle <= lo else "V_interior_collapse"
    if side == "eta":
        return "V_boundary_proper_tail" if angle >= hi else "V_interior_collapse"
    raise AssertionError("not a strict finite J-side point")


def prove_all_sector_inequalities(tiles, parents) -> None:
    """Strict rational endpoint chains imply the stated result for ALL theta in I_i.

    This proves interval implications, not which physical rays land on K9.
    No finite sampling and no supposition E_i has nonempty interior is used.
    """
    for p in range(2):
        left, right = interval(parents[p])
        a0, b0 = interval(tiles[2 * p])
        a1, b1 = interval(tiles[2 * p + 1])
        require(
            Fraction(0) < left < a0 < b0 < a1 < b1 < right < Fraction(1),
            f"original KL ordered W/V sector chain failed for parent {p}",
        )
    require(interval(parents[0])[1] < interval(parents[1])[0],
            "original two V parent sectors overlap")
    for i, tile in enumerate(tiles):
        a, b = interval(tile)
        require(0 < a < b < 1, f"not a strict 0-1 seam: {i}")
        for j, other in enumerate(tiles):
            lo, hi = interval(other)
            vl, vu = interval(parents[j // 2])
            if j == i:
                require((a, b) == (lo, hi), "own gluing seam mismatch")
            elif j // 2 == i // 2:
                if i % 2 == 0:
                    require(vl < a < b < lo,
                            "entire even->odd mate sector must be xi collapse")
                else:
                    require(hi < a < b < vu,
                            "entire odd->even mate sector must be eta collapse")
            elif i // 2 == 0:
                require(b < vl < lo, "opposite parent xi must be V proper tail")
            else:
                require(hi < vu < a, "opposite parent eta must be V proper tail")
            # For EVERY theta in (a,b): theta-1 < 0 < vl and
            # theta+1 > 1 > vu. Both integer-shift tails are V-proper.
            require(a - 1 < b - 1 < 0 < vl and
                    vu < 1 < a + 1 < b + 1,
                    "unit-deck native V-tail separation")
    # This is enough for any integer n<=-1 or n>=1 by monotonicity.


def source_inputs():
    atlas = load("results/tip_kl_side_atlas.json")
    source = load("results/tip_rooted_native_KL_section_20261108.json")
    native_deck = load("results/tip_native_root_deck_monodromy_20261109.json")
    wake = load("results/tip_native_C4_wake_root_matrix_20261109.json")
    trichotomy = load("results/tip_native_finite_J_side_trichotomy_20261109.json")
    full_circle = load("results/tip_native_full_W_ideal_circle_types_20261109.json")
    proper = load("results/tip_native_two_proper_restrictions_20261109.json")
    ray_ladder = load("results/tip_nested_full_ray_census_20261107.json")[
        "actual_Levin_3_to_9_ladder"
    ]
    phase = load("results/tip_root_interval_geometry.json")
    require(atlas["source_boundary_identity"] ==
            "partial^v_i Psi(Y) = eta_i union xi_(i+1)",
            "changed KL native eta/xi incidence")
    stage = next(s for s in atlas["stages"] if s["stage"] == "G")
    W, V = stage["pieces"]["W"], stage["pieces"]["V0"]
    tiles, parents = W["tiles"], V["tiles"]
    require(W["depth"] == 6 and V["depth"] == 3 and
            len(tiles) == 4 and len(parents) == 2,
            "wrong original G=f^3 source stages")
    for j, t in enumerate(tiles):
        require(t["id"] == f"G:W:tile{j}" and
                t["seam_stage_angles"] == list(SOURCE_W_SEAMS[j]),
                f"changed original W tile {j}")
        require(t["xi"]["inner_halfline"][1] == SOURCE_W_SEAMS[j][0]
                and t["eta"]["inner_halfline"][0] == SOURCE_W_SEAMS[j][1],
                f"changed original finite xi/eta half-lines {j}")
        require("not a remaining ideal J side" in t["central_seam_warning"],
                "original KL open seam was silently treated as J side")
    for p, t in enumerate(parents):
        require(t["seam_stage_angles"] == list(SOURCE_V_SEAMS[p]),
                "changed original V parent seam")
    routes = stage["inclusions"]["W_into_V0"]["tile_routes"]
    require(sorted((r["source_tile"], r["target_tile"],
                    r["angular_integer_shift"]) for r in routes) ==
            [(f"G:W:tile{i}", f"G:V0:tile{i // 2}", 0)
             for i in range(4)], "not the actual zero-shift KL W->V immersion")
    prove_all_sector_inequalities(tiles, parents)

    cuts = proper["source_W_child_original_side_cuts"]
    require(len(cuts) == 4, "missing original PR67 proper-tail source cuts")
    for j, c in enumerate(cuts):
        p = j // 2
        require(c["W_tile"] == j and c["V_parent_tile"] == p and
                c["source_W_seam"] == list(SOURCE_W_SEAMS[j]) and
                c["target_V_seam"] == list(SOURCE_V_SEAMS[p]) and
                c["zero_based_angular_shift"] == 0, "W->V source tail drift")
        require(c["xi_interior_collapse_interval"] ==
                [SOURCE_V_SEAMS[p][0], SOURCE_W_SEAMS[j][0]],
                "actual xi collapse gap mismatch")
        require(c["eta_interior_collapse_interval"] ==
                [SOURCE_W_SEAMS[j][1], SOURCE_V_SEAMS[p][1]],
                "actual eta collapse gap mismatch")

    require(full_circle["original_source_ideal_arc_counts"]["J_xi_eta"] == 8
            and full_circle["original_source_ideal_arc_counts"]["O_lambda"] == 4
            and len(full_circle["source_wrapping_joints"]) == 8
            and len(full_circle["source_vertex_incidence"]) == 4,
            "original KL whole ideal circle arc types changed")
    require(phase["inner_root_exact_interval"] == "[x9,x18]" and
            phase["phase_intervals_pairwise_disjoint"],
            "fine physical interval hypothesis unavailable")
    phases = {p["physical_phase"]: p for p in phase["phase_intervals"]}
    require(set(phases) == set(range(9)), "not nine physical fine intervals")

    def low(k):
        e = phases[k]["left_endpoint_enclosure"]
        return Fraction(e["lower_numerator"], 2 ** e["denominator_power_of_two"])

    def high(k):
        e = phases[k]["right_endpoint_enclosure"]
        return Fraction(e["upper_numerator"], 2 ** e["denominator_power_of_two"])

    require(high(6) < low(0) < high(0) < low(3),
            "fine phase D02 < D00 < D01 separation failed")
    require(all(phases[k]["coarse_phase"] == 0 for k in (0, 3, 6)),
            "wrong coarse root phase grouping")

    rows = sorted(source["actual_source_G_KL_atlas"]["angle_rows"],
                  key=lambda row: (row["W_tile"], row["slot"]))
    prior = sorted(native_deck["anchor_rows"],
                   key=lambda row: (row["tile"], row["slot"]))
    require(len(rows) == len(prior) == len(EXPECTED) == 8,
            "eight source-authenticated G ray anchors changed")
    lookup = {(r["ray"], r["other_tile"]): r for r in wake["root_ray_tile_cases"]}
    require(len(lookup) == 32, "missing PR64 original 8x4 source wake cohort")
    for k, (row, auth) in enumerate(zip(rows, prior)):
        name, i, theta, fine, landing = EXPECTED[k]
        require((row["name"], row["W_tile"], row["Pi3"],
                 row["Pi9"], row["physical_K9_target"]) ==
                (name, i, theta, fine, landing),
                f"actual original ray {name} failed exact reference lock")
        require((auth["ray"], auth["tile"], auth["slot"],
                 auth["anchor_G_angle"], auth["fine_Pi9"],
                 auth["physical_K9_target"]) ==
                (name, i, row["slot"], theta, fine, landing),
                f"PR63 native deck mismatch at {name}")
        require(ray_ladder["Pi3_outer_internal"][name] == theta and
                ray_ladder["Pi9_inner_internal"][name] == fine,
                f"independent Levin exact angle mismatch at {name}")
        require(interval(tiles[i])[0] < rat(theta) < interval(tiles[i])[1],
                f"anchor not strictly in open KL seam: {name}")
        for j in range(4):
            case = lookup[(name, j)]
            require(case["anchor_tile"] == i and
                    case["G_angle"] == theta and
                    case["Pi9"] == fine and
                    case["physical_K9_target"] == landing,
                    f"PR64 physical source-root matrix changed for {name},{j}")
            require(case["root_sheet_transverse_delta"] == j // 2 - i // 2,
                    f"PR64 transverse wake charge mismatch for {name},{j}")
            require(case["zero_deck_root_compatible"] == (i // 2 == j // 2),
                    f"PR64 zero-deck rootedness mismatch for {name},{j}")
    return tiles, parents, rows, trichotomy, lookup


def proof_role(i: int, j: int, n: int) -> str:
    same_parent = i // 2 == j // 2
    if n == 0 and same_parent:
        require(j == i ^ 1, "the own seam is not an ideal J point")
        return "mate_naturality_root"
    if n == 0:
        return "opposite_parent_wake_nonroot"
    if same_parent:
        return "native_deck_winding_nonroot"
    return "opposite_parent_wake_and_deck_nonroot"


def compute_manifest(tiles, parents, rays, trichotomy, wake_lookup):
    rows = []
    excluded_seams = 0
    for source_ray in rays:
        i = source_ray["W_tile"]
        theta = rat(source_ray["Pi3"])
        for j, tile in enumerate(tiles):
            for n in (-1, 0, 1):
                x = theta + n
                side = remaining_side(tile, x)
                if side == "open_seam_or_vertex":
                    require(i == j and n == 0,
                            "unanticipated source vertex or seam")
                    excluded_seams += 1
                    continue
                vclass = w_to_v_type(tile, parents[j // 2], x)
                rooted = n == 0 and j == (i ^ 1)
                require(vclass == ("V_interior_collapse" if rooted
                                   else "V_boundary_proper_tail"),
                        f"native J-side / KL W-to-V footprint contradiction {i,j,n}")
                row = {
                    "anchor_ray": source_ray["name"],
                    "anchor_W_tile": i,
                    "source_W_tile": j,
                    "native_integer_shift": n,
                    "original_ideal_side": side,
                    "unwrapped_G_angle": str(x),
                    "physical_G_angle_mod_one": str(theta),
                    "source_V_parent": j // 2,
                    "fine_Pi9": source_ray["Pi9"],
                    "physical_K9_target": source_ray["physical_K9_target"],
                    "fine_sheet_footprint": (
                        "marked_root" if rooted else "proper_nonroot"
                    ),
                    "KL_W_to_V_boundary_footprint": vclass,
                    "proof_role": proof_role(i, j, n),
                    # No individual full F9 defect is inferred from the angles.
                    "based_F9_defect_word": None,
                }
                rows.append(row)
                if n == 0:
                    case = wake_lookup[(source_ray["name"], j)]
                    require(case["source_side_at_zero_deck"] == side,
                            "PR64 authentic J-side type mismatch")
                    require(case["zero_deck_root_compatible"] == rooted,
                            "PR64 native finite J root result mismatch")
    require(excluded_seams == 8 and len(rows) == 88,
            "88 strict J-side / 8 genuine open seam census failed")
    require(len({(r["source_W_tile"], r["unwrapped_G_angle"]) for r in rows}) ==
            88, "distinct original finite KL J prime-end names collided")
    rooted_rows = [r for r in rows if r["fine_sheet_footprint"] == "marked_root"]
    nonroot_rows = [r for r in rows if r["fine_sheet_footprint"] == "proper_nonroot"]
    interior = [r for r in rows if
                r["KL_W_to_V_boundary_footprint"] == "V_interior_collapse"]
    proper_tail = [r for r in rows if
                   r["KL_W_to_V_boundary_footprint"] == "V_boundary_proper_tail"]
    require((len(rooted_rows), len(nonroot_rows), len(interior),
             len(proper_tail)) == (8, 80, 8, 80),
            "dual source/fine J-side footprint counts changed")
    require({id(r) for r in rooted_rows} == {id(r) for r in interior} and
            {id(r) for r in nonroot_rows} == {id(r) for r in proper_tail},
            "the original source V-proper tails must be fine nonroot in cohort")

    prior_root = trichotomy["sample_exact_witnesses"]["marked_fine_root"]
    require({(r["ray"], r["source_W_tile"], r["original_ideal_side"],
              r["unwrapped_G_angle"]) for r in rooted_rows} ==
            {(r["ray"], r["source_W_tile"], r["ideal_side"], r["G_angle"])
             for r in prior_root},
            "positive finite mate J-side witnesses changed")
    removed = trichotomy["sample_exact_witnesses"]["removed_fine_target"]
    exterior = trichotomy["sample_exact_witnesses"]["ordinary_fine_exterior"]
    require(len(removed) == 16 and len(exterior) == 8,
            "other two original target classes were silently lost")
    require({r["physical_target"] for r in removed} == {"x3", "x6"} and
            {r["physical_target"] for r in exterior} == {"a"},
            "excluded-phase / ordinary-exterior targets confused with K9")
    require({rat(r["angle_mod_one"]) for r in removed + exterior}.isdisjoint(
            {rat(r["physical_G_angle_mod_one"]) for r in rows}),
            "an original removed/exterior angle was called a root angle")
    return {
        "schema_version": 1,
        "scope": "88 finite exact J-side witnesses from 8 authenticated root rays, all 4 original W tiles, n=-1,0,1; not the whole E_i landing set",
        "ideal_domain": "E_i={theta in original open W seam I_i: actual G ray landing(theta) in K9}; finite J_j={theta+n outside original j seam: theta in union E_i, n integer}",
        "counts": {
            "excluded_open_gluing_seam_at_zero_deck": 8,
            "strict_finite_J_witnesses": 88,
            "marked_fine_root": 8,
            "proper_fine_nonroot": 80,
            "W_to_V_interior_collapse": 8,
            "W_to_V_boundary_proper_tail": 80,
        },
        "full_KL_prescribed_based_F9_words": None,
        "words_gate": "OPEN: require original KL path class, base whiskers, fine W-root connector, geometric nine-cut intersections and basis change",
        "rows": rows,
    }


def reduce_word(word):
    stack = []
    for letter in word:
        require(type(letter) is int and 1 <= abs(letter) <= 9,
                f"invalid F9 signed letter {letter!r}")
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def inverse(word):
    return tuple(-g for g in reversed(word))


def beta_power(n: int):
    return BETA0 * n if n >= 0 else inverse(BETA0) * (-n)


def wind(word, j):
    return sum(1 if g == j else -1 if g == -j else 0 for g in word)


def root_subgroup(word):
    return all(abs(letter) == 1 for letter in reduce_word(word))


def same_left_coset(x, y):
    return root_subgroup(tuple(x) + inverse(y))


def select_root_shift(g):
    g = reduce_word(g)
    n = -wind(g, 2)
    return n if root_subgroup(beta_power(n) + g) else None


def all_reduced_F9_words(max_length=3):
    yield ()
    letters = tuple(range(-9, 0)) + tuple(range(1, 10))
    for length in range(1, max_length + 1):
        for w in product(letters, repeat=length):
            if all(x != -y for x, y in zip(w, w[1:])):
                yield w


def verify_nonabelian_based_prefix() -> int:
    """Checks F9 prefix algebra, not a made-up word of a physical KL path."""
    require(BETA0 == (1, 2, 3) and BETA0 != (1,),
            "coarse beta0 was collapsed to fine b00")
    require(reduce_word(BETA0 + inverse(BETA0)) == (),
            "free reduction of coarse meridian inverse failed")
    require(not root_subgroup(BETA0), "coarse beta0 is not a fine meridian")
    commutator = (2, 3, -2, -3)
    require(all(wind(commutator, j) == 0 for j in range(1, 10))
            and not root_subgroup(commutator)
            and select_root_shift(commutator) is None,
            "a zero-homology nonroot commutator was erased")
    require(reduce_word(BETA0 + (4,)) != reduce_word((4,) + BETA0),
            "wrong noncommutative left prefix / right append order")
    require(select_root_shift(inverse(BETA0) + (1, 1)) == 1,
            "exact positive root-shift control failed")
    require(select_root_shift(inverse(BETA0) + (4,)) is None,
            "a nonroot word was falsely selected by winding")
    checked = 0
    for g in all_reduced_F9_words(3):
        candidate = select_root_shift(g)
        actual = [n for n in range(-5, 6)
                  if root_subgroup(beta_power(n) + g)]
        require(actual == ([] if candidate is None else [candidate]),
                f"F9 root selector mismatch: {g!r}")
        for a in (-2, -1, 0, 1, 2):
            require(wind(beta_power(a) + g, 2) == a + wind(g, 2) and
                    wind(beta_power(a) + g, 3) == a + wind(g, 3),
                    "based prefix beta0 full phase winding failed")
            for b in (-2, -1, 0, 1, 2):
                require(reduce_word(beta_power(a) + beta_power(b) + g) ==
                        reduce_word(beta_power(a + b) + g),
                        "nonabelian based-prefix composition failed")
                require(same_left_coset(beta_power(a) + g, beta_power(b) + g)
                        == (a == b),
                        "distinct based prefix shifts were collapsed in H\\F9")
        checked += 1
    require(checked == 5527, f"wrong nine-generator word sample {checked}")
    # The for-all-n proof is topological / integer winding, not extrapolated
    # from the finite 5x5 tests: w01(beta0^(n-m))=n-m, zero on H.
    return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check-manifest", action="store_true")
    mode.add_argument("--write-manifest", action="store_true")
    opts = parser.parse_args()
    source = source_inputs()
    computed = compute_manifest(*source)
    checked_words = verify_nonabelian_based_prefix()
    if opts.write_manifest:
        OUT.write_text(json.dumps(computed, indent=2, sort_keys=True) + "\n",
                       encoding="utf-8")
        print(f"WROTE {OUT}")
    elif opts.check_manifest:
        require(json.loads(OUT.read_text(encoding="utf-8")) == computed,
                "the exact 88-row manifest drifted from the source")
        print("PASS: all-sector rational implications; 88 strict J-side rows; "
              "8 V-interior rooted / 80 V-proper nonroot; "
              f"{checked_words} reduced F9 selector controls")
    else:
        print(json.dumps(computed, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
