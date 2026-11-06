#!/usr/bin/env python3
"""Exact ambient alpha-ray pullbacks through puzzle depth six at the tip.

The accompanying written slit-lifting proof supplies the landing interpretation.
This program verifies rational angles, inverse-branch choices, complete fibers,
cyclic order and the critical faces. It does not prove complex analysis or assign
the separate localization O/xi/eta markings.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

from verify_tip_ray_portrait import LOWER, UPPER, doubled, linked

Pair = tuple[F, F]
ALPHA: Pair = (F(1, 3), F(2, 3))
MAX_DEPTH = 6


def pair_id(pair: Pair) -> str:
    return ",".join(str(theta) for theta in pair)


def lift_angle(theta: F, branch: int, cut: F) -> F:
    """Select the unique preimage in the specified *open* angular semicircle.

    Branch 0 is (cut, cut+1/2), branch 1 its circular complement.
    Cut endpoints are excluded, never assigned to either branch by convention.
    """
    assert branch in (0, 1) and 0 < cut < F(1, 2)
    candidates = (theta / 2, (theta + 1) / 2)
    assert all(t not in (cut, cut + F(1, 2)) for t in candidates)
    selected = [t for t in candidates
                if (cut < t < cut + F(1, 2)) == (branch == 0)]
    assert len(selected) == 1
    return selected[0]


def lift_pair(pair: Pair, branch: int, cut: F) -> Pair:
    return tuple(sorted(lift_angle(t, branch, cut) for t in pair))


def critical_face(pairs: dict[Pair, str], critical_rays: tuple[F, ...]) -> list[Pair]:
    """Boundary chords of the face containing all four critical-point accesses.

    Cut the angle circle at one critical access. For each vertex chord the open
    interval away from this cut is the side not containing 0. The maximal such
    intervals are precisely the boundary chords of the critical face.
    """
    anchor = critical_rays[0]
    excluded = []
    for pair in pairs:
        a, b = sorted((t - anchor) % 1 for t in pair)
        assert 0 < a < b < 1
        assert all(not a < (t - anchor) % 1 < b for t in critical_rays)
        excluded.append((a, b, pair))
    maximal = [item for item in excluded if not any(
        other[0] <= item[0] and item[1] <= other[1] and item != other
        for other in excluded
    )]
    return [item[2] for item in sorted(maximal)]


def generate_tree(tau: F, max_depth: int = MAX_DEPTH) -> list[dict]:
    assert 0 < tau < F(1, 2)
    cut = tau / 2
    critical_rays = tuple(sorted((cut, (1 - tau) / 2,
                                 cut + F(1, 2), (2 - tau) / 2)))
    pairs: dict[Pair, str] = {ALPHA: ""}
    first_depth: dict[Pair, int] = {}
    levels = []
    for depth in range(max_depth + 1):
        assert len(pairs) == 2**depth
        angles = sorted(t for pair in pairs for t in pair)
        # Independent closed-form enumeration of the entire inverse ray set.
        expected_angles = sorted(
            (base + j) / 2**depth
            for base in ALPHA for j in range(2**depth)
        )
        assert angles == expected_angles
        assert len(set(angles)) == 2**(depth + 1)
        assert all(not linked(a, b) for a, b in combinations(pairs, 2))
        assert all(tuple(sorted((1 - t) % 1 for t in pair)) in pairs
                   for pair in pairs)
        if depth:
            assert all(tuple(sorted((t + F(1, 2)) % 1 for t in pair)) in pairs
                       for pair in pairs)
        face = critical_face(pairs, critical_rays)
        records = []
        for pair, word in sorted(pairs.items()):
            first_depth.setdefault(pair, depth)
            parent = tuple(sorted(doubled(t, 1) for t in pair))
            assert depth == 0 or parent in previous_pairs
            assert tuple(sorted(doubled(t, depth) for t in pair)) == ALPHA
            # Follow the branch word from alpha, innermost (rightmost) first.
            reconstructed = ALPHA
            for bit in reversed(word):
                reconstructed = lift_pair(reconstructed, int(bit), cut)
            assert reconstructed == pair
            records.append({
                "id": pair_id(pair),
                "angles": [str(t) for t in pair],
                "landing_target": "alpha" if not word else f"b_{word}(alpha)",
                "inverse_branch_word": word,
                "first_depth": first_depth[pair],
                "steps_to_fixed_alpha": first_depth[pair],
                "eventual_point_period": 1,
                "eventual_ray_period": 2,
                "image_pair": pair_id(parent),
                "ambient_prime_ends": [str(t) for t in pair],
                "ccw_sector_endpoints": [[str(pair[0]), str(pair[1])],
                                         [str(pair[1]), str(pair[0])]],
                "on_critical_piece": pair in face,
                "localization_O_xi_eta": None,
            })
        levels.append({
            "puzzle_depth": depth,
            "equipotential_height_relative_to_base": str(F(1, 2**depth)),
            "vertex_count": len(pairs),
            "ray_count": len(angles),
            "new_vertices": sum(row["first_depth"] == depth for row in records),
            "cyclic_ray_order": [str(t) for t in angles],
            "critical_piece_boundary_pairs": [pair_id(pair) for pair in face],
            "vertices": records,
        })
        previous_pairs = pairs
        pairs = {}
        for parent, word in previous_pairs.items():
            for branch in (0, 1):
                pair = lift_pair(parent, branch, cut)
                assert pair not in pairs
                pairs[pair] = str(branch) + word
    return levels


def certify() -> dict:
    assert LOWER + UPPER == 1
    tree = generate_tree(LOWER)
    assert [x["vertex_count"] for x in tree] == [1, 2, 4, 8, 16, 32, 64]
    assert [x["new_vertices"] for x in tree] == [1, 1, 2, 4, 8, 16, 32]
    expected_top = ["7/24,17/24", "5/24,19/24"]
    expected_child = ["43/192,53/192", "55/192,137/192",
                      "139/192,149/192", "41/192,151/192"]
    assert tree[3]["critical_piece_boundary_pairs"] == expected_top
    assert tree[6]["critical_piece_boundary_pairs"] == expected_child
    top_angles = {F(t) for pair in expected_top for t in pair.split(",")}
    child_angles = {F(t) for pair in expected_child for t in pair.split(",")}
    assert top_angles.isdisjoint(child_angles)
    assert {doubled(t, 3) for t in child_angles} == top_angles
    assert all(sum(doubled(t, 3) == target for t in child_angles) == 2
               for target in top_angles)
    # Regression against the complete previously named depth-three vertices.
    assert {row["id"] for row in tree[3]["vertices"]} == {
        "1/3,2/3", "1/6,5/6", "1/12,11/12", "5/12,7/12",
        "1/24,23/24", "5/24,19/24", "7/24,17/24", "11/24,13/24",
    }
    # The first genuinely nonreal vertices are conjugate but NOT individually
    # conjugation-invariant pairs. This detects the erroneous rule of pairing
    # every angle with 1-angle at all depths.
    nonreal4 = [row["id"] for row in tree[4]["vertices"]
                if sum(F(t) for t in row["angles"]) != 1]
    assert nonreal4 == ["11/48,13/48", "35/48,37/48"]
    return {
        "status": "EXACT_TIP_ALPHA_RAY_TREE_DEPTH6_PASS",
        "parameter": "c_tip: exact root and bracket in period27_misiurewicz_tip.json",
        "critical_value_cut_ray": str(LOWER),
        "cut_preimage_rays": [str(LOWER / 2), str((LOWER + 1) / 2)],
        "alpha_seed": [str(t) for t in ALPHA],
        "branch_0": "open counterclockwise semicircle (tau/2,(tau+1)/2)",
        "branch_1": "complementary open semicircle",
        "word_convention": "b_i1...ik = b_i1 composed with ... composed with b_ik",
        "maximum_puzzle_depth": MAX_DEPTH,
        "levels": tree,
        "first_nonreal_depth4_pairs": nonreal4,
        "top_child_boundary_ray_intersection": [],
        "top_child_return_time": 3,
        "analytic_dependencies": [
            "certified tip critical-value ray landing (Zakeri Theorems 3.1/3.3)",
            "ambient alpha rays 1/3,2/3 from the existing KL top-puzzle audit",
            "slit-plane inverse-branch landing proof in accompanying audit",
            "KL Decorations section 2.1 puzzle topology; not checked by Python",
        ],
        "scope": "Complete finite ambient alpha-ray tree and cyclic side data through depth6; O/xi/eta and localization naturality are not assigned",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-manifest", action="store_true")
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()
    report = certify()
    encoded = json.dumps(report, sort_keys=True, indent=2) + "\n"
    if args.check_manifest:
        manifest = Path(__file__).resolve().parents[2] / "results" / "tip_puzzle_ray_tree.json"
        assert manifest.read_text(encoding="utf-8") == encoded, "manifest differs"
    print(encoded if args.print_json else report["status"],
          end="" if args.print_json else "\n")


if __name__ == "__main__":
    main()
