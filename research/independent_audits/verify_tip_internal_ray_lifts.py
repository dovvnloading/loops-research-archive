#!/usr/bin/env python3
"""Exact ambient lifts of the G=f^3 internal alpha puzzle through depth six.

Analytic eligibility, landing, polynomial-like germ equality and Levin's map
are proved/imported in the companion notes. This checks the finite rational
selection and the uniquely forced monotone correspondence, not those theorems.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

from verify_tip_puzzle_ray_tree import (
    ALPHA, MAX_DEPTH, Pair, critical_face, generate_tree, lift_pair, pair_id,
)
from verify_tip_ray_portrait import LOWER, UPPER, doubled, linked
from verify_tip_levin_transport import certify as levin_finite_certificate

G_ALPHA: Pair = (F(2, 9), F(7, 9))
CUT = LOWER / 2
CRITICAL_RAYS = tuple(sorted((LOWER / 2, UPPER / 2,
                             (LOWER + 1) / 2, (UPPER + 1) / 2)))


def first_child_excluded_arcs() -> list[tuple[F, F]]:
    ambient = generate_tree(LOWER)
    return [tuple(sorted((F(t) - CUT) % 1 for t in pair.split(",")))
            for pair in ambient[6]["critical_piece_boundary_pairs"]]


def in_first_child(theta: F, excluded: list[tuple[F, F]]) -> bool:
    value = (theta - CUT) % 1
    # Strict: these selected rays cannot land at a boundary alpha-preimage.
    return all(not a <= value <= b for a, b in excluded)


def central_g_preimages(pair: Pair, word: str,
                        excluded: list[tuple[F, F]]) -> dict[Pair, str]:
    children = {pair: word}
    for _ in range(3):
        children = {lift_pair(parent, branch, CUT): str(branch) + parent_word
                    for parent, parent_word in children.items()
                    for branch in (0, 1)}
    assert len(children) == 8
    # Landing cannot be on the first-child boundary. Thus a vertex's two rays
    # lie in the same face, which is checked independently for every child.
    assert all(in_first_child(pair[0], excluded) == in_first_child(pair[1], excluded)
               for pair in children)
    selected = {pair: address for pair, address in children.items()
                if all(in_first_child(t, excluded) for t in pair)}
    assert len(selected) == 2
    return selected


def certify() -> dict:
    levin = levin_finite_certificate()
    known = {F(a): F(t) for a, t in levin["period3_internal_angles"].items()}
    excluded = first_child_excluded_arcs()
    assert all(in_first_child(t, excluded) and in_first_child(doubled(t, 3), excluded)
               for t in G_ALPHA)
    assert tuple(sorted(doubled(t, 3) for t in G_ALPHA)) == G_ALPHA
    # The source-defined Pi3 is degree-one monotone. These enclosing pairs
    # force the two period-at-most-two internal angles without a tuning guess.
    candidate_internal = [F(0), F(1, 3), F(2, 3)]
    seed_mapping = {}
    for ambient, left, right in ((F(2, 9), F(110, 511), F(114, 511)),
                                 (F(7, 9), F(397, 511), F(401, 511))):
        assert left < ambient < right
        candidates = [t for t in candidate_internal if known[left] <= t <= known[right]]
        assert len(candidates) == 1
        seed_mapping[ambient] = candidates[0]
    assert seed_mapping == {F(2, 9): F(2, 3), F(7, 9): F(1, 3)}
    # All rational rays at this physical period-three point have exact ray
    # period six (Milnor Lemma 18.3). The four possible angles in the central
    # child over two G iterates leave exactly the seed after period exclusion.
    candidate_ambient = [F(k, 63) for k in range(1, 63)
                         if in_first_child(F(k, 63), excluded)
                         and in_first_child(doubled(F(k, 63), 3), excluded)]
    assert candidate_ambient == [F(2, 9), F(2, 7), F(5, 7), F(7, 9)]
    exact_period_six = [t for t in candidate_ambient
                        if all(doubled(t, j) != t for j in range(1, 6))]
    assert exact_period_six == list(G_ALPHA)

    levels = []
    pairs: dict[Pair, str] = {G_ALPHA: ""}
    first_depth: dict[Pair, int] = {}
    previous_mapping: dict[F, F] = {}
    for depth in range(MAX_DEPTH + 1):
        assert len(pairs) == 2**depth
        ambient_angles = sorted(t for pair in pairs for t in pair)
        internal_angles = sorted((a + j) / 2**depth
                                 for a in ALPHA for j in range(2**depth))
        assert len(set(ambient_angles)) == len(internal_angles) == 2**(depth + 1)
        assert all(not linked(a, b) for a, b in combinations(pairs, 2))
        # A cyclic-order-preserving bijection of these finite ordered sets is
        # fixed by one anchor; the second anchor and all dynamics are checks.
        offset = (internal_angles.index(F(2, 3))
                  - ambient_angles.index(F(2, 9))) % len(ambient_angles)
        mapping = {a: internal_angles[(i + offset) % len(internal_angles)]
                   for i, a in enumerate(ambient_angles)}
        assert mapping[F(7, 9)] == F(1, 3)
        if depth:
            assert all(doubled(t, 1) == previous_mapping[doubled(a, 3)]
                       for a, t in mapping.items())
            assert all(mapping[a] == t for a, t in previous_mapping.items())
        internal_pairs = {tuple(sorted(mapping[t] for t in pair)) for pair in pairs}
        assert len(internal_pairs) == len(pairs)
        assert all(not linked(a, b) for a, b in combinations(internal_pairs, 2))
        face = critical_face(pairs, CRITICAL_RAYS)
        rows = []
        for pair, word in sorted(pairs.items()):
            first_depth.setdefault(pair, depth)
            parent = tuple(sorted(doubled(t, 3) for t in pair))
            assert depth == 0 or parent in previous_pairs
            reconstructed = G_ALPHA
            for bit in reversed(word):
                reconstructed = lift_pair(reconstructed, int(bit), CUT)
            assert reconstructed == pair
            rows.append({
                "id": pair_id(pair),
                "ambient_angles": [str(t) for t in pair],
                "corresponding_internal_angles": [str(mapping[t]) for t in pair],
                "internal_pair": pair_id(tuple(sorted(mapping[t] for t in pair))),
                "ambient_prime_ends": [str(t) for t in pair],
                "corresponding_internal_prime_ends": [str(mapping[t]) for t in pair],
                "ccw_ambient_sector_endpoints": [
                    [str(pair[0]), str(pair[1])], [str(pair[1]), str(pair[0])]],
                "landing_target": "alpha_G" if not word else f"b_{word}(alpha_G)",
                "ambient_f_inverse_word": word,
                "first_G_depth": first_depth[pair],
                "G_steps_to_alpha_G": first_depth[pair],
                "f_steps_to_alpha_G": 3 * first_depth[pair],
                "G_image_pair": pair_id(parent),
                "eventual_G_point_period": 1,
                "eventual_f_point_period": 3,
                "eventual_internal_ray_period": 2,
                "eventual_ambient_ray_period": 6,
                "on_internal_critical_piece": pair in face,
                "localization_O_xi_eta": None,
            })
        levels.append({
            "G_puzzle_depth": depth,
            "ambient_inverse_time_from_alpha_G": 3 * depth,
            "vertex_count": len(pairs),
            "ray_count": len(ambient_angles),
            "ambient_cyclic_ray_order": [str(t) for t in ambient_angles],
            "internal_cyclic_order_starting_at_first_ambient_ray": [
                str(mapping[t]) for t in ambient_angles],
            "critical_face_ambient_pairs": [pair_id(pair) for pair in face],
            "critical_face_internal_pairs": [
                pair_id(tuple(sorted(mapping[t] for t in pair))) for pair in face],
            "vertices": rows,
        })
        previous_pairs, previous_mapping = pairs, mapping
        pairs = {}
        for parent, word in previous_pairs.items():
            children = central_g_preimages(parent, word, excluded)
            assert not pairs.keys() & children.keys()
            pairs.update(children)

    # Independent internal-plane slit pullback using the normalized G critical
    # value angle 25/56. Its analytic identification is in the terminal audit;
    # equality here is only the independent rational cross-check.
    internal_tree = generate_tree(F(25, 56))
    for level, direct in zip(levels, internal_tree):
        assert {row["internal_pair"] for row in level["vertices"]} == {
            row["id"] for row in direct["vertices"]}
        assert set(level["critical_face_internal_pairs"]) == set(
            direct["critical_piece_boundary_pairs"])
    return {
        "status": "EXACT_TIP_G_INTERNAL_AMBIENT_LIFTS_DEPTH6_PASS",
        "ambient_map": "f(z)=z^2+c_tip",
        "internal_map": "G=f^3 on the central degree-two return",
        "alpha_G_ambient_rays": [str(t) for t in G_ALPHA],
        "alpha_G_internal_images": [str(seed_mapping[t]) for t in G_ALPHA],
        "seed_period_at_most_six_candidates": [str(t) for t in candidate_ambient],
        "seed_exact_period_six_candidates": [str(t) for t in exact_period_six],
        "independent_internal_critical_value_angle": "25/56",
        "maximum_internal_puzzle_depth": MAX_DEPTH,
        "levels": levels,
        "scope": "Actual ambient access labels under the written landing/eligibility proof; finite arithmetic only in this program; no O/xi/eta or localization-sheet identification",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-manifest", action="store_true")
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()
    report = certify()
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.check_manifest:
        manifest = Path(__file__).resolve().parents[2] / "results" / "tip_internal_ray_lifts.json"
        assert manifest.read_text(encoding="utf-8") == encoded, "manifest differs"
    print(encoded if args.print_json else report["status"],
          end="" if args.print_json else "\n")


if __name__ == "__main__":
    main()
