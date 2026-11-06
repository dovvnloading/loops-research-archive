#!/usr/bin/env python3
"""Exact ordinary KL pseudo-piece side atlas at the two tip stages.

The companion note proves the gluing, prime-end interpretation, and same-root
canonical-localization lifts. This program independently extracts the relevant
faces from the landed ray trees, checks all rational side endpoints and ambient
representatives, and verifies the finite same-stage inclusion collision. It does
not certify the analytic theorems or identify a cross-scale protected-side map.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from verify_tip_internal_ray_lifts import certify as internal_certificate
from verify_tip_kl_puzzle import certify as top_puzzle_certificate
from verify_tip_puzzle_ray_tree import (
    Pair, certify as ambient_certificate, critical_face, pair_id,
)
from verify_tip_ray_portrait import LOWER


PIECES = {
    "P": (1, F(1, 4), ((F(1, 6), F(1, 3)), (F(2, 3), F(5, 6)))),
    "QL": (3, F(5, 16), ((F(7, 24), F(1, 3)), (F(2, 3), F(17, 24)))),
    "QR": (3, F(3, 16), ((F(1, 6), F(5, 24)), (F(19, 24), F(5, 6)))),
    "V0": (3, F(1, 4), ((F(5, 24), F(7, 24)), (F(17, 24), F(19, 24)))),
    "W": (6, None, ((F(41, 192), F(43, 192)),
                     (F(53, 192), F(55, 192)),
                     (F(137, 192), F(139, 192)),
                     (F(149, 192), F(151, 192)))),
}
BASE_HEIGHT = F(1, 256)
CARRIER_TO_PUZZLE_HEIGHT = F(2)


def external_intervals(pairs: dict[Pair, str], probe: F) -> tuple[list[Pair], list[Pair]]:
    """Recover a face and its exterior intervals from the full planar ray tree."""
    face = critical_face(pairs, (probe,))
    excluded = [tuple(sorted((t - probe) % 1 for t in pair)) for pair in face]
    angles = sorted(t for pair in face for t in pair)
    assert len(set(angles)) == len(angles)
    intervals = []
    for a, b in zip(angles, angles[1:] + [angles[0] + 1]):
        midpoint = ((a + b) / 2 - probe) % 1
        if all(not left < midpoint < right for left, right in excluded):
            # These five particular faces have no seam crossing angle zero.
            assert 0 < a < b < 1
            intervals.append((a, b))
    assert len(intervals) == len(face)
    assert sum(b - a for a, b in intervals) < 1
    return face, intervals


def index_level(level: dict, stage: str) -> tuple[dict[Pair, dict], dict[F, F]]:
    vertices, ambient = {}, {}
    for row in level["vertices"]:
        if stage == "f":
            angles = tuple(F(t) for t in row["angles"])
            correspondence = [(t, t) for t in angles]
        else:
            angles = tuple(F(t) for t in row["internal_pair"].split(","))
            correspondence = list(zip(
                map(F, row["corresponding_internal_angles"]),
                map(F, row["ambient_angles"]),
            ))
        assert angles == tuple(sorted(angles))
        vertices[angles] = row
        for theta, physical in correspondence:
            assert theta not in ambient or ambient[theta] == physical
            ambient[theta] = physical
    assert len(vertices) == level["vertex_count"]
    assert len(ambient) == level["ray_count"]
    return vertices, ambient


def vertex_record(pair: Pair, vertices: dict[Pair, dict], ambient: dict[F, F]) -> dict:
    row = vertices[pair]
    return {
        "stage_ray_pair": pair_id(pair),
        "stage_angles": [str(t) for t in pair],
        "ambient_representatives_in_stage_angle_order": [str(ambient[t]) for t in pair],
        "physical_landing_target": row["landing_target"],
    }


def dynamics_record(source: dict, target: dict, time: int, physical_step: int) -> dict:
    routes = []
    for tile in source["tiles"]:
        a, b = map(F, tile["seam_stage_angles"])
        scaled_a, scaled_b = 2**time * a, 2**time * b
        carry = scaled_a.numerator // scaled_a.denominator
        image = (scaled_a - carry, scaled_b - carry)
        assert 0 < image[0] < image[1] < 1
        targets = [t for t in target["tiles"]
                   if tuple(map(F, t["seam_stage_angles"])) == image]
        assert len(targets) == 1
        target_tile = targets[0]
        for physical, image_physical in zip(tile["ambient_endpoint_representatives"],
                                           target_tile["ambient_endpoint_representatives"]):
            assert (2**(physical_step * time) * F(physical)) % 1 == F(image_physical)
        routes.append({
            "source_tile": tile["id"], "target_tile": target_tile["id"],
            "angular_integer_carry": carry,
        })
    counts = [sum(r["target_tile"] == t["id"] for r in routes) for t in target["tiles"]]
    degree = len(source["tiles"]) // len(target["tiles"])
    assert counts == [degree] * len(target["tiles"])
    return {"stage_time": time, "physical_f_time": time * physical_step,
            "degree": degree, "tile_routes": routes}


def inclusion_record(source: dict, target: dict) -> dict:
    routes = []
    for tile in source["tiles"]:
        a, b = map(F, tile["seam_stage_angles"])
        targets = [t for t in target["tiles"]
                   if F(t["seam_stage_angles"][0]) <= a < b
                   <= F(t["seam_stage_angles"][1])]
        assert len(targets) == 1
        routes.append({"source_tile": tile["id"], "target_tile": targets[0]["id"],
                       "angular_integer_shift": 0})
    assert {r["target_tile"] for r in routes} == {t["id"] for t in target["tiles"]}
    return {"tile_routes": routes,
            "boundary_image_warning": "Source outer and Julia boundary can map into target interior"}


def certify() -> dict:
    source_reports = {"f": ambient_certificate(), "G": internal_certificate()}
    top = top_puzzle_certificate()
    assert top["outer_g3_fixed_a_bracket"] == ["3/32", "1/10"]
    stages = []
    for stage, physical_step, tau in (("f", 1, LOWER), ("G", 3, F(25, 56))):
        levels = source_reports[stage]["levels"]
        pieces = {}
        for name, (depth, fixed_probe, expected_intervals) in PIECES.items():
            vertices, ambient = index_level(levels[depth], stage)
            probe = tau / 2 if fixed_probe is None else fixed_probe
            face, intervals = external_intervals({pair: "" for pair in vertices}, probe)
            assert intervals == list(expected_intervals)
            if name in ("P", "V0", "W"):
                key = ("critical_piece_boundary_pairs" if stage == "f"
                       else "critical_face_internal_pairs")
                assert {pair_id(pair) for pair in face} == set(levels[depth][key])
            height = F(1, 2**depth)
            assert 0 < BASE_HEIGHT < height / 2
            tiles = []
            for i, (a, b) in enumerate(intervals):
                previous = (i - 1) % len(intervals)
                following = (i + 1) % len(intervals)
                incoming = tuple(sorted((intervals[previous][1], a)))
                outgoing = tuple(sorted((b, intervals[following][0])))
                assert incoming in face and outgoing in face
                tile_id = f"{stage}:{name}:tile{i}"
                midpoint = (a + b) / 2
                tiles.append({
                    "id": tile_id, "index": i,
                    "seam_stage_angles": [str(a), str(b)],
                    "ambient_endpoint_representatives": [str(ambient[a]), str(ambient[b])],
                    "seam_midpoint_lift": str(midpoint),
                    "basepoint_height_relative_to_initial": str(BASE_HEIGHT),
                    "tile_mark_height_relative_to_initial": str(height / 2),
                    "finite_gluing_height_relative_to_initial": str(height),
                    "lambda": {"outer_line": "all real x",
                               "carrier_height_relative_to_initial": str(CARRIER_TO_PUZZLE_HEIGHT * height),
                               "wrapping_endpoints": ["-infinity", "+infinity"]},
                    "xi": {"inner_halfline": ["-infinity", str(a)],
                           "finite_endpoint_vertex": vertex_record(incoming, vertices, ambient)},
                    "eta": {"inner_halfline": [str(b), "+infinity"],
                            "finite_endpoint_vertex": vertex_record(outgoing, vertices, ambient)},
                    "outgoing_vertex_boundary": [f"{tile_id}:eta",
                                                  f"{stage}:{name}:tile{following}:xi"],
                    "central_seam_warning": "The open inner seam is glued to the central copy; it is not a remaining ideal J side",
                })
            pieces[name] = {
                "depth": depth, "physical_inverse_time": physical_step * depth,
                "height_relative_to_initial": str(height),
                "face_probe_stage_angle": str(probe),
                "vertex_count": len(face), "tile_count": len(tiles),
                "boundary_vertices": [vertex_record(pair, vertices, ambient) for pair in sorted(face)],
                "tiles": tiles,
            }

        dynamics = {
            "QL_to_P": dynamics_record(pieces["QL"], pieces["P"], 2, physical_step),
            "QR_to_P": dynamics_record(pieces["QR"], pieces["P"], 2, physical_step),
            "W_to_V0": dynamics_record(pieces["W"], pieces["V0"], 3, physical_step),
        }
        inclusions = {
            "QL_into_P": inclusion_record(pieces["QL"], pieces["P"]),
            "QR_into_P": inclusion_record(pieces["QR"], pieces["P"]),
            "V0_into_P": inclusion_record(pieces["V0"], pieces["P"]),
            "W_into_V0": inclusion_record(pieces["W"], pieces["V0"]),
        }

        # Two different J-side prime ends under the actual source inclusion.
        witness, partner = F(11, 48), F(13, 48)
        first, second = pieces["W"]["tiles"][:2]
        assert F(first["seam_stage_angles"][1]) < witness < F(second["seam_stage_angles"][0])
        assert F(first["seam_stage_angles"][1]) < partner < F(second["seam_stage_angles"][0])
        target = pieces["V0"]["tiles"][0]
        assert F(target["seam_stage_angles"][0]) < witness < partner < F(target["seam_stage_angles"][1])
        routes = inclusions["W_into_V0"]["tile_routes"]
        assert routes[0]["target_tile"] == routes[1]["target_tile"] == target["id"]
        interior_height = F(pieces["W"]["height_relative_to_initial"]) / 2
        assert 0 < interior_height < F(pieces["V0"]["height_relative_to_initial"])
        vertices, ambient = index_level(levels[6], stage)
        pair = (witness, partner)
        assert pair in vertices
        assert pair not in {tuple(map(F, row["stage_angles"])) for row in pieces["W"]["boundary_vertices"]}
        assert pair not in {tuple(map(F, row["stage_angles"])) for row in pieces["V0"]["boundary_vertices"]}
        collision = {
            "source_defined_map": "KL Lemma 3.4 inclusion Psi(W) into Psi(V0)",
            "side_points": [f"{first['id']}:eta", f"{second['id']}:xi"],
            "same_finite_angle_lift": str(witness),
            "ambient_representative": str(ambient[witness]),
            "interior_collision_height_relative_to_initial": str(interior_height),
            "interior_source_points": [first["id"], second["id"]],
            "common_physical_landing_vertex": vertex_record(pair, vertices, ambient),
            "target_location": "central interior of Psi(V0), outside the terminal root",
            "cross_scale": False,
            "analytic_dependence": "Distinct interior tile points, ideal side points, and their common images follow from the note's gluing proof",
        }
        assert sum(piece["tile_count"] for piece in pieces.values()) == 12
        stages.append({
            "stage": stage, "physical_time_per_stage_step": physical_step,
            "ordinary_stage_filled_set": "K(f)" if stage == "f" else "K3",
            "terminal_root": "K3" if stage == "f" else "K9",
            "coordinate_type": ("ambient Bottcher angle and height" if stage == "f"
                                else "straightening-transported topological angle and height; not a physical conformal metric"),
            "pieces": pieces, "dynamics": dynamics, "inclusions": inclusions,
            "same_stage_side_collision": collision,
        })
    return {
        "status": "EXACT_TIP_KL_ORDINARY_SIDE_ATLAS_PASS",
        "stages": stages, "total_pieces": 10, "total_tiles": 24,
        "source_boundary_identity": "partial^v_i Psi(Y) = eta_i union xi_(i+1)",
        "height_unit": "initial geometric puzzle height h; carrier height H=2h",
        "carrier_to_geometric_puzzle_height": str(CARRIER_TO_PUZZLE_HEIGHT),
        "basepoint_convention": "angle 0 at height h/256; increase angle to the listed midpoint, then change height to h_m/2",
        "retained_sheet_coordinate": "all integer translates in each universal tile; no finite coset quotient",
        "analytic_dependencies": [
            "Existing analytic landing proofs for the two complete depth-six ray trees",
            "KL Decorations Lemmas 3.3 and 3.4 and section 3.2.4",
            "Written phase-avoidance proof and Kahn Theorem 7.12 for same-root canonical immersions",
        ],
        "scope": "Ordinary source pseudo-piece sides, ambient endpoint labels, finite branch routing, and same-stage inclusion collisions; no cross-scale protected-side functor",
        "ledger_status_changes": [],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-manifest", action="store_true")
    parser.add_argument("--print-json", action="store_true")
    args = parser.parse_args()
    report = certify()
    encoded = json.dumps(report, sort_keys=True, indent=2) + "\n"
    if args.check_manifest:
        path = Path(__file__).resolve().parents[2] / "results" / "tip_kl_side_atlas.json"
        assert path.read_text(encoding="utf-8") == encoded, "manifest differs"
    print(encoded if args.print_json else report["status"],
          end="" if args.print_json else "\n")


if __name__ == "__main__":
    main()
