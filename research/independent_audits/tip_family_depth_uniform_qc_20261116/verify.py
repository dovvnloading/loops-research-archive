#!/usr/bin/env python3
"""Finite consistency checks for a *conditional* non-compounding QC lemma.

No numerical K or global KKL conjugacy is constructed or certified here.
The expensive (3,3,3) inequalities are recomputed by the unchanged
archived Fraction/interval verifier, imported read-only.
"""
from __future__ import annotations

import argparse
import importlib.util
from fractions import Fraction as Q
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ARCHIVED = HERE.parent / "tip_family_all_depths_20261116" / "verify.py"

# Terminal *local* combinatorics only: these are not k-fold boundary atoms.
BLOCKS = (
    (18, 19, 0, 1, 2), (3, 4), (5,), (6,), (7, 8, 9),
    (10,), (11, 12, 13), (14,), (15,), (16, 17),
)
COVER = tuple(s % 10 for s in range(20))
PAIRS = ((3, 1), (19, 17), (3, 17))
EDGE_CUT_IMAGES = (2, 4, 4, 3, 0)
EDGES = ((0, 1), (2, 3), (3, 4))
MATRIX = ((0, 0, 1), (1, 0, 1), (1, 1, 0))

# The large-period 0.26 lower bound is certified only for p>=13.
GENERAL_REFERENCE = (Q(1, 4), Q(39, 50))
LARGE_PERIOD_REFERENCE = (Q(13, 50), Q(39, 50))
CREST_P3_REFERENCE = (Q(5676, 10000), Q(5684, 10000))


class VerificationError(AssertionError):
    """Finite-algebraic inconsistency, never an analytic KKL counterexample."""


def ensure(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def rational(value: Q | int | str) -> Q:
    ensure(not isinstance(value, (float, bool)), "float/bool not exact input")
    try:
        return Q(value)
    except (TypeError, ValueError, ZeroDivisionError) as exc:
        raise VerificationError("invalid rational input") from exc


def shortest_inclusive_span(a: int, b: int, total: int) -> int:
    ensure(total > 2 and 0 <= a < total and 0 <= b < total,
           "invalid atom index")
    return 1 + min((a - b) % total, (b - a) % total)


def marked_table_check(
    blocks: tuple[tuple[int, ...], ...] = BLOCKS,
    cover: tuple[int, ...] = COVER,
    pairs: tuple[tuple[int, int], ...] = PAIRS,
    cut_images: tuple[int, ...] = EDGE_CUT_IMAGES,
) -> dict[str, object]:
    """Reject collapsing the distinct cover/immersion and malformed marking."""
    ensure(len(blocks) == 10, "need ten target immersion blocks")
    ensure(all(len(b) >= 1 for b in blocks), "empty immersion block")
    ensure(sorted(s for b in blocks for s in b) == list(range(20)),
           "immersion is not a disjoint complete source partition")
    ensure(all(b[(i + 1) % len(b)] == (b[i] + 1) % 20
               for b in blocks for i in range(len(b) - 1)),
           "immersion blocks are not consecutive")
    ensure(blocks == BLOCKS, "immersion/attachment changed")
    ensure(cover == COVER and len(cover) == 20, "covering push changed")
    ensure(tuple(cover.count(i) for i in range(10)) == (2,) * 10,
           "not a double covering")
    immersion = {s: i for i, block in enumerate(blocks) for s in block}
    ensure(any(cover[s] != immersion[s] for s in range(20)),
           "cover conflated with immersion")
    ensure(tuple(immersion[s] for s in (19, 0, 1)) == (0, 0, 0),
           "single attached source triple moved")
    ensure(pairs == PAIRS, "proper source endpoint pairs changed")
    src = tuple(shortest_inclusive_span(a, b, 20) for a, b in pairs)
    tgt = tuple(shortest_inclusive_span(cover[a], cover[b], 10)
                for a, b in pairs)
    ensure(src == (3, 3, 7) and tgt == (3, 3, 5),
           "inclusive source/cover target spans changed")
    ensure(all(x > 2 for x in src + tgt), "KKL strict >2 filter failed")
    ensure(all(immersion[a] != immersion[b] for a, b in pairs),
           "proper immersion path lost")
    ensure(cut_images == EDGE_CUT_IMAGES, "old-edge images changed")
    computed = tuple(tuple(
        int(min(cut_images[EDGES[col][0]], cut_images[EDGES[col][1]]) <= row[0]
            and row[1] <=
            max(cut_images[EDGES[col][0]], cut_images[EDGES[col][1]]))
        for col in range(3)) for row in EDGES)
    ensure(computed == MATRIX, "old-edge incidence matrix changed")
    # I1 and I9 are sides of the SAME old real edge; do not count twice.
    ensure(len({(0, 1)}) == 1 and blocks[1] != blocks[9],
           "old edge side bookkeeping failed")
    return {"source_spans": src, "target_spans": tgt, "edge_matrix": computed}


def reference_bounds(period: int) -> tuple[Q, Q]:
    ensure(type(period) is int and period >= 3, "reference period must be >=3")
    return LARGE_PERIOD_REFERENCE if period >= 13 else GENERAL_REFERENCE


def qc_image_bounds(lower: Q | int | str, upper: Q | int | str,
                    K: Q | int | str) -> tuple[Q, Q]:
    """Strict conditional widths for a *bijectively transported* full Wave class."""
    lo, hi, k = rational(lower), rational(upper), rational(K)
    ensure(Q(0) < lo < hi and k >= 1, "invalid positive width/K bounds")
    return lo / k, hi * k


def level_bounds(depth: int, reference_period: int,
                 K: Q | int | str) -> tuple[Q, Q]:
    """K is an ASSUMED uniform dilatation; depth is never multiplied into it."""
    ensure(type(depth) is int and depth >= 1, "invalid depth")
    return qc_image_bounds(*reference_bounds(reference_period), K)


def crest_ratio_bounds(lower: Q | int | str, upper: Q | int | str,
                       K: Q | int | str) -> tuple[Q, Q]:
    """Both positive numerator and denominator transported: a K^2 loss."""
    lo, hi, k = rational(lower), rational(upper), rational(K)
    ensure(Q(0) < lo < hi and k >= 1, "invalid positive ratio/K bounds")
    return lo / (k * k), hi * k * k


def archived_depth_three() -> dict[str, Q]:
    """Execute the original exact certificate, not a copied decimal calculation."""
    ensure(ARCHIVED.is_file(), "merged depth-three source is missing")
    spec = importlib.util.spec_from_file_location("_depth_three_qc_regression", ARCHIVED)
    ensure(spec is not None and spec.loader is not None, "cannot load source verifier")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module  # dataclass annotations resolve this module
    spec.loader.exec_module(module)
    module.check_marked_tables(BLOCKS)
    ensure(module.PERIODS == (3, 9, 27), "periods no longer (3,9,27)")
    ensure(module.RADII == (Q(1, 4), Q(1, 40), Q(1, 250)),
           "physical disk radii have drifted")
    result = module.verify()
    floors = {
        "rouche1": Q(127470, 10**6),
        "rouche2": Q(6346, 10**6),
        "rouche3": Q(3900, 10**6),
        "normalized_third": Q(172673, 10**6),
        "radial_width_lower": Q(252105, 10**6),
    }
    for name, bound in floors.items():
        ensure(type(result[name]) is Q and result[name] > bound,
               f"depth-three strict lower rational bound failed: {name}")
    ensure(type(result["plane_width_upper"]) is Q
           and result["plane_width_upper"] < Q(764704, 10**6),
           "depth-three strict full-plane upper rational bound failed")
    ensure(result["radial_width_lower"] < result["plane_width_upper"],
           "contradictory depth-three width enclosures")
    # The tempting "0.26" conclusion is intentionally NOT asserted.
    ensure(result["radial_width_lower"] > Q(1, 4)
           and result["plane_width_upper"] < Q(31, 40),
           "merged physical (3,3,3) sandwich drifted")
    return result


def quick_checks() -> None:
    marked_table_check()
    for k in (Q(1), Q(3, 2), Q(2), Q(17, 3)):
        ensure(level_bounds(1, 3, k) == level_bounds(100000, 3, k),
               "depth-compounding error")
        ensure(level_bounds(1, 13, k) == (Q(13, 50) / k, Q(39, 50) * k),
               "large-period conditional width arithmetic error")
        ensure(level_bounds(1, 3, k) == (Q(1, 4) / k, Q(39, 50) * k),
               "small-period lower bound was silently strengthened")
        ensure(crest_ratio_bounds(*CREST_P3_REFERENCE, k)
               == (CREST_P3_REFERENCE[0] / (k * k),
                   CREST_P3_REFERENCE[1] * k * k),
               "crest numerator/denominator K^2 accounting error")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="test only finite marking and conditional algebra")
    args = parser.parse_args()
    quick_checks()
    print("PASS: 10/20 local marking; distinct covering/immersion; spans 3,3,7 / 3,3,5")
    print("PASS: conditional width <=K, ratio <=K^2, with NO depth product")
    print("Reference p>=13: strict (0.26/K, 0.78*K); p=3,4: only (0.25/K, 0.78*K)")
    if not args.quick:
        r = archived_depth_three()
        for key in ("rouche1", "rouche2", "rouche3", "normalized_third",
                    "radial_width_lower", "plane_width_upper"):
            print(f"PASS exact rational depth-three {key} ({r[key].numerator.bit_length()}-bit numerator)")
    print("NOT CERTIFIED: global KKL marking/QC transport, numerical K, any all-depth width theorem")


if __name__ == "__main__":
    main()
