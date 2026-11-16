#!/usr/bin/env python3
"""Read-only rational/discrete regression for the M-discharge implication.

This is NOT a formalization of Caratheodory, KKL, or conformal geometry.
The cited notes prove those steps in prose with external theorems.
Here we replay the independent chart/gain certificates, and check the
finite incidence and strict rational implications needed by that proof.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUDITS = ROOT / "research" / "independent_audits"

# This is the physical iota* table, NOT the degree-two G_* covering table.
BLOCKS: dict[int, tuple[int, ...]] = {
    0: (18, 19, 0, 1, 2),
    1: (3, 4),
    2: (5,),
    3: (6,),
    4: (7, 8, 9),
    5: (10,),
    6: (11, 12, 13),
    7: (14,),
    8: (15,),
    9: (16, 17),
}
PARENT_BASE = (9, 0, 1)
SOURCE_BASES = ((1, 2, 3), (17, 18, 19))
CROSSING = ((3, 1), (19, 17))
AVOIDING = (3, 17)
# Strict *rational* bounds proved separately by the unchanged finite audit.
FLOORS = {
    3: (F(490, 1000), F(974, 1000), F(1, 100)),
    4: (F(511, 1000), F(985, 1000), F(7, 100)),
    **{p: (F(581, 1000), F(988, 1000), F(3, 10))
       for p in range(5, 13)},
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def span(n: int, a: int, b: int) -> int:
    """Inclusive shortest cyclic atom count, including both end atoms."""
    require(type(n) is int and n > 2 and
            type(a) is int and type(b) is int and
            0 <= a < n and 0 <= b < n and a != b,
            "invalid distinct cyclic endpoints")
    return min((b - a) % n, (a - b) % n) + 1


def check_marking(blocks: dict[int, tuple[int, ...]] = BLOCKS) -> None:
    """Finite order, block partition, attachment, and 3/3/7 vs 3/3/5.

    The proof that the numbers have PHYSICAL prime-end meaning is in the
    earlier identification theorem, not in this function.
    """
    require(set(blocks) == set(range(10)), "target atoms not I_0..I_9")
    require(blocks == BLOCKS, "physical iota* blocks changed")
    flat = [atom for block in blocks.values() for atom in block]
    require(len(flat) == 20 and set(flat) == set(range(20)),
            "source atom partition not a bijection")
    for i, block in blocks.items():
        require(bool(block) and all(0 <= a < 20 for a in block),
                f"bad I_{i} block")
        require(all((b - a) % 20 == 1 for a, b in zip(block, block[1:])),
                f"I_{i} block not consecutive")
    require(set((19, 0, 1)).issubset(blocks[0]),
            "left attachment not entirely in iota*I_0")
    require(PARENT_BASE == (9, 0, 1) and
            SOURCE_BASES == ((1, 2, 3), (17, 18, 19)),
            "changed A.1 bases/crests")

    inverse = {a: k for k, block in blocks.items() for a in block}
    require(all(inverse[a] != inverse[b] for a, b in (*CROSSING, AVOIDING)),
            "non-proper restriction within one immersion block")
    require(tuple(span(20, *pair) for pair in (*CROSSING, AVOIDING))
            == (3, 3, 7), "source proper short arcs changed")
    # The separate unbranched covering G_* sends S_j to I_(j mod 10).
    require(tuple((a % 10, b % 10)
                  for a, b in (*CROSSING, AVOIDING))
            == ((3, 1), (9, 7), (3, 7)),
            "G_* covering mistaken for iota*")
    require(tuple(span(10, a % 10, b % 10)
                  for a, b in (*CROSSING, AVOIDING))
            == (3, 3, 5), "target covered short arcs changed")
    require(all(span(20, *pair) > 2 for pair in (*CROSSING, AVOIDING)),
            "A.1 excludes source paths subordinate to <=2 atoms")
    require(all(sum((j % 10 == k) for j in range(20)) == 2
                for k in range(10)), "degree-two ideal cover lost")


def strict_bracket(row: dict, key: str) -> tuple[F, F]:
    pair = row.get(key)
    require(isinstance(pair, (list, tuple)) and len(pair) == 2 and
            all(type(n) is int for n in pair) and pair[0] < pair[1],
            f"invalid strict millionth interval: {key}")
    return F(pair[0], 10**6), F(pair[1], 10**6)


def check_finite_report(rows: list[dict]) -> None:
    """Independently compare outward strict bounds with rational defect logic."""
    require(type(rows) is list and [r["p"] for r in rows] ==
            list(range(3, 13)), "missing, duplicate or reordered physical p")
    for row in rows:
        p = row["p"]
        parent_floor, child_cap, gain_floor = FLOORS[p]
        expected_chart = ("right-circular-segment" if p in (3, 4)
                          else "right-semidisk")
        require(row["construction"] == expected_chart,
                f"p={p}: wrong embedded target quadrilateral")
        require((F(row["proved_parent_gt"]), F(row["proved_child_lt"]),
                 F(row["proved_D_gt"])) ==
                (parent_floor, child_cap, gain_floor),
                f"p={p}: changed claimed strict thresholds")
        lo_P, hi_P = strict_bracket(row, "parent_competitor_strict_1e-6")
        lo_C, hi_C = strict_bracket(row, "child_actual_upper_strict_1e-6")
        lo_E, hi_E = strict_bracket(row, "child_plane_upper_strict_1e-6")
        lo_D, hi_D = strict_bracket(row, "defect_strict_lower_1e-6")
        # The 10^-6 display brackets can STRADDLE a strict threshold:
        # the p3 source-metric saving is only 1/5,000,000. Strict
        # comparisons are made on full 2^-512 intervals in finite.certify(),
        # not inferred by rounding these presentation brackets.
        require(hi_P > parent_floor and lo_C < child_cap and
                lo_E < hi_E and hi_C > 0,
                f"p={p}: inconsistent physical parent/child brackets")
        require(hi_D > gain_floor and hi_D > lo_D,
                f"p={p}: reported gain bracket cannot contain strict sign")
        # Correct reciprocal reversal: P > floor, C < cap.
        require(F(2) / child_cap - F(1) / parent_floor > gain_floor,
                f"p={p}: displayed defect does not follow")
        require(hi_D > 0 and lo_P < hi_P and lo_C < hi_C and
                lo_E < hi_E, f"p={p}: malformed bracket")


def check_physical_cut_order(finite, rows: list[dict]) -> None:
    """Reconstruct BOTH real orders with outward enclosures, not labels alone.

    Every selected period is independently re-isolated from the immutable
    exact dyadic packet. This is an arithmetic test of (O1),(O2), NOT a
    Python proof that the prime-end accesses have these labels.
    """
    for row in rows:
        p, c, orbit = finite.v.checked_packet(row)
        xp, x2, x3, x4, x5, x6 = (orbit[j*p] for j in range(1, 7))
        alpha = finite.v.alpha_interval(p, c, orbit)
        zero = finite.v.Iv.point(0)
        target = (x2, x5, x3, zero, x6, alpha, x4, xp)
        source = (-xp, -x4, x2, x5, -alpha, x3, x6, alpha,
                  -x5, -x2, x4, xp)
        require(all(a.lt(b) for a, b in zip(target, target[1:])),
                f"p={p}: selected physical target cuts cross")
        require(all(a.lt(b) for a, b in zip(source, source[1:])),
                f"p={p}: selected physical inverse cuts cross")


def check_tail_floor(parent: F = F(2, 3),
                     child: F = F(63, 50)) -> F:
    require(parent > 0 and child > 0, "nonpositive tail data")
    defect = F(2)/child - F(1)/parent
    require(defect == F(11, 126) and defect > F(1, 100),
            "p>=13 rational tail gain does not imply finite bound")
    return defect


def load_verifier(directory: str, module_name: str):
    filename = AUDITS / directory / "verify.py"
    require(filename.is_file(), f"missing read-only predecessor: {filename}")
    spec = importlib.util.spec_from_file_location(module_name, filename)
    require(spec is not None and spec.loader is not None,
            "cannot import certified predecessor")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def run() -> None:
    check_marking()
    check_tail_floor()

    # The prior three-return certificate checks the *actual* selected roots
    # using adjacent 2^-256 brackets, full-complex-disk errors, and p>=13.
    prime = load_verifier(
        "real_primitive_tip_family_prime_end_identification_20261116",
        "m_discharge_prime")
    old = json.loads((AUDITS /
        "real_primitive_tip_family_unconditional_20261116/results.json"
        ).read_text())
    finite_prime = prime.check_all_finite(old)
    require([r["p"] for r in finite_prime] == list(range(3, 13)),
            "prime-end analytic finite witnesses not complete")
    require(prime.check_large_model()["p"] == ">=13",
            "all-period three-return bound absent")

    # The finite gain verifier ALSO replays the limiting/canonical/sandwich
    # intervals. It checks the p3/p4 segment, p5..p12 semidisk, whole-target
    # gate, true-source Rouché exclusion and positive missing SC energy.
    finite = load_verifier(
        "tip_family_finite_p_wave_gain_20261116", "m_discharge_finite")
    check_finite_report(finite.certify())
    check_physical_cut_order(finite, old["periods"])
    require(finite.lim.PARENT_TAIL_FLOOR == F(2, 3) and
            finite.lim.CHILD_TAIL_CEILING == F(63, 50) and
            finite.lim.TAIL_GAIN_FLOOR == F(11, 126),
            "all-p normalized chart constants changed")
    print("PASS: physical p3..12 charts + p>=13 chart, strict gain floors; "
          "KKL prime ends/A.1/conformal embeddings require the cited "
          "mathematical theorems, not Python.")


if __name__ == "__main__":
    run()
