#!/usr/bin/env python3
"""Endpoint-aware checks accompanying the written selected-slit theorem.

The input is the ten already isolated physical parameter cells.  All interval
arithmetic here is independent and uses outward rounding on a 2^-640 grid.
The analytic identification, the full-path collar lemma, and the all-period
Chebyshev argument are WRITTEN proofs in NOTE.md, not outputs of this script.

Run with --write to create this new contribution's results.json, or without
arguments to compare it.  No upstream file is modified.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
INPUT = ROOT / "research/independent_audits/real_primitive_tip_family_unconditional_20261116/results.json"
OUTPUT = HERE / "results.json"
PRECISION = 640
SCALE = 1 << PRECISION


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def floor_q(q: Q) -> int:
    return q.numerator // q.denominator


def ceil_q(q: Q) -> int:
    return -((-q.numerator) // q.denominator)


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        require(self.lo <= self.hi, "inverted interval")

    @staticmethod
    def hull(lo: Q, hi: Q) -> "Interval":
        require(lo <= hi, "inverted rational interval")
        return Interval(floor_q(lo * SCALE), ceil_q(hi * SCALE))

    @staticmethod
    def point(q: Q | int) -> "Interval":
        q = Q(q)
        return Interval.hull(q, q)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + -other

    def square(self) -> "Interval":
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        high = max(self.lo**2, self.hi**2)
        return Interval(low // SCALE, -((-high) // SCALE))

    def before(self, other: "Interval") -> bool:
        return self.hi < other.lo

    def midpoint(self) -> Q:
        return Q(self.lo + self.hi, 2 * SCALE)


def iterate(z: Interval, c: Interval, n: int) -> Interval:
    for _ in range(n):
        z = z.square() + c
    return z


def alpha_cell(c: Interval, p: int, left: Interval, right: Interval) -> Interval:
    a, b = Q(left.hi, SCALE), Q(right.lo, SCALE)
    require(a < b, "alpha starting cell is empty")
    require((iterate(Interval.point(a), c, p) - Interval.point(a)).lo > 0,
            "alpha left sign")
    require((iterate(Interval.point(b), c, p) - Interval.point(b)).hi < 0,
            "alpha right sign")
    for _ in range(150):
        middle = (a + b) / 2
        sign = iterate(Interval.point(middle), c, p) - Interval.point(middle)
        if sign.lo > 0:
            a = middle
        elif sign.hi < 0:
            b = middle
        else:
            raise AssertionError("alpha sign unresolved")
    return Interval.hull(a, b)


def locate(z: Interval, side: int, cuts: list[Interval]) -> int:
    n = len(cuts)
    if z.before(cuts[0]):
        return 0
    if cuts[-1].before(z):
        return n
    for k in range(1, n):
        if cuts[k - 1].before(z) and z.before(cuts[k]):
            return k if side == 1 else 2 * n - k
    raise AssertionError("sample was not separated from every cut")


def sample_atom(j: int, cuts: list[Interval], left: Interval,
                right: Interval) -> tuple[Q, int]:
    n = len(cuts)
    if j == 0:
        a, b, side = left, cuts[0], 1
    elif j == n:
        a, b, side = cuts[-1], right, 1
    else:
        k, side = (j, 1) if j < n else (2 * n - j, -1)
        a, b = cuts[k - 1], cuts[k]
    require(a.before(b), "empty real source atom")
    # This asymmetric sample avoids the critical point in the central atom.
    return (2 * a.midpoint() + b.midpoint()) / 3, side


def cyclic_blocks(labels: list[int]) -> list[list[int]]:
    n = len(labels)
    result = []
    for i in range(10):
        starts = [j for j in range(n)
                  if labels[j] == i and labels[(j - 1) % n] != i]
        require(len(starts) == 1, "coarse block is disconnected")
        j, block = starts[0], []
        while labels[j] == i:
            require(len(block) < n, "block covers everything")
            block.append(j)
            j = (j + 1) % n
        result.append(block)
    require(sorted(sum(result, [])) == list(range(20)), "block partition failed")
    return result


def derive_atlas(row: dict) -> dict:
    p = row["p"]
    parameter = row["parameter_bracket"]
    denominator = 1 << parameter["denominator_power_of_two"]
    c = Interval.hull(Q(parameter["lower_numerator"], denominator),
                      Q(parameter["upper_numerator"], denominator))
    x = [Interval.point(0)]
    for _ in range(6 * p):
        x.append(x[-1].square() + c)
    r, ell, a, b, d, h = (x[j * p] for j in (1, 2, 5, 3, 6, 4))
    e = alpha_cell(c, p, d, h)
    target = [a, b, d, e, h]
    source = [-h, ell, a, -e, b, d, e, -a, -ell, h]
    require(all(u.before(v) for u, v in zip(target, target[1:])), "target order")
    extended = [-r, *source, r]
    require(all(u.before(v) for u, v in zip(extended, extended[1:])), "source order")
    require(ell.before(a) and h.before(r), "terminal intervals")

    # G'(z) has sign -sign(z) on the entire interval (-r,r), using
    # G'(z)=2^p z product_{j=1}^{p-1} f^j(z).
    real = Interval.hull(Q(0), Q(r.hi, SCALE))
    derivative_signs = []
    for j in range(1, p):
        real = real.square() + c
        require(real.hi < 0 if j == 1 else real.lo > 0,
                "whole-real-branch derivative factor is not separated")
        derivative_signs.append(-1 if j == 1 else 1)

    cover, collapse = [], []
    for j in range(20):
        q, side = sample_atom(j, source, -r, r)
        z = Interval.point(q)
        image = iterate(z, c, p)
        image_side = side if q < 0 else -side
        cover.append(locate(image, image_side, target))
        collapse.append(0 if z.before(ell) else locate(z, side, target))
    require(cover == [j % 10 for j in range(20)], "cover cyclic alignment")
    blocks = cyclic_blocks(collapse)

    # The cut lift is DERIVED from the physical incidence, rather than read.
    start = blocks[0][0] - 20
    lift = [start]
    for block in blocks:
        lift.append(lift[-1] + len(block))
    require(lift[-1] - lift[0] == 20, "degree-two lift increment")
    return {"p": p, "parameter_cell": parameter, "cover": cover,
            "collapse_labels": collapse, "blocks": blocks, "cut_lift": lift,
            "whole_real_derivative_factors": derivative_signs}


@dataclass(frozen=True)
class Arc:
    left: int
    right: int
    left_closed: bool = False
    right_closed: bool = False

    def __post_init__(self) -> None:
        require(0 <= self.right - self.left <= 10, "invalid target arc")


def lifted_cut(k: int, lift: list[int]) -> int:
    turn, index = divmod(k, 10)
    return lift[index] + 20 * turn


def advance(arc: Arc | None, lift: list[int]) -> Arc | None:
    """None denotes the entire circle, never a punctured circle."""
    if arc is None:
        return None
    a, b = lifted_cut(arc.left, lift), lifted_cut(arc.right, lift)
    length = b - a
    if length > 10 or (length == 10 and (arc.left_closed or arc.right_closed)):
        return None
    a0 = a % 10
    return Arc(a0, a0 + length, arc.left_closed, arc.right_closed)


def saturation_time(arc: Arc, lift: list[int]) -> int:
    for n in range(1, 20):
        arc = advance(arc, lift)
        if arc is None:
            return n
    raise AssertionError("marked arc did not saturate")


def closure(arc: Arc | None) -> Arc | None:
    if arc is None or arc.right - arc.left == 10:
        return None
    return Arc(arc.left, arc.right, True, True)


def check_marked_action(lift: list[int]) -> dict:
    counts = 0
    max_time = 0
    for a in range(10):
        for length in range(1, 11):
            for left_closed in (False, True):
                for right_closed in (False, True):
                    arc = Arc(a, a + length, left_closed, right_closed)
                    # The connected lift of a full closed/half-open turn is
                    # already the circle; those cases are handled separately.
                    if length == 10 and (left_closed or right_closed):
                        continue
                    max_time = max(max_time, saturation_time(arc, lift))
                    require(advance(closure(arc), lift) == closure(advance(arc, lift)),
                            "closure commutation at an original cut failed")
                    counts += 1
    require(max_time == 5, "sharp full-marked-interval bound changed")
    open_times = [saturation_time(Arc(j, j + 1), lift) for j in range(10)]
    closed_times = [saturation_time(Arc(j, j + 1, True, True), lift)
                    for j in range(10)]
    halfturns = []
    for a in range(10):
        for length in range(1, 10):
            if lifted_cut(a + length, lift) - lifted_cut(a, lift) == 10:
                image = advance(Arc(a, a + length), lift)
                require(image is not None and image.right - image.left == 10,
                        "open half-turn incorrectly called a full circle")
                require(advance(Arc(a, a + length, True, True), lift) is None,
                        "closed half-turn not a full circle")
                halfturns.append([a, a + length])
    require(halfturns, "half-turn regression lacks a witness")
    for k in (-1000001, -100, -1, 0, 1, 99, 1000001):
        require(lifted_cut(k + 10, lift) == lifted_cut(k, lift) + 20,
                "deck equivariance")
    return {"states_checked": counts, "maximum_saturation_time": max_time,
            "open_atom_saturation_times": open_times,
            "closed_atom_saturation_times": closed_times,
            "open_halfturn_examples": halfturns,
            "closure_commutes_at_original_marked_cuts": True,
            "attachment_root_stalk": {"target_atom": 0,
                 "source_closed_cut_span": [19, 22],
                 "source_atom_interiors": [19, 0, 1],
                 "covered_closed_cut_span": [9, 12],
                 "covered_atom_interiors": [9, 0, 1]}}


def tent_first_critical(a: Q, b: Q) -> int:
    require(Q(0) <= a < b <= Q(1), "invalid tent interval")
    length, bound = b - a, 0
    while length * (1 << bound) < 1:
        bound += 1
    for n in range(bound + 1):
        if a < Q(1, 2) < b:
            return n
        require(b - a == length * (1 << n), "precritical length doubling")
        if b <= Q(1, 2):
            a, b = 2 * a, 2 * b
        else:
            require(a >= Q(1, 2), "branch not selected")
            a, b = 2 - 2 * b, 2 - 2 * a
    raise AssertionError("Chebyshev critical-hit bound failed")


def check_tent() -> dict:
    tested = 0
    for denominator in (8, 16, 32, 64):
        for a in range(denominator):
            for b in range(a + 1, denominator + 1):
                tent_first_critical(Q(a, denominator), Q(b, denominator))
                tested += 1
    delays = [1, 2, 3, 5, 10, 25, 50, 100, 1000]
    for n in delays:
        a, b = Q(1, 1 << (n + 3)), Q(1, 1 << (n + 2))
        for _ in range(n + 1):
            require(b < Q(1, 2), "advertised long avoidance contains critical angle")
            a, b = 2 * a, 2 * b
    return {"exact_interval_tests": tested, "avoidance_delays_tested": delays,
            "proof_bound": "first critical hit <= ceil(log2(1/angular_length))",
            "status": "finite regressions; all-interval theorem is written"}


def compute() -> dict:
    original = json.loads(INPUT.read_text(encoding="utf-8"))
    atlases = [derive_atlas(row) for row in original["periods"]]
    require([x["p"] for x in atlases] == list(range(3, 13)), "unexpected period set")
    lift = atlases[0]["cut_lift"]
    require(all(x["cut_lift"] == lift for x in atlases), "period-specific incidence drift")
    return {"schema": 1, "arithmetic": f"outward dyadic intervals 2^-{PRECISION}",
            "scope": "selected real slit family; geometric and Chebyshev proofs in NOTE.md",
            "all_period_status": "p>=13 uses the cited written chart theorem, not this finite check",
            "physical_atlases": atlases, "marked_action": check_marked_action(lift),
            "chebyshev_escape": check_tent()}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = compute()
    if args.write:
        OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        require(json.loads(OUTPUT.read_text(encoding="utf-8")) == result, "result manifest changed")
    print(json.dumps({"physical_periods": len(result["physical_atlases"]),
                      "cut_lift": result["physical_atlases"][0]["cut_lift"],
                      "marked_action": result["marked_action"],
                      "chebyshev_escape": result["chebyshev_escape"]}, indent=2))


if __name__ == "__main__":
    main()
