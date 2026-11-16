#!/usr/bin/env python3
"""Independent, source-locked PR #68 native wave-transfer regenerator.

Standard-library rational/interval arithmetic; never imports the PR #68 checker.
Topology/KKL results are *stated dependencies*, not proved by finite code.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
INPUT = HERE / "physical_examples/tip_pr68.json"
LOCK = HERE / "source_contracts/LOCK.json"
CONTRACT = HERE / "source_contracts/record_fields.json"
MANIFEST = HERE / "experiment_manifests/tip_pr68.json"
ORIGINAL = REPO / "results/tip_root_interval_geometry.json"
REFERENCE = REPO / "results/tip_KKL_tree_marked_breakage_20261109.json"
SCALE = 1 << 256


def ensure(predicate: bool, reason: str) -> None:
    if not predicate:
        raise AssertionError(reason)


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


@dataclass(frozen=True)
class Box:
    """Outward 2^-256 dyadic enclosure of a real number (inclusive)."""
    low: int
    high: int

    def __post_init__(self) -> None:
        ensure(self.low <= self.high, "empty interval")

    @classmethod
    def rational(cls, value: Q | int) -> "Box":
        scaled = Q(value) * SCALE
        low = scaled.numerator // scaled.denominator
        high = -((-scaled.numerator) // scaled.denominator)
        return cls(low, high)

    def __add__(self, other: "Box") -> "Box":
        return Box(self.low + other.low, self.high + other.high)

    def __neg__(self) -> "Box":
        return Box(-self.high, -self.low)

    def square(self) -> "Box":
        a, b = self.low**2, self.high**2
        low = 0 if self.low <= 0 <= self.high else min(a, b)
        return Box(low // SCALE, (max(a, b) + SCALE - 1) // SCALE)

    def before(self, other: "Box") -> bool:
        return self.high < other.low

    def center(self) -> Q:
        return Q(self.low + self.high, 2 * SCALE)

    def contains(self, other: "Box") -> bool:
        return self.low <= other.low and other.high <= self.high

    def overlaps(self, other: "Box") -> bool:
        return not (self.before(other) or other.before(self))


def bracket(c: Box, steps: int = 27) -> list[Box]:
    orbit = [Box.rational(0)]
    for _ in range(steps):
        orbit.append(orbit[-1].square() + c)
    return orbit


def iterate3(z: Box, c: Box) -> Box:
    for _ in range(3):
        z = z.square() + c
    return z


def isolate_alpha(c: Box) -> Box:
    """Interval-bisect the dividing real fixed point of G; no guessed decimal."""
    lo, hi = Q(3, 32), Q(1, 10)
    ensure(Box.rational(lo).before(iterate3(Box.rational(lo), c)), "alpha lower sign")
    ensure(iterate3(Box.rational(hi), c).before(Box.rational(hi)), "alpha upper sign")
    for _ in range(88):
        mid = (lo + hi) / 2
        y, x = iterate3(Box.rational(mid), c), Box.rational(mid)
        if x.before(y):
            lo = mid
        elif y.before(x):
            hi = mid
        else:
            raise AssertionError("alpha interval too imprecise for bisection")
    return Box(Box.rational(lo).low, Box.rational(hi).high)


def isolate_negative_preimage(y: Box, c: Box, left: Box) -> Box:
    """Monotone negative branch G:[-x3,0] -> [x6,x3]."""
    lo, hi = Q(left.low, SCALE), Q(0)
    for _ in range(78):
        m = (lo + hi) / 2
        gm = iterate3(Box.rational(m), c)
        if gm.before(y):
            lo = m
        elif y.before(gm):
            hi = m
        else:
            raise AssertionError("source cut not separable at 78 bits")
    return Box(Box.rational(lo).low, Box.rational(hi).high)


def index_of(value: Box, side: int, cuts: list[Box]) -> int:
    """Two boundary sides on a real slit, terminal atom through either tip."""
    n = len(cuts)
    if value.before(cuts[0]):
        return 0
    if cuts[-1].before(value):
        return n
    for j in range(1, n):
        if cuts[j - 1].before(value) and value.before(cuts[j]):
            return j if side == 1 else 2*n - j
    raise AssertionError("point touches a cut or cannot be placed exactly")


def source_sample(s: int, cuts: list[Box], left: Box, right: Box) -> tuple[Q, int]:
    n = len(cuts)
    if s == 0:
        a, b, side = left, cuts[0], 1
    elif s == n:
        a, b, side = cuts[-1], right, 1
    else:
        j, side = (s, 1) if s < n else (2*n-s, -1)
        a, b = cuts[j-1], cuts[j]
    ensure(a.before(b), "sample cell not separated")
    return (2*a.center() + b.center())/3, side


def short_arc(a: int, b: int, size: int) -> list[int]:
    forward = (b-a) % size
    backward = (a-b) % size
    ensure(forward != backward, "ambiguous half-circle arc")
    start, length = (a, forward) if forward < backward else (b, backward)
    return [(start+k) % size for k in range(length+1)]


def cyclic_blocks(labels: list[int], target_count: int) -> list[list[int]]:
    n = len(labels)
    ensure(set(labels) == set(range(target_count)), "missing target cell")
    blocks = []
    for t in range(target_count):
        starts = [s for s in range(n) if labels[s] == t and labels[(s-1)%n] != t]
        ensure(len(starts) == 1, "disconnected immersion pullback cell")
        s, block = starts[0], []
        while labels[s] == t:
            ensure(len(block) < n, "cyclic cell overflow")
            block.append(s)
            s = (s+1) % n
        blocks.append(block)
    ensure(sorted(sum(blocks, [])) == list(range(n)), "pullback not a partition")
    return blocks


def disk_image(center: Q, radius: Q, c0: Q, cr: Q) -> tuple[Q, Q]:
    """Exact rational complex-ball bound for three polynomial applications."""
    d, r = center, radius
    for _ in range(3):
        r = 2*abs(d)*r + r*r + cr
        d = d*d + c0
    return d, r


def certify_circle(q: Q, w: Q, c0: Q, cr: Q, limit: Q,
                   center_in_tree: tuple[Q, Q]) -> dict:
    ensure(w < q, "clockwise/semicircle convention changed")
    mid, radius = (w+q)/2, (q-w)/2
    ensure(center_in_tree[0] < mid < center_in_tree[1], "disk center not in native tree")
    ensure(abs(mid)+radius < Q(1, 4), "physical circle not in target disk")
    d, r = disk_image(mid, radius, c0, cr)
    ensure(abs(d)+r < limit, "whole complex disk bound failed")
    return {"center": str(mid), "radius": str(radius),
            "real_left_intersection": str(w), "real_right_endpoint": str(q),
            "certified_G_disk_image_absolute_bound": str(limit),
            "certified_clearance_to_target_radius_1_over_4": str(Q(1, 4)-limit)}


def restrictions(q: Q, w: Q, source_cuts: list[Box], tleft: Box,
                 tright: Box, attachment_end: Box) -> list[list[int]]:
    """Circle/slit incidence, not a table of expected marked restrictions."""
    Qbox, Wbox = Box.rational(q), Box.rational(w)
    ensure(tleft.before(Qbox) and Qbox.before(tright), "q not on source slit")
    qs = (index_of(Qbox, 1, source_cuts), index_of(Qbox, -1, source_cuts))
    if Wbox.before(tleft):
        return [[qs[0], qs[1]]]
    ensure(Wbox.before(attachment_end) and tleft.before(Wbox),
           "left crossing is not in the new attachment")
    return [[qs[0], index_of(Wbox, 1, source_cuts)],
            [index_of(Wbox, -1, source_cuts), qs[1]]]


def recompute(example: dict, source: dict) -> dict:
    ensure(example["return"]["physical_iterate"] == 3, "wrong physical return time")
    ensure(example["return"]["restricted_degree"] == 2, "wrong central degree")
    ensure(example["domains"]["target"]["radius"] == "1/4", "wrong target disk")
    ensure(example["operations"]["covering"]["ideal_action"] == "f_*", "wrong cover")
    ensure(example["operations"]["immersion"]["ideal_action"] == "iota^*", "wrong immersion")
    ensure(example["operations"]["covering"]["ideal_action"] != example["operations"]["immersion"]["ideal_action"], "operations conflated")
    ensure(source["inner_root_exact_interval"] == "[x9,x18]", "root source drift")
    ensure("x18=-x9" in source["exact_orbit_relations"], "orbit identity missing")
    ensure(source["phase_intervals_pairwise_disjoint"] is True, "small Julia phase separation")
    phases = {a["physical_phase"]: a for a in source["phase_intervals"]}
    for k, val in ((0, "[x9,x18]"), (3, "[x12,x3]"), (6, "[x6,x15]")):
        ensure(phases[k]["exact_interval"] == val and phases[k]["coarse_phase"] == 0,
               "small Julia interval provenance drift")
    p = source["parameter_bracket"]
    den = 1 << p["denominator_power_of_two"]
    clo, chi = Q(p["lower_numerator"], den), Q(p["upper_numerator"], den)
    ensure(clo < chi, "parameter bracket invalid")
    c = Box(Box.rational(clo).low, Box.rational(chi).high)
    orbit = bracket(c)
    x = {"x"+str(k): t for k,t in enumerate(orbit)}
    x["alpha"] = isolate_alpha(c)
    ensure(x["x9"].overlaps(-x["x18"]), "phase root relation not consistent")
    ensure(x["x6"].before(x["x15"]) and x["x15"].before(x["x9"])
           and x["x9"].before(Box.rational(0)) and Box.rational(0).before(x["x18"])
           and x["x18"].before(x["alpha"]) and x["alpha"].before(x["x12"])
           and x["x12"].before(x["x3"]), "orbit and fixed-point order")
    ensure((-x["x3"]).before(x["x6"]), "attachment no longer exists")
    ensure(x["x3"].before(Box.rational(Q(1,4))), "native tree outside U3")
    # G' = 8z f(z) f²(z), so G increases on [-x3,0] and decreases on [0,x3].
    fbox = Box(0,x["x3"].high).square()+c
    f2box = fbox.square()+c
    ensure(fbox.high < 0 < f2box.low, "negative monotone branch uncertified")
    ensure(iterate3(-x["x3"],c).overlaps(x["x6"]), "tree preimage endpoint")
    ensure(iterate3(Box.rational(0),c).overlaps(x["x3"]), "critical return")
    t_symbols = example["marking"]["target_cuts"]
    ensure(t_symbols == ["x15","x9","x18","alpha","x12"], "marking source convention drift")
    target_cuts = [x[key] for key in t_symbols]
    ensure(all(a.before(b) for a,b in zip(target_cuts,target_cuts[1:])), "target cuts overlap")
    # Find all ten cut preimages by strict monotone bisection, instead of
    # supplying a twenty-entry atom map or any table from the old checker.
    candidates = []
    for name, target in zip(t_symbols,target_cuts):
        neg = isolate_negative_preimage(target,c,-x["x3"])
