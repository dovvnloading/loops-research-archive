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
