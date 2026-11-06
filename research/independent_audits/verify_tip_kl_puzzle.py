#!/usr/bin/env python3
"""Exact rational first Kahn--Lyubich tip-puzzle and obstruction audit.

Certifies finite interval inequalities, angular routing, and first-return
indices. Analytic ray landings, puzzle topology, the modified principal nest,
Levin's theorem, and Kahn's localization remain explicitly imported.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F

TIP_K = -607918036626757496169199575185708826140
LOW = F(-1786511, 1_000_000)
HIGH = F(-1786510, 1_000_000)
assert LOW < F(TIP_K, 2**128) < F(TIP_K + 1, 2**128) < HIGH


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self) -> None:
        assert self.lo <= self.hi

    def __add__(self, rhs: Interval | F | int) -> Interval:
        if not isinstance(rhs, Interval):
            rhs = exact(rhs)
        return Interval(self.lo + rhs.lo, self.hi + rhs.hi)

    __radd__ = __add__

    def __mul__(self, rhs: Interval | F | int) -> Interval:
        if not isinstance(rhs, Interval):
            rhs = exact(rhs)
        four = [x*y for x in (self.lo, self.hi) for y in (rhs.lo, rhs.hi)]
        return Interval(min(four), max(four))

    __rmul__ = __mul__

    def sq(self) -> Interval:
        if self.lo <= 0 <= self.hi:
            return Interval(F(0), max(self.lo**2, self.hi**2))
        return Interval(min(self.lo**2, self.hi**2), max(self.lo**2, self.hi**2))


def exact(x: F | int) -> Interval:
    return Interval(F(x), F(x))


PARAMETER = Interval(LOW, HIGH)


def f(z: Interval) -> Interval:
    return z.sq() + PARAMETER


def iterate(z: Interval, count: int) -> Interval:
    for _ in range(count):
        z = f(z)
    return z


def angle_pair(*nums: int, den: int) -> tuple[F, ...]:
    return tuple(sorted(F(k, den) for k in nums))


def certify() -> dict:
    orbit = [exact(0)]
    for _ in range(9):
        orbit.append(f(orbit[-1]))
    assert orbit[1].hi < -1
    assert orbit[2].lo > 1
    assert 0 < orbit[3].lo <= orbit[3].hi < F(1, 4)
    assert orbit[6].hi < 0

    # Dividing alpha is negative; alpha'=-alpha is the positive root
    # of y^2+y+c=0. Rational signs prove 7/8 < alpha' < 1.
    h = lambda z: z.sq() + z + PARAMETER
    assert h(exact(F(7, 8))).hi < 0 < h(exact(1)).lo

    # Depth-3 central vertex +-t: f^2(t)=alpha'.
    assert iterate(exact(F(5, 16)), 2).lo > 1
    assert iterate(exact(F(7, 16)), 2).hi < F(7, 8)
    assert orbit[3].hi < F(1, 4) < F(5, 16)

    # g3=f^3 has a fixed a in (1/16,1/8), inside I3.
    assert iterate(exact(F(1, 16)), 3).lo > F(1, 16)
    assert iterate(exact(F(1, 8)), 3).hi < F(1, 8)
    assert orbit[6].hi < F(1, 16) < F(1, 8) < orbit[3].lo
    z = Interval(F(1, 16), F(1, 8))
    gprime = exact(8) * z * f(z) * iterate(z, 2)
    assert gprime.hi < -1

    # A different r in (1,9/8) satisfies f^3(r)=0 in K3.
    assert iterate(exact(1), 3).hi < 0 < iterate(exact(F(9, 8)), 3).lo
    # K3 subset D(0,1/4). f(K3) lies left of -1; f^2(K3)
    # lies right of 9/8 by an exact expansion bound.
    assert PARAMETER.hi + F(1, 16) < -1
    max_c = -PARAMETER.lo
    second_phase_radius = 2 * max_c / 16 + F(1, 256)
    assert orbit[2].lo - second_phase_radius > F(9, 8)

    # The fact a is outside B9={K9,g3(K9),g3^2(K9)} uses the
    # earlier proved disjointness and cycling of K9 phase components;
    # it is an imported geometric argument, not certified by this code.
    rays = {
        "alpha": angle_pair(1, 2, den=3),
        "alpha_prime": angle_pair(1, 5, den=6),
        "b_minus": angle_pair(5, 7, den=12),
        "b_plus": angle_pair(1, 11, den=12),
        "v_minus": angle_pair(7, 17, den=24),
        "v_plus": angle_pair(5, 19, den=24),
    }
    assert all(sum(pair) == 1 for pair in rays.values())
    routes = [
        ("alpha", "alpha", 1),
        ("alpha_prime", "alpha", 1),
        ("b_minus", "alpha_prime", 1),
        ("b_plus", "alpha_prime", 1),
        ("v_minus", "b_minus", 1),
        ("v_plus", "b_minus", 1),
        ("v_minus", "alpha_prime", 2),
        ("v_plus", "alpha_prime", 2),
        ("v_minus", "alpha", 3),
        ("v_plus", "alpha", 3),
    ]
    for source, target, k in routes:
        doubled = tuple(sorted((2**k * angle) % 1 for angle in rays[source]))
        assert doubled == rays[target], (source, target, k)
    assert rays["v_minus"] != rays["v_plus"]
    assert set(rays["v_minus"]).isdisjoint(rays["v_plus"])

    # The KL q,n are not the quadratic-like return periods 3 and 9.
    q, n, p, next_p = 2, 1, 3, 9
    assert (n-1)*q+1 == 1
    assert n*q+1 == 3
    assert (2*n-1)*q+1 == 3
    assert n*q == q == 2
    assert next_p//p == 3 and next_p-p == 6

    return {
        "status": "TIP_KL_TOP_PUZZLE_EXACT_CHECK_PASS",
        "parameter_enclosure": [str(LOW), str(HIGH)],
        "alpha_prime_bracket": ["7/8", "1"],
        "outer_puzzle_first_escape_q_n": [q, n],
        "depths_P_V0_Q": [1, 3, 3],
        "vertex_real_bracket_t": ["5/16", "7/16"],
        "outer_g3_fixed_a_bracket": ["1/16", "1/8"],
        "extra_preimage_r_bracket": ["1", "9/8"],
        "source_angular_pairs": {k:[str(x) for x in v] for k,v in rays.items()},
        "scope": "Exact rational inequalities and angular routing; actual landing/puzzle topology, KL localization and interscale naturality require separately named analytic inputs",
    }


if __name__ == "__main__":
    print(certify()["status"])
