#!/usr/bin/env python3
"""Exact rational first Kahn--Lyubich tip-puzzle and obstruction audit.

Certifies finite interval inequalities, angular routing, and first-return
indices. Analytic ray landings, puzzle topology, the modified principal nest,
Levin's theorem, and Kahn's localization remain explicitly imported.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from verify_real_nested_3_9 import (
    Interval as GridInterval, ZERO, ONE, UNIT,
    parameter, orbit_and_derivative,
)
from verify_complex_quadratic_like_3_9 import evaluate_bounds
from verify_tip_complex_domains import U3, U9, SMALL9

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

    # SECOND KL top puzzle: degree-two polynomial-like G=f^3
    # has a real dividing fixed a in (3/32,1/10) with
    # G'(a)<-1 (standard real quadratic-like straightening).
    # Its symmetric preimage alpha'_G=-a, a positive b_G with
    # G(b_G)=-a, and central vertices ±t_G with G(t_G)=b_G.
    assert iterate(exact(F(3, 32)), 3).lo > F(3, 32)
    assert iterate(exact(F(1, 10)), 3).hi < F(1, 10)
    assert iterate(exact(F(17, 100)), 3).lo > -F(3, 32)
    assert iterate(exact(F(7, 40)), 3).hi < -F(1, 10)
    assert iterate(exact(F(1, 32)), 3).lo > F(7, 40)
    assert iterate(exact(F(1, 16)), 3).hi < F(17, 100)
    assert orbit[3].lo > F(1, 16)
    assert orbit[6].hi < -F(1, 10)
    assert -F(1, 32) < orbit[9].lo <= orbit[9].hi < F(1, 32)

    # Three consecutive IVT inverse branches of g=f^3.
    # Existence is proved analytically by the strict *exact* signs.
    assert iterate(exact(1), 3).hi < 0
    assert iterate(exact(F(17, 16)), 3).lo > 0
    assert iterate(exact(F(6, 5)), 3).hi < 1
    assert iterate(exact(F(49, 40)), 3).lo > F(17, 16)
    assert iterate(exact(F(31, 25)), 3).hi < F(6, 5)
    assert iterate(exact(F(5, 4)), 3).lo > F(49, 40)

    # The independently audited 2^-224 phase-disk bounds show the
    # first preimage is outside B3 and the third is outside B9.
    pl, ph = parameter(TIP_K), parameter(TIP_K + 1)
    physical = GridInterval(pl.lo, ph.hi)
    stages, _ = orbit_and_derivative(physical, 18)
    coefs = [ZERO, ONE]
    for j in range(1, 9):
        coefs.append(stages[j] * coefs[j].times(2))
    bound3 = evaluate_bounds(stages, coefs, U3, 3)
    bound9 = evaluate_bounds(stages, coefs, SMALL9, 9)
    bound_inner = evaluate_bounds(stages, coefs, U9, 9)
    assert stages[3].lo - bound_inner.deviation[3] > 7*UNIT//40
    # All G^2-central preimages of alpha_G consist of ±a, ±b_G,
    # bounded by |b_G|<7/40. Hence no G^3 alpha_G vertex is
    # in U9, since Re G(U9)>7/40 by the previous strict test.


    def misses_all_phase_disks(
        start: int, upper: int, count: int, bounds
    ) -> bool:
        return all(
            stages[j].hi + bounds.deviation[j] < start
            or upper < stages[j].lo - bounds.deviation[j]
            for j in range(count)
        )
    assert misses_all_phase_disks(UNIT, 17*UNIT//16, 3, bound3)
    assert misses_all_phase_disks(31*UNIT//25, 5*UNIT//4, 9, bound9)

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

    # Stronger source-level obstruction: actual z*=31/1024 lies
    # in I3 ⊂ B3 but outside *every* physical phase of B9.
    # Reuse the independently certified exact signed-dyadic majorants
    # rather than substituting numerical Julia plots.
    from verify_real_nested_3_9 import (
        Interval as DyadicInterval, ZERO, ONE, UNIT, parameter,
        orbit_and_derivative,
    )
    from verify_complex_quadratic_like_3_9 import evaluate_bounds
    from verify_period27_misiurewicz_tip import TIP_K as EXACT_TIP_K
    assert EXACT_TIP_K == TIP_K
    tip_c_lo, tip_c_hi = parameter(TIP_K), parameter(TIP_K + 1)
    tip_interval = DyadicInterval(tip_c_lo.lo, tip_c_hi.hi)
    X, _ = orbit_and_derivative(tip_interval, 18)
    A = [ZERO, ONE]
    for j in range(1, 9):
        A.append(X[j] * A[j].times(2))
    shrink_r = 27 * UNIT // 1024
    phase = evaluate_bounds(X, A, shrink_r, 9)
    z = 31 * UNIT // 1024
    assert shrink_r < z < UNIT // 32
    assert X[6].hi < z < X[3].lo
    assert all(X[j].hi + phase.deviation[j] < z
               or z + phase.deviation[j] < X[j].lo
               for j in range(1, 9))

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
        "outer_g3_fixed_a_bracket": ["3/32", "1/10"],
        "second_level_kl_puzzle": {
            "quadratic_like_map": "G=f^3:V3->U3, one return unit = 3 physical iterates",
            "alpha_G_dividing_real_bracket": ["3/32", "1/10"],
            "alpha_prime_G": "-alpha_G",
            "positive_offcritical_preimage_b_G_bracket": ["17/100", "7/40"],
            "central_vertex_t_G_bracket": ["1/32", "1/16"],
            "escape_clock_q_n": [2, 1],
            "source_piece_depths": [1, 3, 3],
            "first_critical_return_under_G": 3,
            "physical_return": 9
        },
        "extra_preimage_r_bracket": ["1", "17/16"],
        "extra_preimage_nested_three_brackets": [
            ["1", "17/16"], ["6/5", "49/40"], ["31/25", "5/4"]
        ],
        "phase_disk_avoidance": {
            "f3_inverse_component": "all three f^j(V3) avoid (1,17/16)",
            "f9_inverse_component": "all nine f^j(V9) avoid (31/25,5/4)"
        },
        "source_angular_pairs": {k:[str(x) for x in v] for k,v in rays.items()},
        "scope": "Exact rational inequalities and angular routing; actual landing/puzzle topology, KL localization and interscale naturality require separately named analytic inputs",
    }


if __name__ == "__main__":
    print(certify()["status"])
