#!/usr/bin/env python3
"""Exact prime-end identification *analytic inputs*, not numerical prime ends.

Certifies an EXTRA quadratic-like restriction of (f_c^p)^3, p=3..12,
from the existing read-only dyadic tip brackets. Certifies the model bounds
for p>=13 by rational inequalities. The topological conclusion uses the
named straightening, PCF local-connectivity and Caratheodory/KKL theorems
spelled out in NOTE.md; integer arithmetic does NOT prove those theorems.
"""
from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINITE = HERE.parent / "real_primitive_tip_family_unconditional_20261116" / "results.json"
S = 1 << 512
TAIL_SCALE = 1 << 192
R = Q(3, 10)


def check(test: bool, reason: str) -> None:
    if not test:
        raise AssertionError(reason)


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        check(self.lo <= self.hi, "inverted outward interval")

    @classmethod
    def point(cls, value: Q | int) -> Interval:
        v = Q(value) * S
        return cls(v.numerator // v.denominator,
                   -((-v.numerator) // v.denominator))

    def __add__(self, other: Interval) -> Interval:
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> Interval:
        return Interval(-self.hi, -self.lo)

    def __mul__(self, other: Interval) -> Interval:
        candidates = (self.lo * other.lo, self.lo * other.hi,
                      self.hi * other.lo, self.hi * other.hi)
        return Interval(min(candidates) // S, -((-max(candidates)) // S))

    def square(self) -> Interval:
        low = (0 if self.lo <= 0 <= self.hi else
               min(self.lo * self.lo, self.hi * self.hi))
        return Interval(low // S,
                        -((-max(self.lo * self.lo, self.hi * self.hi)) // S))

    def abs_upper(self) -> Q:
        return Q(max(abs(self.lo), abs(self.hi)), S)

    def abs_lower(self) -> Q:
        if self.lo > 0:
            return Q(self.lo, S)
        if self.hi < 0:
            return Q(-self.hi, S)
        return Q(0)

    def before(self, other: Interval) -> bool:
        return self.hi < other.lo


def ceil_tail(value: Q) -> Q:
    check(value >= 0, "negative tail")
    z = value * TAIL_SCALE
    return Q(-((-z.numerator) // z.denominator), TAIL_SCALE)


def orbit_and_quadratic(c: Interval, n: int) -> tuple[list[Interval], list[Interval], list[Interval]]:
    """Full f^j(0), df^j(0)/dc, and [z^2] f^j(z), outward 2^-512."""
    zero, one, two = (Interval.point(k) for k in (0, 1, 2))
    x, deriv, coef = [zero], [zero], [zero]
    for k in range(1, n + 1):
        deriv.append(two * x[-1] * deriv[-1] + one)
        coef.append(one if k == 1 else two * x[-1] * coef[-1])
        x.append(x[-1].square() + c)
    return x, deriv, coef


def whole_disk_tail(x: list[Interval], a: list[Interval], n: int, radius: Q) -> Q:
    """All order >=4 Taylor terms, with exact upward 2^-192 rounding."""
    radius_sq = radius * radius
    tail = Q(0)
    for k in range(1, n + 1):
        tail = ceil_tail(2 * x[k - 1].abs_upper() * tail +
                         (a[k - 1].abs_upper() * radius_sq + tail) ** 2)
    return tail


def check_finite_row(row: dict) -> dict:
    p = row["p"]
    check(type(p) is int and 3 <= p <= 12, "period outside finite ledger")
    bracket = row["parameter_bracket"]
    check(bracket["unique_in_seed_window"] is True, "lost root uniqueness")
    check(bracket["denominator_power_of_two"] == 256, "wrong dyadic scale")
    low = bracket["lower_numerator"]
    high = bracket["upper_numerator"]
    check(type(low) is int and type(high) is int and high == low + 1,
          "parameter interval is not an adjacent dyadic bracket")
    a, b = Q(low, 1 << 256), Q(high, 1 << 256)
    check(-2 < a < b < -1, "parameter outside near-minus-two family")
    x, d, coef = orbit_and_quadratic(Interval(low << 256, high << 256), 6 * p)
    check((d[6*p] + d[3*p]).hi < 0, "not unique in the entire bracket")
    for c, direction in ((a, 1), (b, -1)):
        v, _, _ = orbit_and_quadratic(Interval.point(c), 6 * p)
        h = v[6*p] + v[3*p]
        check(h.lo > 0 if direction == 1 else h.hi < 0,
              "bracket endpoint does not have strict P sign")
    check((x[6*p] + x[3*p]).lo <= 0 <= (x[6*p] + x[3*p]).hi,
          "tip equality not enclosed")
    zero = Interval.point(0)
    check(x[p].lo > 0 and x[2*p].hi < 0 and x[3*p].hi < 0 and
          x[4*p].lo > 0 and x[5*p].hi < 0 and x[6*p].lo > 0,
          "wrong critical return itinerary")
    check(x[2*p].before(x[5*p]) and x[5*p].before(x[3*p]) and
          x[3*p].before(zero) and zero.before(x[6*p]) and
          x[6*p].before(x[4*p]) and x[4*p].before(x[p]),
          "strict phase order fails")
    A = coef[p]
    B = coef[3*p]
    check(A.hi < 0 and B.abs_lower() > 0, "critical quadratic terms vanish")
    abs_A_lo, abs_A_hi = A.abs_lower(), A.abs_upper()
    radius_hi, radius_lo = R / abs_A_lo, R / abs_A_hi
    physical_U = Q(1, 4) if p == 3 else Q(1, 2**p)
    check(radius_hi < physical_U, "three-return disk exceeds original U")
    tail_p = whole_disk_tail(x, coef, p, radius_hi)
    bound_G = x[p].abs_upper() + A.abs_upper() * radius_hi**2 + tail_p
    check(bound_G < physical_U, "three-return disk not inside central V")
    tail_3p = whole_disk_tail(x, coef, 3*p, radius_hi)
    # Uniform for |w|<=R: h^3(w) = A*f^(3p)(w/A).
    # Compare with the *exact* quadratic term (B/A)*w^2.
    dominant = abs_A_lo * B.abs_lower() * radius_lo**2
    perturb = abs_A_hi * (x[3*p].abs_upper() + tail_3p) + R
    margin = dominant - perturb
    check(abs_A_hi * x[3*p].abs_upper() < R, "critical value leaves H target")
    check(margin > Q(1, 8), "three-return Rouché gap <= 1/8")
    check(row["complex_phase_disks_pairwise_disjoint"] is True,
          "prior complex phase certificate missing")
    check(Q(row["central_degree_two_Rouche_margin_lower_2^-64"]) > 0,
          "prior original first-return Rouché margin missing")
    return {"p": p, "root_bracket": "adjacent 2^-256 with full negative derivative",
            "H_three_return_Rouche_margin_gt_1/8": True,
            "H_critical_value_inside_3/10": True,
            "H_disk_inside_original_V": True}


def check_all_finite(data: dict) -> list[dict]:
    check(data.get("schema") == "real-primitive-tip-unconditional-finite-interval/v1",
          "unexpected source certificate schema")
    rows = data.get("periods")
    check(isinstance(rows, list) and [row.get("p") for row in rows] == list(range(3, 13)),
          "missing, repeated, or unordered p=3..12")
    check(data.get("source_avoiding_short_arc_atoms") == 7 and
          data.get("cover_pushed_avoiding_short_arc_atoms") == 5,
          "source/covers short-arc correction was lost")
    return [check_finite_row(row) for row in rows]


def check_large_model() -> dict:
    """Universal p>=13 model proof, evaluated at worst q=4^-13."""
    q = Q(1, 4**13)
    t0, t1 = -Q(1795, 1000), -Q(1785, 1000)
    vmin, vmax = t1*t1 + t1, t0*t0 + t0
    check(Q(7, 5) < vmin < vmax < Q(10, 7), "quadratic second return bound")
    u3_lower = vmin**2 + t0
    u3_upper = vmax**2 + t1
    check(Q(0) < u3_lower < u3_upper < Q(13, 50) < R,
          "third return / critical value bound")
    beta = 4*abs(t1)*vmin
    check(beta > Q(99, 10), "quadratic coefficient B too small")
    check(2*vmax + 4*t0*t0 < 16, "quartic coefficient C too large")
    check(4*abs(t0) < 8, "sextic coefficient D too large")
    e1, e2, e3 = 88*q, 440*q, 1848*q
    check(abs(t0)+R*R + e1 < Q(19, 10), "first return leaves error disk")
    check(vmax + 2*abs(t0)*R**2 + R**4 + e2 < Q(9, 5),
          "second return leaves error disk")
    # e is valid for |w|<=21/10; both preceding complex orbit disks lie inside.
    remaining = u3_upper + 16*R**4 + 8*R**6 + R**8 + e3 + R
    margin = beta*R**2 - remaining
    check(margin > Q(1, 8), "uniform Rouché gap <= 1/8")
    # |A|>3/(20q), |h(w)|<19/10 on D_R; R_orig=2^-p.
    check(Q(19, 10)*Q(20, 3)*q < Q(1, 2**13),
          "normalized small disk fails to embed in original V")
    check(Q(20, 3)*R*q < Q(1, 2**13),
          "normalized source disk fails original U inclusion")
    return {"p": ">=13", "q_max": "4^-13",
            "H_three_return_Rouche_margin_gt_1/8": True,
            "H_critical_value_inside_3/10": True,
            "H_disk_inside_original_V": True}


def main() -> None:
    result = {"p3_to_p12": check_all_finite(json.loads(FINITE.read_text())),
              "p13_and_up": check_large_model(),
              "meaning": "full-disk arithmetic and discrete source constraints only; named topological theorems in NOTE.md"}
    print(json.dumps(result, sort_keys=True, indent=2))
    print("PASS: p>=3 nested 3-return degree-two Rouché with gap >1/8; source certificates unchanged")


if __name__ == "__main__":
    main()
