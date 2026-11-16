#!/usr/bin/env python3
"""Exact/interval checks for the marked-Wave sandwich, not a proof checker.

The topological inclusions and the extremal-length periodization argument are
proved in NOTE.md.  This script rechecks their finite arithmetic hypotheses,
including four new high-period root isolations; all arithmetic is Fraction and
outward 2^-512 intervals from the existing (unchanged) canonical-width core.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CORE = ROOT / "research/independent_audits/real_primitive_tip_family_canonical_width_20261116/verify.py"
OLD = ROOT / "research/independent_audits/real_primitive_tip_family_unconditional_20261116/results.json"
PRIOR = CORE.with_name("results.json")
RESULT = HERE / "results.json"

# Import the pinned arithmetic implementation, not its claimed Wave inclusions.
spec = importlib.util.spec_from_file_location("canonical_width_interval_core", CORE)
assert spec is not None and spec.loader is not None
v = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = v
spec.loader.exec_module(v)

BLOCKS = (
    (18, 19, 0, 1, 2), (3, 4), (5,), (6,), (7, 8, 9),
    (10,), (11, 12, 13), (14,), (15,), (16, 17),
)
CROSSING = ((3, 1), (19, 17))
AVOIDING = (3, 17)
LIMIT_RADIAL_LOW = Q(2604925, 10**7)
LIMIT_PLANE_HIGH = Q(7749233, 10**7)


def check(ok: bool, why: str) -> None:
    if not ok:
        raise AssertionError(why)


def cyclic_span(pair: tuple[int, int], n: int) -> int:
    a, b = pair
    check(0 <= a < n and 0 <= b < n and a != b, "invalid source atoms")
    d = (a - b) % n
    return 1 + min(d, n-d)


def check_marking() -> dict:
    flat = sum((tuple(b) for b in BLOCKS), ())
    check(len(flat) == 20 and set(flat) == set(range(20)), "missing or overlapping immersion atoms")
    block_of = {a: j for j, block in enumerate(BLOCKS) for a in block}
    check(all(cyclic_span(pair, 20) == 3 for pair in CROSSING), "A.1 crossing shortness")
    check(cyclic_span(AVOIDING, 20) == 7, "avoiding source shortness != 7")
    check(all(block_of[a] != block_of[b] for a, b in CROSSING),
          "immersion pullback discarded a crossing child")
    check(all(cyclic_span((a % 10, b % 10), 10) == 3 for a, b in CROSSING),
          "covering pushforward shortness")
    check(cyclic_span(tuple(a % 10 for a in AVOIDING), 10) == 5,
          "avoiding covering shortness != 5")
    check({block_of[1], block_of[19]} == {0}, "nonproper immersion block drift")
    return {
        "A1_parent_base": [9, 0, 1],
        "A1_crest": 0,
        "source_crossing_spans": [3, 3],
        "source_avoiding_span": 7,
        "cover_crossing_endpoints": [[3, 1], [9, 7]],
        "cover_avoiding_endpoints": [3, 7],
        "cover_crossing_spans": [3, 3],
        "cover_avoiding_span": 5,
        "crossing_children_in_distinct_immersion_blocks": True,
        "covering_is_not_immersion": True,
    }


def p_value(c: Q, p: int) -> v.Iv:
    x, _ = v.poly_orbit(v.Iv.point(c), 6*p)
    return x[6*p] + x[3*p]


def tau_at(c: Q, p: int) -> v.Iv:
    """Normalized chart coordinate at one rational parameter point."""
    x, _ = v.poly_orbit(v.Iv.point(c), p)
    A = v.Iv.point(1)
    for j in range(1, p):
        A = A*v.TWO*x[j]
    return A*x[p]


def invert_tau(p: int, target: Q) -> tuple[Q, Q]:
    """Bracket a target tau-level without assuming monotonicity outside chart.

    On every bisection step the one-point interval establishes which side of
    target holds; this method is not a root-isolation proof until certify_tip
    checks the final parameter hull and the itinerary.
    """
    q = Q(1, 4**p)
    lo, hi = -2 + Q(148, 10)*q, -2 + Q(149, 10)*q
    check(tau_at(lo, p).high() < target < tau_at(hi, p).low(),
          f"p={p}: normalized chart seed does not straddle {target}")
    for _ in range(110):
        mid = (lo + hi)/2
        t = tau_at(mid, p)
        if t.high() < target:
            lo = mid
        elif t.low() > target:
            hi = mid
        else:
            raise AssertionError(f"p={p}: ambiguous tau bisection")
    return lo, hi


def certify_tip(p: int) -> tuple[v.Iv, list[v.Iv]]:
    """New exact chart-based bisection, full-hull derivative, p=13..16.

    Locates the unique root within tau in (-1.795,-1.785).  A broad
    P_p sign bracket alone is NOT sufficient: P_p has other roots.
    """
    check(13 <= p <= 16, "period is outside individual high-period certificates")
    q = Q(1, 4**p)
    lo, _ = invert_tau(p, v.MODEL_LO)
    _, hi = invert_tau(p, v.MODEL_HI)
    check(lo < hi, "inverted chart")
    check(p_value(lo, p).positive() and p_value(hi, p).negative(),
          f"p={p}: distinguished root endpoint signs")
    for _ in range(200):
        mid = (lo + hi)/2
        s = p_value(mid, p)
        if s.positive():
            lo = mid
        elif s.negative():
            hi = mid
        else:
            raise AssertionError(f"p={p}: ambiguous P midpoint")
    c = v.Iv.hull(lo, hi)
    x, dx = v.poly_orbit(c, 6*p, derivative=True)
    P = x[6*p] + x[3*p]
    check(P.lo < 0 < P.hi, f"p={p}: parameter root not enclosed")
    check((dx[6*p]+dx[3*p]).negative(), f"p={p}: full-hull transversality")
    check(v.Iv.point(-2+14*q).lt(c) and c.lt(v.Iv.point(-2+16*q)),
          f"p={p}: not in analytic chart")
    check(x[1].negative() and all(x[j].positive() for j in range(2, p+1)),
          f"p={p}: prefix itinerary")
    check(x[p].high() < 14*q, f"p={p}: central chart bound")
    for j, sign in enumerate((1, -1, -1, 1, -1, 1), 1):
        check(x[j*p].positive() if sign > 0 else x[j*p].negative(),
              f"p={p}: signed return j={j}")
    A = v.Iv.point(1)
    for j in range(1, p):
        A = A*v.TWO*x[j]
    tau = A*x[p]
    check(A.negative() and tau.inside(v.MODEL_LO, v.MODEL_HI),
          f"p={p}: not the distinguished normalized root")
    return c, x

def finite_case(p: int, c: v.Iv, x: list[v.Iv], pi: v.Iv) -> dict:
    alpha = v.alpha_interval(p, c, x)
    xp, x2, x5, x3, x4 = (x[j*p] for j in (1, 2, 5, 3, 4))
    check(x2.lt(x5) and x5.lt(x3) and x3.negative(), "target slit order")
    check(v.ZERO.lt(x[6*p]) and x[6*p].lt(alpha) and alpha.lt(x4) and x4.lt(xp),
          "target fixed point / cuts")
    check((-xp).lt(-x4) and (-x4).lt(x2) and x5.lt(-alpha)
          and (-alpha).lt(x3), "source crossing gate and marking order")
    ratio, radial, margin = v.radial_data(p, c, x, alpha, pi)
    R = Q(1, 4) if p == 3 else Q(1, 2**p)
    full_lo, full_hi, plane = v.bound_for_finite_disk(xp, x2, x5, x3, R, pi)
    check(radial.lt(full_hi) and full_hi.lt(plane), "ordered witnesses/envelopes")
    check(margin.low() > Q(2, 5)*R, "whole gate disk not in central source")
    if p >= 13:
        check(radial.low() > Q(26, 100) and full_hi.high() < Q(78, 100),
              f"p={p}: first high periods not inside (0.26,0.78)")
    return {
        "p": p,
        "round_lower_1e-7_strict": v.bracket_dec(radial),
        "full_lift_upper_1e-7_strict": v.bracket_dec(full_hi),
        "plane_full_lift_upper_1e-7_strict": v.bracket_dec(plane),
        "whole_gate_disk_margin_gt_2_5_of_R": True,
    }


def pad(z: v.Iv, e: Q) -> v.Iv:
    check(e >= 0, "negative interval error")
    return v.Iv.hull(z.low()-e, z.high()+e)


def model_plane_envelope(p: int, u: list[v.Iv]) -> v.Iv:
    """Upper enclosure for ALL p>=13, by the all-p normalized-orbit error.

    Let xi_j=-A_p*x_(jp)=-h_p^j(0).  Since A_p<0, this is a positive
    affine scaling of the physical plane slit; conformal width is unchanged.
    """
    check(isinstance(p, int) and p >= 13, "out of model perturbation regime")
    q = Q(1, 4**p)
    errors = {1: Q(15246)}
    for j in (2, 3, 5):
        errors[j] = Q(30*15246) + Q(88*(4**j-1), 3)
    coordinates = {j: -pad(u[j], errors[j]*q) for j in (1, 2, 3, 5)}
    upper, _, _, _ = v.infinite_envelope_for_cuts(
        coordinates[1], coordinates[2], coordinates[5], coordinates[3])
    return upper


def run() -> dict:
    marking = check_marking()
    old = json.loads(OLD.read_text())
    recomputed = v.run(old)
    check(recomputed == json.loads(PRIOR.read_text()),
          "previous finite arithmetic snapshot has drifted")
    check(recomputed["model_limit_radial_width_1e-7_strict"] == [2604925, 2604928],
          "radial limit enclosure drift")
    check(recomputed["model_limit_full_path_upper_envelope_1e-7_strict"] ==
          [7749230, 7749233], "plane limit enclosure drift")
    check(recomputed["large_p_radial_result"]["radial_width_difference_bound"] ==
          "7000000*4^(-p)", "all-p radial rate drift")
    pi = v.pi_interval()
    finite = []
    for source in old["periods"]:
        p, c, x = v.checked_packet(source)
        finite.append(finite_case(p, c, x, pi))
    for p in range(13, 17):
        c, x = certify_tip(p)
        finite.append(finite_case(p, c, x, pi))
    t, u = v.isolate_model()
    check(t.inside(v.MODEL_LO, v.MODEL_HI), "wrong limiting root")
    model_13 = model_plane_envelope(13, u)
    model_14 = model_plane_envelope(14, u)
    model_15 = model_plane_envelope(15, u)
    model_17 = model_plane_envelope(17, u)
    check(model_13.high() < Q(1), "p13 model plane envelope outside analytic regime")
    check(model_14.high() < Q(1), "p14 model plane envelope outside analytic regime")
    check(model_15.high() < Q(1), "p15 model plane envelope outside analytic regime")
    check(model_17.high() < Q(78, 100), "tail plane envelope excessive")
    check(LIMIT_RADIAL_LOW-Q(7_000_000, 4**17) > Q(26,100),
          "rate does not give >0.26 from p17")
    check(LIMIT_RADIAL_LOW < Q(2604928,10**7) and LIMIT_PLANE_HIGH < Q(78,100),
          "limit strict enclosures inconsistent")
    return {
        "schema": "real-primitive-tip-canonical-wave-sandwich/v1",
        "scope": "finite arithmetic and conditional analytic KKL curve inclusions; NOT a computation of W_p*",
        "arithmetic": "rational and outward 2^-512; old dyadic packets rechecked; new p13..16 roots independently bisected",
        "marking": marking,
        "finite": finite,
        "all_p_ge_13": {
            "round_lower_formula_strict": "2604925/10000000 - 7000000/4^p < W_p^rad <= W_p*",
            "full_lift_upper_formula": "W_p* <= Q_p <= Q_plane(p) <= model_plane_envelope(p)",
            "model_plane_envelope_13_1e-7_strict": v.bracket_dec(model_13),
            "model_plane_envelope_14_1e-7_strict": v.bracket_dec(model_14),
            "model_plane_envelope_15_1e-7_strict": v.bracket_dec(model_15),
            "model_plane_envelope_17_1e-7_strict": v.bracket_dec(model_17),
            "for_p_ge_17": "0.26 < W_p* < 0.78 (using enclosing model p=17 box)",
        },
        "limits": {
            "round_lower_1e-7_strict": [2604925,2604928],
            "plane_upper_1e-7_strict": [7749230,7749233],
            "deduction": "0.26 < liminf W_p* <= limsup W_p* < 0.78",
            "convergence_of_W_p_star": "OPEN: requires two-sided continuity/compactness of maximal admissible KKL Wave class",
        },
        "logical_scope": {
            "prime_end_marking": "cited slit/prime-end identification, not proved by Python",
            "parent_wave_A1": "proved in NOTE.md, not executable",
            "immersion_A3_2": "set-valued restriction only, not an extra A1 parent condition",
            "covering_A3_1": "S_j maps to I_(j mod 10), separate from immersion",
            "upper_periodization": "proved by an l2 pushdown of covering-strip conformal metrics in NOTE.md",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true",
                        help="explicitly replace new-only snapshot after review")
    parser.add_argument("--report", action="store_true",
                        help="print a provisional result without comparing snapshot")
    opts = parser.parse_args()
    data = run()
    rendered = json.dumps(data, indent=2, sort_keys=True, ensure_ascii=True)+"\n"
    if opts.write:
        RESULT.write_text(rendered)
    elif not opts.report:
        check(RESULT.read_text() == rendered, "new results drift: run --write only after review")
    if opts.report:
        print(rendered)
    else:
        print("canonical-width sandwich: finite periods 3..16, tail and marking checks PASS")


if __name__ == "__main__":
    main()
