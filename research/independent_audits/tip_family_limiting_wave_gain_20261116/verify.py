#!/usr/bin/env python3
"""Outward-rational certificate for a *strict* independently optimized Wave gain.

The analytic statements (Schwarz--Christoffel, foliation, KKL markings,
exhaustion) are in NOTE.md and are NOT Python theorems.  This checker tests
their exact rational consequences, dependencies, and all-p chart boxes.
No floats, optimizer, sampled curve, or numerical-only premise is used.
"""
from __future__ import annotations

import importlib.util
import math
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
UPSTREAM = ROOT / "research/independent_audits/tip_family_canonical_wave_gain_20261116/verify.py"

spec = importlib.util.spec_from_file_location("tip_limit_upstream_gain", UPSTREAM)
if spec is None or spec.loader is None:
    raise RuntimeError("Cannot import pinned canonical gain verifier")
gain = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = gain
spec.loader.exec_module(gain)
v = gain.v
I = v.Iv
ONE, TWO = v.ONE, v.TWO
RADIUS = F(5, 2)
PARENT_TAIL_FLOOR = F(2, 3)
CHILD_TAIL_CEILING = F(63, 50)
TAIL_GAIN_FLOOR = F(11, 126)


def require(ok: bool, msg: str) -> None:
    if not ok:
        raise AssertionError(msg)


def model_positive_boxes(period: int, orbit: list[I]) -> dict[int, I]:
    """xi_j=(-A_p)x_{jp}=-u_j+error, *positive* scale (-A_p)>0.

    This is precisely (5.3) of the predecessor sandwich, not a claim
    that the negative A_p normalization preserves the real cut order.
    """
    require(type(period) is int and period >= 13, "all-p box starts at 13")
    q = F(1, 4**period)
    coefficients = {1: F(15246)}
    for j in (2, 3, 5):
        # The factor 1/3 applies only to the accumulated iterate error.
        # Equation (5) of NOTE.md and the upstream sandwich both retain
        # the full parameter-error term 30*15246.
        coefficients[j] = F(30 * 15246) + F(88 * (4**j - 1), 3)
    return {j: -gain.pad(orbit[j], coefficients[j] * q)
            for j in (1, 2, 3, 5)}


def certified_period13_boxes() -> dict[int, I]:
    """Actual p=13 cuts, independently isolated in the signed chart.

    The corrected uniform p=13 error box is too wide to prove the
    claimed parent floor.  The existing exact root/derivative/itinerary
    certificate supplies a separate finite case; no decimal seed is
    accepted as a root or substituted for the actual iterate.
    """
    _, orbit = gain.s.certify_tip(13)
    A = ONE
    for j in range(1, 13):
        A = A * TWO * orbit[j]
    require(A.negative(), "p13 physical scaling needs A_p<0")
    return {j: (-A) * orbit[13*j] for j in (1, 2, 3, 5)}


def parent_angle_data(x1: I, x2: I, x5: I, x3: I) -> tuple[I, I, I, I]:
    """Joukowski left-tip electrodes; cos(a)=(m-x5)/r, cos(b)=(m-x3)/r."""
    require(x2.lt(x5) and x5.lt(x3) and x3.lt(x1),
            "physical parent slit cut order")
    m = (x2 + x1) / TWO
    r = (x1 - x2) / TWO
    require(r.positive(), "degenerate target slit")
    ca = (m - x5) / r
    cb = (m - x3) / r
    require(cb.positive() and ca.gt(cb) and ca.lt(ONE),
            "parent left-tip angle chart invalid")
    a = v.arccos_pos(ca)
    b = v.arccos_pos(cb)
    require(a.positive() and a.lt(b), "parent electrodes not separated")
    return a, b, ca, cb


def symmetric_quad_width(A: I, B: I) -> I:
    """SC width in the half-plane, boundary electrodes [-B,-A],[A,B]."""
    require(A.positive() and A.lt(B), "symmetric electrodes overlap")
    k = (B - A) / (B + A)
    require(k.positive() and k.lt(ONE), "bad symmetric cross-ratio")
    return v.upper_envelope_elliptic(k)


def parent_semidisk_width(x1: I, x2: I, x5: I, x3: I,
                          radius: F = RADIUS) -> I:
    """CERTIFIED competitor, not a bound on arbitrary leaves.

    In the selected log lift take the right semidisk Re(z)>0, |z|<R.
    The conformal map 2Rz/(R^2-z^2) takes it to a right half-plane;
    the boundary angle t is sent to 2Rt/(R^2+t^2).
    Its SC rectangle foliation projects injectively because R<pi.
    """
    require(radius > 0 and I.point(radius).lt(v.pi_interval()),
            "semidisk must be strictly below pi")
    a, b, _, _ = parent_angle_data(x1, x2, x5, x3)
    RR = I.point(radius)
    require(b.lt(RR), "parent electrode outside bounded semidisk")
    def boundary(t: I) -> I:
        return TWO * RR * t / (RR.square() + t.square())
    return symmetric_quad_width(boundary(a), boundary(b))


def parent_halfstrip_width(x1: I, x2: I, x5: I, x3: I) -> I:
    """Limiting right half-strip |Im z|<pi via sinh(z/2).

    Boundary values sin(a/2), sin(b/2) are obtained algebraically as
    sqrt((1-cos(a))/2), avoiding any numerical trigonometry.
    """
    _, _, ca, cb = parent_angle_data(x1, x2, x5, x3)
    return symmetric_quad_width(((ONE - ca) / TWO).sqrt(),
                                ((ONE - cb) / TWO).sqrt())


def child_halfstrip_width(x1: I, x2: I, x5: I, x4: I, alpha: I) -> I:
    """Limiting source upper half-strip 0<Im z<pi via cosh(z).

    The map sends the four electrodes to algebraic cosines. The
    lower child is its complex conjugate, with identical width.
    """
    require(x1.positive() and x2.negative() and x5.negative()
            and x4.positive() and alpha.positive(), "source cut signs")
    A = x4 / x1
    B = (-x2) / x1
    C = (-x5) / x1
    D = alpha / x1
    require(ONE.gt(A) and A.gt(B) and B.gt(C) and C.gt(D)
            and D.positive(), "wrong source four-electrode order")
    k2 = (A - B) * (C - D) / ((A - C) * (B - D))
    require(k2.positive() and k2.lt(ONE), "source strip cross-ratio invalid")
    return v.upper_envelope_elliptic(k2.sqrt())


def disk_cutoff_certificate(x: dict[int, I]) -> None:
    """Entire semidisk projects inside U_p for all p>=13, not sampled leaves."""
    m = (x[1] + x[2]) / TWO
    r = (x[1] - x[2]) / TWO
    require(m.inside(-2, 2) and r.inside(0, 2),
            "all-period target normalization too large for disk cutoff")
    require(I.point(RADIUS).lt(v.pi_interval()), "R must lie strictly below pi")
    z = F(5, 2)
    # e^(5/2) < truncated series plus a geometric tail:
    # for terms starting at n=21, the subsequent ratio <= (5/2)/22 < 1/2.
    series = sum((z**n / math.factorial(n) for n in range(21)), F(0))
    tail = 2 * z**21 / math.factorial(21)
    require(series + tail < 13, "exp(5/2) rational majorant failed")
    # |J(-exp(z))| <= |m| + r/2 (exp(Re(z))+exp(-Re(z)))
    #                 < 2 + (2/2)(13+1) = 16.
    # The all-p theorem gives (-A_p) R_p > (3/20) 2^p >= 1228.8.
    require(F(3, 20) * 2**13 > 16,
            "scaled finite target disk does not contain the whole competitor")


def strict_brackets(label: str, z: I, a: F, b: F) -> None:
    require(z.inside(a, b),
            f"{label}: outward interval fails proposed strict bracket "
            f"({z.low()}, {z.high()})")


def certify() -> dict[str, object]:
    # Re-run the *complete* predecessor: real finite periods, separate
    # immersion/cover incidence, original sandwich packets, and E_coarse.
    predecessor = gain.run()
    require(predecessor["p_ge_13"]["child_full_plane_upper_strict"]
            == str(CHILD_TAIL_CEILING), "upstream tail child cap changed")
    require(gain.s.BLOCKS[0] == (18, 19, 0, 1, 2)
            and gain.s.BLOCKS[1] == (3, 4)
            and gain.s.BLOCKS[9] == (16, 17), "immersion marking drift")
    tau, orbit = v.isolate_model()
    require(tau.inside(v.MODEL_LO, v.MODEL_HI),
            "distinguished model parameter not isolated")
    alpha_t = (ONE - (ONE - I.point(4) * tau).sqrt()) / TWO
    require(alpha_t.inside(F(-1), F(-4, 5)),
            "selected (negative-w) model fixed point changed")

    # Limiting positive coordinate xi=(-A_p) z: xi_j = -u_j.
    x = {j: -orbit[j] for j in (1, 2, 3, 4, 5)}
    alpha = -alpha_t
    p_low = parent_halfstrip_width(x[1], x[2], x[5], x[3])
    p_high, _, _, _ = v.infinite_envelope_for_cuts(
        x[1], x[2], x[5], x[3])
    c_low = child_halfstrip_width(
        x[1], x[2], x[5], x[4], alpha)
    c_high = gain.sharp_child_plane(
        x[1], x[2], x[5], x[4], alpha)
    require(p_low.lt(p_high) and c_low.lt(c_high),
            "strip competitor and full-lift ordering invalid")
    strict_brackets("limit parent half-strip", p_low,
                    F(752754, 10**6), F(752757, 10**6))
    strict_brackets("limit parent full-lift", p_high,
                    F(774922, 10**6), F(774925, 10**6))
    strict_brackets("limit child half-strip", c_low,
                    F(960197, 10**6), F(960201, 10**6))
    strict_brackets("limit child full-lift", c_high,
                    F(987646, 10**6), F(987650, 10**6))
    defect_lower = TWO / c_high - ONE / p_low
    defect_upper = TWO / c_low - ONE / p_high
    require(defect_lower.low() > F(696, 1000)
            and defect_upper.high() < F(793, 1000),
            "limiting positive defect enclosure failed")

    # Keep the full cited errors.  Their p=13 box does NOT certify >2/3;
    # isolate that physical tip separately, then use p=14 for the tail.
    boxes14 = model_positive_boxes(14, orbit)
    for p in (15, 17, 64):
        smaller = model_positive_boxes(p, orbit)
        require(all(boxes14[j].low() <= smaller[j].low()
                    and smaller[j].high() <= boxes14[j].high()
                    for j in (1, 2, 3, 5)),
                "normalized all-period error boxes not nested")
    disk_cutoff_certificate(boxes14)
    p_tail_disk = parent_semidisk_width(
        boxes14[1], boxes14[2], boxes14[5], boxes14[3])
    strict_brackets("all p>=14 parent semidisk",
                    p_tail_disk, PARENT_TAIL_FLOOR, F(3, 4))

    physical13 = certified_period13_boxes()
    disk_cutoff_certificate(physical13)
    p13_disk = parent_semidisk_width(
        physical13[1], physical13[2], physical13[5], physical13[3])
    strict_brackets("actual p=13 parent semidisk",
                    p13_disk, PARENT_TAIL_FLOOR, F(3, 4))
    p_disk = I.hull(min(p13_disk.low(), p_tail_disk.low()),
                    max(p13_disk.high(), p_tail_disk.high()))
    # From P_p >= W_disk > 2/3 and C_p <= E_p^coarse < 63/50:
    # D_p = 2/C_p - 1/P_p > 2/(63/50) - 1/(2/3) = 11/126.
    require(2 / CHILD_TAIL_CEILING - 1 / PARENT_TAIL_FLOOR
            == TAIL_GAIN_FLOOR and TAIL_GAIN_FLOOR > 0,
            "inverse-width direction or tail gain rational identity wrong")
    return {
        "limit_parent_lower": p_low,
        "limit_parent_upper": p_high,
        "limit_child_lower": c_low,
        "limit_child_upper": c_high,
        "limit_defect_lower": defect_lower,
        "limit_defect_upper": defect_upper,
        "p13_parent_disk_lower": p13_disk,
        "p_ge_14_parent_disk_lower": p_tail_disk,
        "all_p_parent_disk_lower": p_disk,
        "all_p_child_cap": CHILD_TAIL_CEILING,
        "all_p_defect_strict_floor": TAIL_GAIN_FLOOR,
    }


def main() -> None:
    c = certify()
    for key, value in c.items():
        if isinstance(value, I):
            print(f"{key}: [{value.low()}, {value.high()}] (certified outer interval)")
        else:
            print(f"{key}: {value}")
    print("PASS: limiting 0.696 < D_inf < 0.793; "
          "all p>=13 D_p>11/126; conditional physical marking M")
    print("NOT PROVED: exact optimum, P_p -> P_inf, "
          "any buffered canonical WAD amplification")


if __name__ == "__main__":
    main()
