#!/usr/bin/env python3
"""Exact premises for complete buffered-WAD exclusion on selected p>=10.

The covering, ring-doubling, shadow-packing, and hyperbolic collar arguments
are written in NOTE.md. This checker certifies their arithmetic premises,
not those analytic theorems. No floating point enters an acceptance test.
"""
from __future__ import annotations

import importlib.util
import argparse
import json
from fractions import Fraction as F
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUDITS = ROOT / "research/independent_audits"
UPSTREAM = AUDITS / "tip_family_canonical_wave_gain_20261116/verify.py"
spec = importlib.util.spec_from_file_location("buffer_zero_upstream", UPSTREAM)
if spec is None or spec.loader is None:
    raise RuntimeError("Missing upstream exact arithmetic")
gain = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = gain
spec.loader.exec_module(gain)
v = gain.v
I = v.Iv
ONE, TWO = v.ONE, v.TWO
LIMITS = {"K0": F(597, 100), "K1": F(16, 5), "K2": F(419, 100)}
OUTER_LIMIT = F(15, 4)
TAIL_START = 17


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def cross_ratio(b: I, a: I, d: I, c: I, radius: I) -> I:
    """Upper-half disk electrodes [a,d] and outside (b,c), with real cuts.

    h(z)=z+R^2/z maps the upper-half disk to a half-plane. The expression
    below cancels all reciprocal-coordinate denominators, including when
    zero lies in the central slit. The resulting cyclic cross ratio is
    positive and below one.
    """
    require(b.lt(a) and a.lt(d) and d.lt(c), "unordered ring electrodes")
    require(radius.positive(), "nonpositive disk radius")
    require(b.low() >= -radius.high() and c.high() <= radius.high(),
            "cut endpoint outside disk")
    r2 = radius.square()
    factors = (r2 - a*d, r2 - b*c, r2 - b*d, r2 - a*c)
    require(all(z.positive() for z in factors), "degenerate disk correction")
    m = ((d-a)*(c-b))/((d-b)*(c-a))
    m = m * factors[0]*factors[1] / (factors[2]*factors[3])
    require(m.positive() and m.lt(ONE), "invalid ring cross ratio")
    return m


def ring_length_bound(m: I) -> I:
    """ell <= pi/mod(ring) = 2*pi*K(sqrt(m))/K(sqrt(1-m))."""
    require(m.positive() and m.lt(ONE), "invalid elliptic argument")
    return TWO*v.pi_interval()*v.elliptic_factor(m)/v.elliptic_factor(ONE-m)


def order_check(x: dict[int, I], radius: I) -> None:
    entries = (-radius, x[2], x[5], x[3], v.ZERO,
               x[6], x[4], x[1], radius)
    require(all(a.lt(b) for a, b in zip(entries, entries[1:])),
            "physical three-slit order or outer containment failed")


def certify_chart(label: str, x: dict[int, I], radius: I) -> dict:
    order_check(x, radius)
    rings = {
        "K0": (x[5], x[3], x[6], x[4]),
        "K1": (x[6], x[4], x[1], radius),
        "K2": (-radius, x[2], x[5], x[3]),
    }
    lengths = {}
    parameters = {}
    for name, cuts in rings.items():
        m = cross_ratio(*cuts, radius)
        ell = ring_length_bound(m)
        require(ell.high() < LIMITS[name],
                f"{label}: {name} length cap failed")
        lengths[name] = v.bracket_dec(ell, 9)
        parameters[name] = v.bracket_dec(m, 9)

    # Same primitive outer annulus as the predecessor, with common t=200.
    t = F(200)
    center = (x[2]+x[1])/TWO
    half = (x[1]-x[2])/TWO
    major = half*I.point((t+1/t)/2)
    require(center.abs_upper()+major.high() < radius.low(),
            f"{label}: whole outer Joukowski ellipse exits the disk")
    pi = v.pi_interval()
    ell_outer = TWO*pi.square()/v.log_iv(I.point(t))
    require(ell_outer.high() < OUTER_LIMIT, "outer length cap failed")
    lengths["outer"] = v.bracket_dec(ell_outer, 9)
    return {"case": label, "ring_cross_ratio_outward_1e9": parameters,
            "peripheral_length_upper_certificate_outward_1e9": lengths}


def finite_chart(p: int, orbit: list[I]) -> tuple[dict[int, I], I]:
    scale = ONE
    for j in range(1, p):
        scale = scale*TWO*orbit[j]
    require(scale.negative(), "positive normalization needs A_p<0")
    scale = -scale
    return ({j: scale*orbit[j*p] for j in range(1, 7)},
            scale*I.point(F(1, 2**p)))


def uniform_tail_chart(start: int = TAIL_START) -> tuple[dict[int, I], I]:
    require(type(start) is int and start >= 13, "invalid all-period start")
    _, orbit = v.isolate_model()
    q = F(1, 4**start)
    coefficients = {1: F(15246)}
    for j in range(2, 6):
        coefficients[j] = F(30*15246) + F(88*(4**j-1), 3)
    x = {j: -gain.pad(orbit[j], coefficients[j]*q) for j in range(1, 6)}
    # The exact defining tip equation is x_(6p)+x_(3p)=0.
    # Use it directly: the upstream parameter-derivative bound is stated
    # only through the fifth model iterate, not the sixth.
    x[6] = -x[3]
    # Work in this fixed smaller disk for every period in the tail.
    # The actual normalized target radius is strictly larger than it.
    radius = I.point(F(3, 20)*2**start)
    return x, radius


def collar_cosh_bound(first: F, second: F) -> I:
    """cosh(omega(first)+omega(second)); both are length upper bounds."""
    require(0 < first < 8 and 0 < second < 8, "collar length outside series regime")
    a, b = I.point(first/2), I.point(second/2)
    sa, sb = v.sinh_iv(a), v.sinh_iv(b)
    ca, cb = (ONE+sa.square()).sqrt(), (ONE+sb.square()).sqrt()
    return (ONE+ca*cb)/(sa*sb)


def cutoff_checks() -> dict:
    # The exact threshold s*=log(17+12sqrt(2)) exceeds 7/2.
    # Positive series with geometric tail certifies exp(1/2)<33/20.
    from math import factorial
    z = F(1, 2)
    n = 12
    partial = sum((z**j/F(factorial(j)) for j in range(n+1)), F(0))
    tail = z**(n+1)/F(factorial(n+1))/(1-z/F(n+2))
    require(partial+tail < F(33, 20), "exponential cutoff failed")
    require(F(33, 20)**7 < F(169, 5), "7/2 exponential cutoff failed")
    require(F(7, 5)**2 < 2 and F(169, 5) == 17+12*F(7, 5),
            "algebraic threshold comparison failed")
    require(LIMITS["K1"] < F(7, 2), "right slit not singly excluded")
    require(all(z < 7 for z in (*LIMITS.values(), OUTER_LIMIT)),
            "returning-arc cap failed")
    require(LIMITS["K1"] < LIMITS["K2"] and OUTER_LIMIT < LIMITS["K2"]
            and LIMITS["K2"] < LIMITS["K0"], "largest-two length sorting failed")

    # For distinct K0,K2, the hyperbolic collar lemma implies
    # cosh d >= (1+cosh(A/2)cosh(B/2))/(sinh(A/2)sinh(B/2)).
    bound = collar_cosh_bound(LIMITS["K0"], LIMITS["K2"])
    require(bound.low() > F(1061, 1000), "two-collar separation failed")
    require(F(1061, 1000)**2 > F(9, 8), "distance threshold failed")
    # Returning classes satisfy s <= ell_i/2 <3. The same full-width
    # cap as the distinct-boundary estimate therefore applies.
    require(max(*LIMITS.values(), OUTER_LIMIT)/2 < 3, "returning shadow cap failed")
    require(F(33, 20)**6 < F(2061, 61), "returning exponential gap failed")
    raw_m = I.point(F(2000, 2061))
    raw_q = v.elliptic_factor(raw_m)/v.elliptic_factor(ONE-raw_m)
    require(raw_q.high() < F(1999, 1000), "uniform raw quadrilateral gap failed")
    # cosh((log 2)/2)=3/(2sqrt(2)); both sides are positive.
    return {"cosh_distance_strict_lower": "1061/1000",
            "collar_cosh_expression_outward_1e9": v.bracket_dec(bound, 9),
            "s_star_strict_lower": "7/2",
            "q_equals_2_distance": "(log 2)/2",
            "all_classes_raw_q_strict_upper": "1999/1000",
            "raw_q_envelope_outward_1e9": v.bracket_dec(raw_q, 9)}


def diagnose_period9_boundary(packet: dict) -> dict:
    """Show why the same ring/collar certificate does not settle p=9.

    This is failure of these upper peripheral caps to certify sufficient
    separation, never a lower bound for an actual canonical coefficient.
    The exact whole-carrier ring improves on any inscribed carrier ellipse.
    """
    p, _, orbit = v.checked_packet(packet)
    require(p == 9, "range diagnostic needs the checked p=9 root")
    x, radius = finite_chart(p, orbit)
    order_check(x, radius)
    center = (x[2]+x[1])/TWO
    half = (x[1]-x[2])/TWO
    require(center.positive(), "p=9 carrier-center sign changed")
    ratio = (radius-center)/half
    require(ratio.gt(ONE), "p=9 carrier ellipse does not fit")
    tmax = ratio+(ratio.square()-ONE).sqrt()
    require(tmax.low() > 100 and tmax.high() < 102,
            "p=9 limiting ellipse parameter escaped certified range")
    central = ring_length_bound(cross_ratio(x[5], x[3], x[6], x[4], radius))
    carrier = ring_length_bound(cross_ratio(-radius, x[2], x[1], radius, radius))
    collar = collar_cosh_bound(central.high(), carrier.high())
    require(collar.high()**2 < F(9, 8),
            "p=9 certificate insufficiency no longer follows")
    return {
        "period": 9,
        "status": "These peripheral caps do not certify all-class exclusion; actual support remains undecided",
        "largest_admissible_ellipse_t_outward_1e9": v.bracket_dec(tmax, 9),
        "central_length_upper_expression_outward_1e9": v.bracket_dec(central, 9),
        "whole_carrier_ring_length_upper_expression_outward_1e9": v.bracket_dec(carrier, 9),
        "guaranteed_collar_cosh_expression_outward_1e9": v.bracket_dec(collar, 9),
        "collar_expression_upper_squared_strictly_below": "9/8",
        "positive_canonical_weight_proved": False,
    }


def certify() -> dict:
    thresholds = cutoff_checks()
    packets = json.loads(gain.s.OLD.read_text(encoding="utf-8"))["periods"]
    rows = []
    for p in (10, 11, 12):
        matches = [row for row in packets if row["p"] == p]
        require(len(matches) == 1, "missing or duplicate original root packet")
        checked_p, _, orbit = v.checked_packet(matches[0])
        require(checked_p == p, "wrong finite root")
        rows.append(certify_chart(str(p), *finite_chart(p, orbit)))
    for p in range(13, TAIL_START):
        _, orbit = gain.s.certify_tip(p)
        rows.append(certify_chart(str(p), *finite_chart(p, orbit)))
    rows.append(certify_chart(f"all p>={TAIL_START}", *uniform_tail_chart()))
    p9_packets = [row for row in packets if row["p"] == 9]
    require(len(p9_packets) == 1, "missing or duplicate p=9 range-boundary packet")
    range_boundary = diagnose_period9_boundary(p9_packets[0])
    return {
        "status": "Exact arithmetic premises for the written all-class zero theorem",
        "surface": "D(0,R_p) minus three actual selected filled intervals, minimal whole-circle marking",
        "conclusion": "W_can(Y_p)=0 for every selected integer p>=10",
        "all_class_argument": "peripheral shadows plus disjoint hyperbolic collars",
        "deck_word_cutoff": None,
        "peripheral_length_strict_caps": {k: str(q) for k, q in LIMITS.items()},
        "outer_length_strict_cap": str(OUTER_LIMIT),
        "thresholds": thresholds,
        "cases": rows,
        "range_boundary_p9": range_boundary,
        "formalized_analysis": False,
        "scope": "Written theorem from named physical and classical analytic inputs; no MLC closure",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-manifest", action="store_true",
                        help="compare the recomputation with certificate.json")
    args = parser.parse_args()
    result = certify()
    if args.check_manifest:
        saved = json.loads((HERE / "certificate.json").read_text(encoding="utf-8"))
        require(result == saved, "stored certificate differs from exact recomputation")
        print("PASS: exact certificate matches all seven finite cases and the uniform tail.")
        print("PASS: every minimally marked full quadrilateral has q<1999/1000 for p>=10.")
        print("Written analysis is in NOTE.md; no arbitrary marking refinement or MLC closure is asserted.")
    else:
        print(json.dumps(result, indent=2))
