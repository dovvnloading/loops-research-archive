#!/usr/bin/env python3
"""Exact collar-based LOCAL widths and WAD norm, never individual KKL q_gamma.

Analytic assumptions (annular cyclic-cover comparison and KKL A.2) are written
in NOTE.md and are not mechanically proved here. No binary float arithmetic.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
TIP = ROOT / "results/tip_KKL_tree_marked_breakage_20261109.json"
INCIDENCE = ROOT / "results/canonical_wad_electrode_incidence_20261116.json"
PREVIOUS = ROOT / "results/canonical_wad_conformal_weights_20261116.json"
OUTPUT = Path(__file__).with_name("results.json")

PARAM = (-607918036626757496169199575185708826140,
         -607918036626757496169199575185708826139)
DEN = 1 << 256
RADIUS = Q(1, 4)
# Elliptical annuli contained in the ACTUAL three-hole surface. For "outer",
# [x6,x3] is only a connected carrier enclosing all holes, NOT a fourth slit.
COLLARS = {
    "outer": (6, 3, Q(23, 10)),
    "K0": (9, 18, Q(11)),
    "K1": (12, 3, Q(49)),
    "K2": (6, 15, Q(25)),
}
# Rational upper bounds on 2*pi/log(t); NOT values of local widths or q_gamma.
LOCAL_UPPER = {
    "outer": Q(943, 125),
    "K0": Q(2621, 1000),
    "K1": Q(323, 200),
    "K2": Q(1953, 1000),
}
NORM_UPPER = Q(687, 100)
REPORT_DEN = 10**9


def require(test: bool, message: str) -> None:
    if not test:
        raise AssertionError(message)


def square_interval(lo: int, hi: int) -> tuple[int, int]:
    """Outward dyadic squaring with a fixed denominator 2**256."""
    require(lo <= hi, "ordered orbit interval")
    low = 0 if lo <= 0 <= hi else min(lo * lo, hi * hi)
    high = max(lo * lo, hi * hi)
    return low // DEN, (high + DEN - 1) // DEN


def orbit(tip: dict) -> dict[int, tuple[Q, Q]]:
    p = tip["source_parameter"]
    require(p["denominator_power_of_two"] == 128 and
            (p["lower_numerator"], p["upper_numerator"]) == PARAM,
            "unchanged physical PR68 dyadic parameter required")
    lo, hi = (v << 128 for v in PARAM)
    out = {}
    for k in range(1, 19):
        if k > 1:
            lo, hi = square_interval(lo, hi)
            lo += PARAM[0] << 128
            hi += PARAM[1] << 128
        out[k] = (Q(lo, DEN), Q(hi, DEN))
    return out


def arctan_range(z: Q, n: int = 30) -> tuple[Q, Q]:
    require(0 < z < 1 and n > 0, "atan domain")
    s = sum(((-1)**k * z**(2*k+1) / Q(2*k+1) for k in range(n)), Q(0))
    tail = z**(2*n+1) / Q(2*n+1)
    return (s, s+tail) if n % 2 == 0 else (s-tail, s)


def pi_range() -> tuple[Q, Q]:
    """16*atan(1/5) - 4*atan(1/239), with alternating remainder."""
    a, b = arctan_range(Q(1, 5))
    c, d = arctan_range(Q(1, 239))
    return 16*a - 4*d, 16*b - 4*c


def atanh_log_range(z: Q, n: int = 25) -> tuple[Q, Q]:
    require(0 <= z <= Q(1, 3) and n > 0, "positive log series domain")
    s = 2*sum((z**(2*k+1)/Q(2*k+1) for k in range(n)), Q(0))
    remainder = 2*z**(2*n+1)/(Q(2*n+1)*(1-z*z))
    return s, s+remainder


def log_range(t: Q) -> tuple[Q, Q]:
    """log(t)=k*log(2)+log(y), y in [1,2), exact positive atanh sums."""
    t = Q(t)
    require(t >= 2, "collar t must be >= 2")
    k, y = 0, t
    while y >= 2:
        k, y = k+1, y/2
    require(1 <= y < 2, "log dyadic reduction")
    log2 = atanh_log_range(Q(1, 3))
    logy = atanh_log_range((y-1)/(y+1))
    return k*log2[0]+logy[0], k*log2[1]+logy[1]


def outward_rational_interval(lo: Q, hi: Q) -> list[str]:
    """Strict 1e-9 outward rounding; never round via float."""
    require(lo <= hi, "ordered real interval")
    floor_lower = lo.numerator*REPORT_DEN // lo.denominator
    ceil_upper = -((-hi.numerator*REPORT_DEN)//hi.denominator)
    return [str(Q(floor_lower-1, REPORT_DEN)),
            str(Q(ceil_upper+1, REPORT_DEN))]


def center_half(left: tuple[Q,Q], right: tuple[Q,Q]):
    require(left[1] < right[0], "positive real interval length")
    m = ((left[0]+right[0])/2, (left[1]+right[1])/2)
    a = ((right[0]-left[1])/2, (right[1]-left[0])/2)
    return m, a


def check_collar(name: str, indices: tuple[int, int],
                 xs: dict[int, tuple[Q,Q]], t: Q) -> None:
    """Check exact ellipse containment in U3 and separation from other K."""
    require(indices == COLLARS[name][:2], "pinned physical collar endpoints")
    left, right = indices
    m, a = center_half(xs[left], xs[right])
    major = a[1]*(t+1/t)/2
    abs_center = max(abs(m[0]), abs(m[1]))
    require(abs_center + major < RADIUS,
            name+": entire Joukowski ellipse must lie strictly inside U3")
    xmin, xmax = m[0]-major, m[1]+major
    if name == "K0":
        require(xmin > xs[15][1] and xmax < xs[12][0],
                "K0 collar collides with K2 or K1")
    elif name == "K1":
        require(xmin > xs[18][1], "K1 collar collides with K0")
    elif name == "K2":
        require(xmax < xs[9][0], "K2 collar collides with K0")
    elif name == "outer":
        require(xs[6][1] < xs[15][0] < xs[9][0] < xs[18][0]
                < xs[12][0] < xs[3][0],
                "whole-tree outer collar must encircle all three holes")
    else:
        raise AssertionError("unknown peripheral interval")


def certify(tip: dict, incidence: dict, previous: dict,
            collars: dict | None = None, uppers: dict | None = None) -> dict:
    collars = COLLARS if collars is None else collars
    uppers = LOCAL_UPPER if uppers is None else uppers
    require(set(collars) == set(COLLARS) and set(uppers) == set(COLLARS),
            "exactly the four peripheral boundaries required")
    require(tip["scope"].startswith("ACTUAL KKL") and
            tip["tree"] == "[x6,x3]", "must use actual physical tree")
    d = incidence["canonical_definition"]
    require(d["surface"] ==
            "U3\\K; K=K0 union K1 union K2 (three disjoint small Julia intervals)"
            and d["minimal_marking"] ==
            "four entire ideal boundary components: K0, K1, K2 and outer U3"
            and d["weights_numerically_enclosed"] is False,
            "source-defined minimal canonical marking/noncertification")
    require(incidence["geometry"]["canonical_small_julia_sets"] ==
            "K0=[x9,x18]; K1=[x12,x3]; K2=[x6,x15]",
            "unchanged KKL slit endpoints")
    require(previous["source_tip"] ==
            "results/tip_KKL_tree_marked_breakage_20261109.json" and
            previous["source_audit"] ==
            "results/canonical_wad_electrode_incidence_20261116.json" and
            previous["embedded_collar_t_for_each_slit"] ==
            {"K0":11, "K1":49, "K2":25} and
            previous["canonical_WAD"]["quadrilateral_enclosures_certified"] is False and
            previous["canonical_WAD"]["excluded_remaining_classes_proved"] is False,
            "previous audit must remain nonclosing and unchanged")
    xs = orbit(tip)
    require(xs[6][1] < xs[15][0] < xs[9][0] < xs[18][0] <
            xs[12][0] < xs[3][0] < RADIUS, "strict three-slit order")
    p0, p1 = pi_range()
    require(Q(333,106) < p0 < p1 < Q(22,7), "exact pi series enclosure")
    require(sum(uppers.values(), Q(0))/2 < NORM_UPPER,
            "rational local bounds do not imply claimed norm upper")

    collar_results = {}
    for name, (i, j, t) in collars.items():
        require(isinstance(t, Q) and t >= 2, "rational Joukowski parameter")
        check_collar(name, (i,j), xs, t)
        lo, hi = log_range(t)
        require(0 < lo < hi, "strict log interval")
        caplo, caphi = 2*p0/hi, 2*p1/lo
        require(caphi < uppers[name],
                name+": 2*pi/log(t) does not fit local upper bound")
        collar_results[name] = {
            "joukowski_parameter_t": str(t),
            "log_t_integral_rational_interval": outward_rational_interval(lo,hi),
            "annulus_conductance_2pi_over_log_t_interval":
                outward_rational_interval(caplo,caphi),
            "peripheral_local_width_strict_upper": str(uppers[name]),
            "local_width_lower_certified": "0",
            "reason": ("collar of outer boundary, annular cover of outer peripheral loop"
                       if name == "outer" else
                       "collar of "+name+", annular cover of its peripheral loop"),
        }

    labels = ("outer", "K0", "K1", "K2")
    pairs = []
    for i, e1 in enumerate(labels):
        for e2 in labels[i:]:
            w = uppers[e1]/2 if e1 == e2 else min(uppers[e1],uppers[e2])
            pairs.append({
                "boundary_pair": [e1,e2],
                "class_status": "open: NO per-class ideal quadrilateral solved",
                "uniform_q_gamma_strict_bracket": ["0",str(2+w)],
                "applies_to": "every admissible simple ideal arc of this endpoint type; not a finite class enumeration",
                "positive_canonical_weight_certified": False,
            })
    return {
        "schema_version": 1,
        "scope": "NEW certified peripheral-collar and norm bounds; NO per-class q_gamma evaluation",
        "physical_tip": "results/tip_KKL_tree_marked_breakage_20261109.json",
        "parents": ["results/canonical_wad_electrode_incidence_20261116.json",
                    "results/canonical_wad_conformal_weights_20261116.json"],
        "surface": "U3\\(K0 union K1 union K2), U3=D(0,1/4), 4 whole-boundary minimal marking",
        "certification": "Fraction-only outward 256-bit orbit; exact rational pi and log intervals; analytic Joukowski/cyclic-cover/modulus comparison in NOTE.md",
        "annular_collars": collar_results,
        "local_width_inequality": "W(I) <= 2*pi/log(t_I), by essential annulus in I-cyclic cover; sum_I W_can(I) = 2*norm(W_can) <= sum_I W(I)",
        "uniform_endpoint_pair_brackets": pairs,
        "every_individual_q_gamma_certified": False,
        "positive_support_classified": False,
        "exhaustive_other_classes_q_le_2_proved": False,
        "positive_support_upper_cardinality_KKL": 10,
        "positive_support_list": None,
        "total_canonical_norm_strict_bracket": ["0",str(NORM_UPPER)],
        "horizontal_vertical_projection_norm_strict_bracket":
            ["0",str(NORM_UPPER)],
        "norm_bracket_semantics": "0 <= norm < upper (non-strict at zero); positive support unknown",
        "numerical_only": [],
        "open": ["which q_gamma>2", "finite exhaustive candidate class enumeration",
                 "nontrivial individual q_gamma lower bounds and decisions",
                 "exact canonical WAD and h+v support",
                 "sharper norm and transfer constant"],
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group()
    g.add_argument("--check-manifest", action="store_true")
    g.add_argument("--write-manifest", action="store_true")
    args = p.parse_args()
    obj = certify(json.loads(TIP.read_text()),
                  json.loads(INCIDENCE.read_text()),
                  json.loads(PREVIOUS.read_text()))
    if args.write_manifest:
        OUTPUT.write_text(json.dumps(obj, sort_keys=True, indent=2)+"\n",
                          encoding="utf-8")
        print("WROTE", OUTPUT)
    elif args.check_manifest:
        require(json.loads(OUTPUT.read_text()) == obj,
                "manifest drift or unsupported positive q_gamma claim")
        print("PASS four exact collars; canonical norm <687/100; all q_gamma OPEN")
    else:
        print(json.dumps(obj, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
