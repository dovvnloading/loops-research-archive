#!/usr/bin/env python3
"""Independent exact/interval finite audit: physical tip Wave versus free annular condenser.

All finite comparisons use Fraction arithmetic (and 256-bit outward dyadic orbit
enclosures). No floats, sampled PDE values, guessed capacity, or point sampling.
The continuum extremal-width and condenser theorems are written proof inputs,
not machine-checked by this finite verifier.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from math import factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / "results/tip_KKL_tree_marked_breakage_20261109.json"
OUT = ROOT / "results/wave_vs_dirichlet_contact_transfer_20261115.json"
D = 1 << 256
H_VALUES = (Q(1, 1024), Q(1, 2048), Q(1, 4096))


def demand(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def arctan_bounds(x: Q, terms: int = 14) -> tuple[Q, Q]:
    demand(0 < x <= 1, "arctan range")
    partial = sum(((-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
                   for k in range(terms)), Q())
    error = x ** (2 * terms + 1) / (2 * terms + 1)
    return ((partial, partial + error) if terms % 2 == 0
            else (partial - error, partial))


def pi_bounds() -> tuple[Q, Q]:
    a, b = arctan_bounds(Q(1, 5))
    c, d = arctan_bounds(Q(1, 239))
    lo, hi = 16 * a - 4 * d, 16 * b - 4 * c
    demand(Q(333, 106) < lo < hi < Q(22, 7), "Machin pi enclosure")
    return lo, hi


def logarithm_atanh_bounds(z: Q, terms: int = 32) -> tuple[Q, Q]:
    demand(0 <= z <= Q(1, 3), "reduced logarithm domain")
    total = sum((2 * z ** (2 * k + 1) / (2 * k + 1)
                 for k in range(terms)), Q())
    tail = 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return total, total + tail


LOG2 = logarithm_atanh_bounds(Q(1, 3))


def log_bounds(x: Q) -> tuple[Q, Q]:
    """Positive rational log by exact power-of-two range reduction."""
    demand(x >= 1, "log input must be >=1")
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    a, b = logarithm_atanh_bounds((x - 1) / (x + 1))
    return k * LOG2[0] + a, k * LOG2[1] + b


def cos_bounds(x: Q) -> tuple[Q, Q]:
    """Alternating Taylor enclosure on [0,1], with no transcendental calls."""
    demand(0 <= x <= 1, "cos input")
    terms = [(-1) ** k * x ** (2 * k) / factorial(2 * k)
             for k in range(9)]
    lower = sum(terms[:8], Q())  # through the negative seventh term
    upper = sum(terms, Q())     # add the positive eighth term
    demand(lower <= upper, "cos enclosure order")
    return lower, upper


def square_dyadic(a: int, b: int) -> tuple[int, int]:
    demand(a <= b, "dyadic order")
    if a <= 0 <= b:
        minimum, maximum = 0, max(a * a, b * b)
    else:
        minimum, maximum = min(a * a, b * b), max(a * a, b * b)
    return minimum // D, -(-maximum // D)


def physical_orbit(source: dict) -> tuple[Q, Q, Q, Q]:
    c = source["source_parameter"]
    demand(c == {
        "denominator_power_of_two": 128,
        "lower_numerator": -607918036626757496169199575185708826140,
        "upper_numerator": -607918036626757496169199575185708826139
    }, "physical PR68 parameter changed")
    c0, c1 = c["lower_numerator"] << 128, c["upper_numerator"] << 128
    a = b = 0
    values = {}
    for n in range(1, 16):
        a, b = square_dyadic(a, b)
        a, b = a + c0, b + c1
        values[n] = (Q(a, D), Q(b, D))
    x3lo, x3hi = values[3]
    x6lo, x6hi = values[6]
    demand(Q(9, 50) < x3lo <= x3hi < Q(1, 5), "x3 localization")
    demand(Q(-1, 5) < x6lo <= x6hi < Q(-7, 50), "x6 localization")
    # The real source interval [-x3,x3] has G monotone on each half:
    # f is negative there, f^2 positive, G'=8*z*f*f^2.
    demand(Q(c0, D) > Q(-9, 5), "c lower")
    demand(Q(c1, D) + x3hi**2 < Q(-17, 10), "f negative upper")
    demand(Q(17, 10)**2 - Q(9, 5) > 0, "f^2 positive lower")
    return x3lo, x3hi, x6lo, x6hi


def check_original_wave(s: dict) -> None:
    w = s["marked_breakable_wave"]
    demand(s["scope"].startswith("ACTUAL KKL"), "not native KKL physical source")
    demand(s["single_new_attachment"] == "[-x3,x6)", "physical attachment")
    demand(s["tree_preimage_in_V3"] == "[-x3,x3]", "preimage tree")
    demand(s["inner_pullback_lengths"] == [5, 2, 1, 1, 3, 1, 3, 1, 1, 2],
           "physical original pullback lengths")
    demand(s["attachment_boundary_source_atoms"] == [19, 0, 1], "attachment block")
    demand(s["crossing_circle_source_restrictions"] == [[3, 1], [19, 17]],
           "native surviving pairs")
    demand(s["crossing_circle_coarse_endpoint_pairs"] == [[1, 0], [0, 9]],
           "native coarse pairs")
    demand(s["both_crossing_restrictions_pass_A1_and_single_pullback_cell_filters"],
           "native path filters")
    demand(w["center"] == "-9/64" and w["open_radius_interval"] == ["3/256", "1/64"],
           "native conformal rectangle")
    demand(w["target_base_atoms"] == [9, 0, 1] and w["target_crest_atom"] == 0,
           "native base and crest")
    demand(w["target_extremal_width"] == "log(4/3)/(2*pi)",
           "native width must not be surrogate capacity")
    demand(w["each_restriction_and_pushforward_width"] == "log(4/3)/pi"
           and w["harmonic_series_inequality_is_equality"],
           "two children series law")
    demand(Q(1, 64) / Q(3, 256) == Q(4, 3), "native radius ratio")


def verify_tip_angle(x3lo: Q, x3hi: Q, x6lo: Q, x6hi: Q) -> None:
    # Joukowski chart z=x3*(w+w^-1)/2, so X=[-x3,x6)
    # has inner angle ell_X=2*acos(-x6/x3), deck w -> -w.
    ratio_lo, ratio_hi = -x6hi / x3hi, -x6lo / x3lo
    lo_c06, _ = cos_bounds(Q(3, 5))
    _, hi_c07 = cos_bounds(Q(7, 10))
    demand(hi_c07 < ratio_lo <= ratio_hi < lo_c06,
           "ell_X in (6/5,7/5) by cos ordering")
    demand(0 < ratio_lo < ratio_hi < 1, "short opposed physical arcs")


def verify_whole_physical_collar(h: Q, x3hi: Q) -> None:
    # exp(h)<=1/(1-h), sinh(h)<h/(1-h) for 0<h<1;
    # z0=x3*cos(theta), |z-z0|<=x3*sinh(h).
    delta = Q(1, 5) * h / (1 - h)
    demand(x3hi < Q(1, 5) and delta < Q(1, 4096), "collar displacement")
    demand(Q(1, 5) + delta < Q(1, 4), "collar source absolute bound")
    derivative = 8 * Q(1, 4) * Q(33, 16) * Q(1601, 256)
    demand(derivative < 26, "G'=8zf(z)f^2(z) disk bound")
    demand(Q(1, 5) + 26 * delta < Q(1, 4), "entire Joukowski collar maps inside U3")
    # T' lives in central V3; radial paths from the collar to T' stay in
    # G^{-1}(U3). This certifies the same physical connected component.


def verify_bounds() -> None:
    s = json.loads(SOURCE.read_text(encoding="utf-8"))
    check_original_wave(s)
    x3lo, x3hi, x6lo, x6hi = physical_orbit(s)
    verify_tip_angle(x3lo, x3hi, x6lo, x6hi)
    pi_lo, pi_hi = pi_bounds()
    log43_lo, log43_hi = log_bounds(Q(4, 3))
    demand(log43_lo / (2 * pi_hi) > Q(1, 25), "full native width > 1/25")
    demand(log43_hi / (2 * pi_lo) < Q(1, 20), "full native width < 1/20")
    demand(Q(1, 7) < 1 / (2 * pi_hi) < 1 / (2 * pi_lo) < Q(1, 6),
           "sliced native density")
    # e^(3/2)>3 by a finite positive Taylor polynomial, hence log(3)<3/2.
    demand(sum((Q(3, 2)**k / factorial(k) for k in range(4)), Q()) > 3,
           "log(3) < 3/2 proof")
    for h in H_VALUES:
        verify_whole_physical_collar(h, x3hi)
        demand(1 / (1 - h) < Q(4, 3), "native S_h is inside PR68 full Wave")
        # Free-outer, complete deck-opposed condenser. The two *written*
        # variational bounds are L=[pi/(2h)+(4/pi)(3/2+log(1+2/ell))]^-1,
        # U=2h/(pi-ell). Evaluate with outward exact rational bounds.
        # Physical ell_X in (6/5,7/5), log(1+2/ell_X)<log3<3/2.
        tip_lower = h / (pi_hi / 2 + 12 * h / pi_lo)
        tip_upper = 2 * h / (pi_lo - Q(7, 5))
        demand(tip_lower > Q(3, 5) * h, "fixed tip condenser lower")
        demand(tip_upper < Q(6, 5) * h, "fixed tip condenser upper")
        # First native witness: full PR68 wave vs genuine source collar.
        demand(log43_lo / (2 * pi_hi) > tip_upper,
               "full native wave exceeds physical source condenser")
        # Reverse order using an actual sub-Wave, r0<r<r0*exp(h).
        demand(h / (2 * pi_lo) < tip_lower,
               "sliced native wave is smaller than physical source condenser")
        # Archive polynomial negative control ell=h^2: h*log(1/ell)->0.
        ell = h * h
        log_up = log_bounds(1 + 2 / ell)[1]
        poly_lower = h / (pi_hi / 2 + (4 * h / pi_lo) * (Q(3, 2) + log_up))
        poly_upper = 2 * h / (pi_lo - ell)
        demand(poly_lower > h / 2 and poly_upper < 2 * h / 3,
               "polynomial thin-collar response")
        # Critical ell=exp(-1/h). Since ell<1/16,
        # log(1+2/ell) <= log3 + 1/h < 3/2 + 1/h.
        demand(1 + 1 / h > 16, "critical ell<1/16 via e^x>1+x")
        crit_lower = h / (pi_hi / 2 + (4 * h / pi_lo) * (3 + 1 / h))
        crit_upper = 2 * h / (pi_lo - Q(1, 16))
        demand(crit_lower > h / 4 and crit_upper < 2 * h / 3,
               "critical exponential response")
        # Literal archive collapse: ell=(h/4)*exp(-1/h^2).
        # log(1+2/ell)<log3+log(4/h)+1/h^2;
        # half-disk radial cutoff W <= pi/(log2+1/h^2).
        log4h_up = log_bounds(4 / h)[1]
        super_lower = h / (
            pi_hi / 2 + (4 * h / pi_lo) * (3 + log4h_up + 1 / (h * h)))
        super_upper = pi_hi / (LOG2[0] + 1 / (h * h))
        demand(super_lower > h * h / 2 and super_upper < 4 * h * h,
               "literal superexponential collapse bracket")
        demand(super_upper < h / (2 * pi_hi),
               "no uniform lower transfer from the artificial small electrode")
    # All assertions above are exact rational predicates, not numerical
    # approximations to a PDE solution.


def compute_manifest() -> dict:
    verify_bounds()
    return {
        "schema_version": 1,
        "source_tip": "results/tip_KKL_tree_marked_breakage_20261109.json",
        "arithmetic": "256-bit outward dyadic polynomial orbit; exact Fraction pi, cosine and logarithm enclosures",
        "physical_tip": {
            "source_conformal_chart": "z=x3*(w+w^-1)/2; t=log|w|; theta=arg(w); tau(w)=-w",
            "real_attachment": "[-x3,x6)",
            "electrode_angular_length": "ell_X=2*acos(-x6/x3)",
            "certified_angular_interval": ["6/5", "7/5"],
            "whole_physical_collar_certified_for": "0<h<=1/1024",
            "target_wave_chart": "z=-9/64+r*exp(i*theta); log(r) in (log(3/256),log(1/64))",
            "native_full_wave_width": "log(4/3)/(2*pi)",
            "each_filtered_child_width": "log(4/3)/pi",
            "filtered_children": 2,
            "native_full_width_certified_interval": ["1/25", "1/20"]
        },
        "finite_physical_comparison": {
            "collar_height": "1/1024",
            "full_native_wave_width": "log(4/3)/(2*pi)",
            "native_subwave_width": "h/(2*pi)",
            "dirichlet_full_capacity_certified_interval": ["(3/5)*h", "(6/5)*h"],
            "strict_order_certified": "W(native S_h) < W_dir(h,ell_X) < W(native S_full)",
            "failing_hypothesis": "PR68 target Wave and source condenser are not on the same surface and native Wave leaves do not join the opposed source electrodes"
        },
        "thin_collar_controls": [
            {
                "access": "ell=ell_X, fixed actual physical attachment",
                "type": "fixed_physical_tip",
                "dirichlet_certified": "(3/5)*h < W_dir < (6/5)*h",
                "wave_certified": "W(native tip S_h)=h/(2*pi)"
            },
            {
                "access": "ell=h^2, formal polynomial control",
                "type": "polynomial",
                "dirichlet_certified": "h/2 < W_dir < (2/3)*h",
                "wave_certified": "W(native tip S_h)=h/(2*pi)"
            },
            {
                "access": "ell=exp(-1/h), formal crossover control",
                "type": "critical_exponential",
                "dirichlet_certified": "h/4 < W_dir < (2/3)*h",
                "wave_certified": "W(native tip S_h)=h/(2*pi)"
            },
            {
                "access": "ell=(h/4)*exp(-1/h^2), archive literal formal negative control",
                "type": "superexponential",
                "dirichlet_certified": "h^2/2 < W_dir < 4*h^2",
                "wave_certified": "W(native tip S_h)=h/(2*pi)"
            }
        ],
        "certified_h_values": ["1/1024", "1/2048", "1/4096"],
        "conditional_comparison": "On a common annulus, S subset Gamma_h(A,tau A) implies 0<=W(S)<=W_dir; optimal constant 1",
        "not_certified": [
            "No identification of PR68 target Wave with the source Dirichlet curve family",
            "Formal variable-ell controls are not physical KKL attachment stages",
            "Canonical maximal WAD weight is not computed; PR68 marked Wave is not an identified proof-selected WAD",
            "No uniform converse, period/depth bridge, parabolic access law or MLC conclusion"
        ],
        "numerical_only_observations": []
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--check-manifest", action="store_true")
    group.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()
    result = compute_manifest()
    if args.write_manifest:
        OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print("WROTE", OUT)
    elif args.check_manifest:
        demand(json.loads(OUT.read_text(encoding="utf-8")) == result, "manifest drift")
        print("PASS: exact physical tip angle/collar, native rectangle widths, "
              "free-outer capacity brackets, both failed unrestricted comparisons, "
              "and three thin-collar scales")
    else:
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
