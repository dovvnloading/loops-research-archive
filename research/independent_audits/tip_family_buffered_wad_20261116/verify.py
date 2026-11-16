#!/usr/bin/env python3
"""Source-faithful tip-family buffered-WAD partial certificate.

Proves peripheral *exclusions*, not an exhaustive q_gamma classification.
Finite arithmetic uses Fraction / inherited outward dyadic interval charts.
Covering spaces, elliptic Landen transformations and the collar comparison
are written proofs in NOTE.md, NOT claimed to be formalized by Python.
No files are written by this verifier.
"""
from __future__ import annotations

import importlib.util
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUDITS = ROOT / "research" / "independent_audits"
OLD = AUDITS / "real_primitive_tip_family_unconditional_20261116" / "results.json"
OUTER_T = {
    3: F(23, 10), 4: F(2), 5: F(4), 6: F(8),
    7: F(16), 8: F(32), 9: F(64), 10: F(128),
    11: F(300), 12: F(512),
}
INNER_T = {"K0": F(11), "K1": F(49), "K2": F(25)}
# Strict rational upper bounds on *cyclic peripheral widths* via collars.
# These are not ideal-cover quadrilateral widths.
INNER_B = {"K0": F(2621, 1000), "K1": F(323, 200),
           "K2": F(1953, 1000)}
TAIL_OUTER_T = F(1024)
MAX_NORM_TAIL = F(619, 200)  # strict: (2.621+1.615+1.953)/2 = 3.0945
ALL = ("outer", "K0", "K1", "K2")
INNER = ("K0", "K1", "K2")


def require(condition: bool, why: str) -> None:
    if not condition:
        raise AssertionError(why)


def load_verifier(directory: str, tag: str):
    source = AUDITS / directory / "verify.py"
    require(source.is_file(), "missing immutable predecessor: " + str(source))
    spec = importlib.util.spec_from_file_location(tag, source)
    require(spec is not None and spec.loader is not None, "bad predecessor loader")
    module = importlib.util.module_from_spec(spec)
    sys.modules[tag] = module
    spec.loader.exec_module(module)
    return module


def elliptic_threshold_finite_logic() -> None:
    """Exact algebraic/transcendental *sufficient* cutoff.

    Landen: q=2 iff k^2=s*=12 sqrt(2)-16, which satisfies
    s*^2 + 32*s* - 32 = 0.  If ell < 7/2, then
    exp(ell) < (33/20)^7 < 169/5 < 17+12 sqrt(2).
    A symbolic proof of Landen's identity is in NOTE, not in this test.
    """
    x = F(26, 27)
    require(x*x + 32*x - 32 < 0 and 0 < x < 1,
            "algebraic q=2 threshold inequality")
    require(F(7, 5)**2 < 2, "sqrt(2)>7/5 required")
    require(F(33, 20)**7 < F(169, 5),
            "exp(7/2) comparison does not fit")
    z = F(1, 2)
    n = 10
    partial = sum((z**j/F(math.factorial(j)) for j in range(n+1)), F(0))
    tail = (z**(n+1)/F(math.factorial(n+1))) / (1-z/F(n+2))
    require(partial < partial+tail < F(33, 20),
            "rigorous positive Taylor remainder for exp(1/2)")


def width_log_length_bounds(quad, t: F) -> tuple[F, F]:
    """0 < ell(I) <= 2*pi^2/log(t) with exact outgoing rational interval."""
    require(type(t) is F and t >= 2, "non-dyadic or negative collar radius")
    pi_low, pi_high = quad.pi_range()
    ln_low, ln_high = quad.log_range(t)
    require(0 < pi_low <= pi_high and 0 < ln_low <= ln_high,
            "invalid rational pi or log enclosure")
    return 2*pi_low*pi_low/ln_high, 2*pi_high*pi_high/ln_low


def check_cyclic_exclusion(ell_upper: F, limit: F) -> None:
    """A certified ell < 7/2 implies every incident ideal q < 2.

    If limit=3, also uses the sharper exp(3)<27<17+12 sqrt(2).
    Passing this finite test is conditional on the analytic cyclic-cover
    / disjoint-boundary-lifts theorem in NOTE.
    """
    require(type(ell_upper) is F and type(limit) is F and ell_upper > 0,
            "length enclosure must be a positive rational")
    require(limit in (F(3), F(7, 2)) and ell_upper < limit,
            "cyclic-cover exclusion length criterion failed")
    elliptic_threshold_finite_logic()
    if limit == 3:
        # e = sum_{n>=0}1/n! < 3, hence e^3 < 27.
        require(F(27) < F(169, 5), "exp(3) threshold comparison failed")


def check_order(xi) -> None:
    """Actual three filled Julia intervals, not the ten-atom tree marking."""
    z = xi[1].point(0)
    ordered = (xi[2], xi[5], xi[3], z,
               xi[6], xi[4], xi[1])
    require(all(a.lt(b) for a,b in zip(ordered, ordered[1:])),
            "physical little-Julia interval order/holes failed")


def ellipse_check(xi, outer_radius, name: str, t: F) -> None:
    """Exact whole-ellipse containment and, for inner holes, slit separation.

    The outer carrier [x_2p,x_p] is not a fourth small Julia set.
    These are embedded *essential annuli*, not ideal quadrilaterals.
    """
    require(name in ALL and isinstance(t, F) and t > 1,
            "unsupported annulus")
    cuts = {"outer": (2, 1), "K0": (3, 6),
            "K1": (4, 1), "K2": (2, 5)}
    left, right = cuts[name]
    require(xi[left].lt(xi[right]), "collar endpoint reversal")
    two = xi[1].point(2)
    m = (xi[left]+xi[right])/two
    a = (xi[right]-xi[left])/two
    require(a.positive(), "collar radius not positive")
    major = a*xi[1].point((t+1/t)/2)
    require(m.abs_upper()+major.high() < outer_radius.low(),
            name+": ellipse exits the target disk")
    leftmost, rightmost = m.low()-major.high(), m.high()+major.high()
    if name == "K0":
        require(leftmost > xi[5].high() and rightmost < xi[4].low(),
                "K0 ellipse runs into K2 or K1")
    if name == "K1":
        require(leftmost > xi[6].high(),
                "K1 ellipse runs into K0")
    if name == "K2":
        require(rightmost < xi[3].low(),
                "K2 ellipse runs into K0")


def chart_for_finite(finite, row):
    p, parameter, orbit = finite.v.checked_packet(row)
    require(3 <= p <= 12, "invalid finite selected root")
    chart, R = finite.physical_positive_chart(p, orbit)
    scale = R / finite.v.Iv.point(F(1, 4) if p == 3 else F(1, 2**p))
    xi = {j: scale*orbit[j*p] for j in range(1,7)}
    # Cross-check the independent normalized coefficient construction.
    require(all(xi[j].low() <= chart[j].high() and
                chart[j].low() <= xi[j].high() for j in range(1,6)),
            "different normalized target chart")
    return p, xi, R


def tail_chart(finite):
    """Uniform p>=13 box: p=13 is the largest 4^-p error box.

    Under the upstream all-p proof:
       |xi_1 + u_1| <= 15246 * 4^-p,
       |xi_j + u_j| <= (30*15246 + 88*(4^j-1)/3)*4^-p.
    The latter induction is applied for *each* j=2,...,6; not only
    j=2,3,5 used in the earlier child-envelope application.
    """
    v, gain = finite.v, finite.gain
    _, u = v.isolate_model()
    q = F(1, 4**13)
    errors = {1: F(15246)}
    for j in range(2, 7):
        errors[j] = 30*F(15246) + F(88*(4**j-1), 3)
    xi = {j: -gain.pad(u[j], errors[j]*q) for j in range(1,7)}
    radius_floor = v.Iv.point(F(3, 20)*2**13)
    # By the all-p theorem -A_p * 4^-p > 3/20, hence
    # (-A_p) R_p > (3/20) 2^p. This grows with p.
    exact_floor = F(3, 20)*2**13
    require(radius_floor.low() <= exact_floor <= radius_floor.high() and
            radius_floor.low() > F(1200),
            "wrong outward all-period target-radius enclosure")
    check_order(xi)
    return xi, radius_floor


def certify() -> dict:
    elliptic_threshold_finite_logic()
    finite = load_verifier("tip_family_finite_p_wave_gain_20261116",
                           "tip_buf_finite")
    quad = load_verifier("canonical_wad_quadrilateral_moduli_20261116",
                         "tip_buf_quad")
    # Replays upstream 3..12 selected roots and the p>=13 realization
    # and SC gain inequalities. The KKL topology remains an analytic input.
    gain_rows = finite.certify()
    require([r["p"] for r in gain_rows] == list(range(3,13)),
            "the source gain chain lost a finite period")
    prior = json.loads(OLD.read_text(encoding="utf-8"))
    require([row["p"] for row in prior["periods"]] == list(range(3,13)),
            "selected dyadic p3..12 packets missing")

    inner_caps = []
    for label in INNER:
        _, hi = width_log_length_bounds(quad, INNER_T[label])
        pi_lo, pi_hi = quad.pi_range()
        log_lo, _ = quad.log_range(INNER_T[label])
        energy_hi = 2*pi_hi/log_lo
        require(energy_hi < INNER_B[label],
                label+": pinned peripheral width upper is unsupported")
        inner_caps.append(INNER_B[label])
    require(sum(inner_caps, F(0))/2 < MAX_NORM_TAIL,
            "incorrect strict nonnegative norm upper")

    results = []
    for row in prior["periods"]:
        p, xi, R = chart_for_finite(finite, row)
        check_order(xi)
        for label in INNER:
            ellipse_check(xi, R, label, INNER_T[label])
        t = OUTER_T[p]
        ellipse_check(xi, R, "outer", t)
        lo, hi = width_log_length_bounds(quad, t)
        excluded = p >= 11
        if excluded:
            check_cyclic_exclusion(hi, F(7, 2))
        results.append({
            "p": p,
            "outer_annulus_t": str(t),
            "outer_cyclic_hyperbolic_length_strict_upper": str(hi),
            "all_outer_incident_q_strictly_less_than_2": excluded,
            "inner_three_collars_verified": True,
            "candidate_endpoint_types_remaining": (6 if excluded else 10),
        })

    xi, R = tail_chart(finite)
    for label in INNER:
        ellipse_check(xi, R, label, INNER_T[label])
    ellipse_check(xi, R, "outer", TAIL_OUTER_T)
    lo, hi = width_log_length_bounds(quad, TAIL_OUTER_T)
    check_cyclic_exclusion(hi, F(3))
    # The full outer interval is absent from canonical support.
    # Each of the three remaining canonical local weights <= W(I) < B_I.
    return {
        "status": "PARTIAL: outer incident classes excluded p>=11; all inner q open",
        "source": "actual Y_{K,p}=U_p minus three Julia intervals, minimal 4-component marking",
        "p3_to_p12": results,
        "tail_all_p_ge_13": {
            "outer_annulus_t": str(TAIL_OUTER_T),
            "outer_cyclic_hyperbolic_length_strict_upper": str(hi),
            "all_outer_incident_q_strictly_less_than_2": True,
            "inner_three_collars_verified": True,
            "candidate_endpoint_types_remaining": 6,
        },
        "uniform_p_ge_11_canonical_norm_strict_upper": str(MAX_NORM_TAIL),
        "all_classes_enumerated": False,
        "any_inner_q_two_sided_certified": False,
        "any_positive_canonical_weight_certified": False,
        "numerical_only": [],
        "unresolved": [
            "six inner endpoint types each contain infinitely many possible isotopy classes",
            "all named inner q_gamma and exclusion of remaining winding classes",
            "whether the complete buffered WAD is zero or positive",
            "any uniform positive lower bound on its norm",
            "a source-faithful WAD-to-unbuffered A.1 gain identification",
        ],
    }


def main():
    out = certify()
    for row in out["p3_to_p12"]:
        print("p={p:2} t={outer_annulus_t}: outer excluded={all_outer_incident_q_strictly_less_than_2}; remaining endpoint types={candidate_endpoint_types_remaining}".format(**row))
    print("p>=13: t=1024; all outer-incident q_gamma < 2")
    print("p>=11: 0 <= ||W_can|| < 619/200; inner q_gamma remain OPEN")
    print("PASS: exact rational/interval certificates, conditional on stated covering and Landen theorems")


if __name__ == "__main__":
    main()
