#!/usr/bin/env python3
"""Read-only, outward-rational defect enclosures for two marked source Waves.

This does NOT calculate optimal KKL Waves or decide the sign of the free
canonical defect. Geometry and the elliptic cross-ratio formula are written
and proved in NOTE.md; this program checks their arithmetic preconditions.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PRIOR_DIR = ROOT / "research/independent_audits/real_primitive_tip_family_canonical_width_sandwich_20261116"

spec = importlib.util.spec_from_file_location("tip_gain_prior_sandwich", PRIOR_DIR / "verify.py")
assert spec is not None and spec.loader is not None
s = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = s
spec.loader.exec_module(s)
v = s.v

# Strict decimal endpoints (units 10^-3), NOT measured canonical values.
# The broad interval contains zero at every period.
DEFECT_3_TO_12 = {
    3: (-1919, 2298), 4: (-1838, 2225), 5: (-1820, 2379),
    6: (-1816, 2449), 7: (-1815, 2484), 8: (-1814, 2504),
    9: (-1814, 2516), 10: (-1814, 2524), 11: (-1814, 2529),
    12: (-1814, 2533),
}
TAIL_DEFECT = (F(-224, 100), F(257, 100))  # strict, all p >= 13
TAIL_CHILD_CAP = F(31, 25)  # 1.24; deliberately coarse
TWO = v.Iv.point(2)
ONE = v.Iv.point(1)


def check(truth: bool, why: str) -> None:
    if not truth:
        raise AssertionError(why)


def child_crossratio(a: v.Iv, b: v.Iv, c: v.Iv, d: v.Iv) -> v.Iv:
    """Full half-plane path modulus for disjoint boundary intervals [a,b],[c,d].

    The right-half-plane logarithmic universal cover has modulus
    K(k)/K(sqrt(1-k**2)), with k**2=(b-a)(d-c)/((c-a)(d-b)).
    """
    check(a.lt(b) and b.lt(c) and c.lt(d), "child endpoint arcs overlap or reorder")
    k2 = (b-a)*(d-c)/((c-a)*(d-b))
    check(k2.positive() and k2.lt(ONE), "child cross ratio outside (0,1)")
    return v.upper_envelope_elliptic(k2.sqrt())


def acos_positive(z: v.Iv) -> v.Iv:
    """acos(0<z<1) with two rigorously convergent arctangent charts.

    The upstream acos_pos chart requires sqrt((1-z)/(1+z)) < 4/5;
    near zero (the coarse x_3 gate) use pi/2-atan(z/sqrt(1-z^2)).
    """
    check(z.positive() and z.lt(ONE), "acos input outside (0,1)")
    root = ((ONE-z)/(ONE+z)).sqrt()
    if root.high() < F(4, 5):
        return TWO*v.atan_unit(root)
    other = z/(ONE-z.square()).sqrt()
    check(other.high() < F(4,5), "neither certified arctangent chart applies")
    return v.pi_interval()/TWO - v.atan_unit(other)


def sharp_child_plane(xp: v.Iv, x2: v.Iv, x5: v.Iv,
                      x4: v.Iv, alpha: v.Iv) -> v.Iv:
    """Source T'=[-xp,xp] with true S1/S3 endpoint intervals.

    After reflecting t -> pi-t, the four slit angles are
    acos(x4/xp), acos(-x2/xp), acos(-x5/xp), acos(alpha/xp).
    The lower child is its conjugate and has the same upper bound.
    """
    check(xp.positive() and x2.negative() and x5.negative()
          and x4.positive() and alpha.positive(), "wrong source cut signs")
    args = (x4/xp, (-x2)/xp, (-x5)/xp, alpha/xp)
    check(all(z.positive() and z.lt(ONE) for z in args),
          "source cuts outside [-xp,xp] or arccos interval domain")
    return child_crossratio(*(acos_positive(z) for z in args))


def coarse_child_plane(xp: v.Iv, x2: v.Iv, x5: v.Iv, x3: v.Iv) -> v.Iv:
    """Enlarge S1 to (-xp,x2), S3 to (x5,x3); no alpha/x4 needed."""
    check(xp.positive() and x2.negative() and x5.negative() and x3.negative(),
          "wrong coarse source signs")
    args = ((-x2)/xp, (-x5)/xp, (-x3)/xp)
    check(all(z.positive() and z.lt(ONE) for z in args),
          "coarse source cuts outside slit")
    return child_crossratio(v.Iv.point(0), *(acos_positive(z) for z in args))


def defect_bounds(parent_rad_lower: F, parent_env_upper: F,
                  child_upper: F) -> tuple[F, F]:
    """With L<Wrad<=P< U and 2Wrad<=C_+,C_-< C:

    2/C - 1/L < 1/C_+ + 1/C_- - 1/P < 1/L - 1/U.
    """
    check(F(0) < parent_rad_lower < parent_env_upper and
          2*parent_rad_lower < child_upper, "invalid width sandwich")
    return 2/child_upper - 1/parent_rad_lower, 1/parent_rad_lower - 1/parent_env_upper


def pad(z: v.Iv, delta: F) -> v.Iv:
    check(delta >= 0, "negative error bound")
    return v.Iv.hull(z.low()-delta, z.high()+delta)


def model_child_envelope(p: int, orbit: list[v.Iv]) -> v.Iv:
    """All-p certified normalized x_jp boxes, inherited (5.3) of sandwich.

    -A_p > 0 is the positive affine scale, so xi_j=(-A_p)x_jp=-u_j.
    """
    check(isinstance(p, int) and p >= 13, "model error only proved for p>=13")
    q = F(1, 4**p)
    err = {1: F(15246)}
    for j in (2, 3, 5):
        err[j] = F(30*15246)+F(88*(4**j-1), 3)
    xi = {j: -pad(orbit[j], err[j]*q) for j in (1, 2, 3, 5)}
    return coarse_child_plane(xi[1], xi[2], xi[5], xi[3])


def run() -> dict:
    # Re-execute old pinned Fraction / outward 2^-512 certificates read-only.
    prior = s.run()
    check(prior == json.loads(s.RESULT.read_text()),
          "upstream sandwich packet changed: must not silently trust it")
    check(prior["schema"] == "real-primitive-tip-canonical-wave-sandwich/v1",
          "upstream schema drift")
    mark = s.check_marking()
    check(mark["A1_parent_base"] == [9,0,1] and mark["A1_crest"] == 0,
          "parent base or crest changed")
    check(mark["source_crossing_spans"] == [3,3] and
          mark["cover_crossing_endpoints"] == [[3,1],[9,7]] and
          mark["cover_avoiding_span"] == 5 and mark["source_avoiding_span"] == 7,
          "different immersion and cover operators conflated")
    check(s.BLOCKS[0] == (18,19,0,1,2) and
          s.BLOCKS[1] == (3,4) and s.BLOCKS[9] == (16,17),
          "A.3.2 blocks drift")

    old = json.loads(s.OLD.read_text())
    source = {r["p"]: r for r in old["periods"]}
    rows = {r["p"]:r for r in prior["finite"]}
    check(sorted(source) == list(range(3,13)), "finite source periods missing")
    check(sorted(rows) == list(range(3,17)), "upstream sandwich finite periods missing")
    result = []
    for p in range(3,13):
        p2, parameter, orbit = v.checked_packet(source[p])
        check(p2 == p, "source packet index mismatch")
        alpha = v.alpha_interval(p, parameter, orbit)
        xp, x2, x5, x4, x3 = (orbit[j*p] for j in (1,2,5,4,3))
        check((-xp).lt(-x4) and (-x4).lt(x2) and x2.lt(x5) and
              x5.lt(-alpha) and (-alpha).lt(x3), "source slit real order")
        sharp = sharp_child_plane(xp,x2,x5,x4,alpha)
        coarse = coarse_child_plane(xp,x2,x5,x3)
        check(sharp.lt(coarse), "child enlarged interval failed monotonicity")
        check(sharp.high() < F(2), "buffered canonical KKL arc might not vanish")
        row=rows[p]
        l=F(row["round_lower_1e-7_strict"][0], 10**7)
        u=F(row["full_lift_upper_1e-7_strict"][1], 10**7)
        lower,upper=defect_bounds(l,u,sharp.high())
        dlo,dhi=DEFECT_3_TO_12[p]
        check(F(dlo,1000)<lower and upper<F(dhi,1000),
              f"p={p}: proposed strict defect enclosure not certified")
        result.append((p, dlo, dhi, v.bracket_dec(sharp)))

    # The p=13 interval is the WIDEST normalized box for all p>=13.
    # Monotonic interval extension then covers the entire infinite tail.
    t, model_orbit = v.isolate_model()
    check(t.inside(v.MODEL_LO,v.MODEL_HI), "limiting model root drift")
    child_cap = model_child_envelope(13, model_orbit)
    check(child_cap.high()<TAIL_CHILD_CAP,
          "p>=13 child plane-slit envelope not < 1.24")
    for p in (14,15,16,17):
        smaller=model_child_envelope(p,model_orbit)
        check(child_cap.low() <= smaller.low() and smaller.high() <= child_cap.high(),
              "model error boxes not nested")
    for p in range(13,17):
        row=rows[p]
        check(F(row["round_lower_1e-7_strict"][0],10**7)>F(26,100) and
              F(row["full_lift_upper_1e-7_strict"][1],10**7)<F(78,100),
              f"p={p}: sandwich not within universal high-p bounds")
    check(s.LIMIT_RADIAL_LOW-F(7_000_000,4**17)>F(26,100),
          "the asymptotic radial estimate is not strong enough at p=17")
    check(s.model_plane_envelope(17,model_orbit).high()<F(78,100),
          "full-plane parent upper tail failed")
    low,high=defect_bounds(F(26,100),F(78,100),TAIL_CHILD_CAP)
    check(TAIL_DEFECT[0]<low and high<TAIL_DEFECT[1],
          "uniform two-sided defect bracket failed")
    return {"finite":result,"p_ge_13":{
        "child_full_plane_upper_strict":str(TAIL_CHILD_CAP),
        "defect_bounds_strict":list(map(str,TAIL_DEFECT)),
        "model_13_child_interval_1e-7":v.bracket_dec(child_cap),
    }}


def main() -> None:
    data=run()
    for p,lo,hi,child in data["finite"]:
        print(f"p={p:2d}: {lo}/1000 < D_p < {hi}/1000, child full-plane envelope in ({child[0]},{child[1]})*1e-7")
    print("all p>=13: -2.24 < D_p < 2.57, conditional physical ideal marking M")
    print("PASS: exact/outward-interval inequalities only; canonical sign remains OPEN")


if __name__ == "__main__":
    main()
