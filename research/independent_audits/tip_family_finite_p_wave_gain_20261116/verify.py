#!/usr/bin/env python3
"""Finite primitive-tip independent maximal A.1-Wave gain, p=3,...,12.

Arithmetic: exact Fraction + outward 2^-512 interval methods from the
immutable upstream audits.  The analytic foliation and SC/density arguments,
and conditional physical prime-end identification M, are in NOTE.md.
NO numerical optimizer, floating-point decision, or supremum attainment.
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
UPSTREAM = ROOT / "research/independent_audits/tip_family_limiting_wave_gain_20261116/verify.py"
spec = importlib.util.spec_from_file_location("finite_gain_pinned_limiting", UPSTREAM)
if spec is None or spec.loader is None:
    raise RuntimeError("pinned limiting gain verifier unavailable")
lim = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = lim
spec.loader.exec_module(lim)
gain, v = lim.gain, lim.v
I, ONE, TWO = v.Iv, v.ONE, v.TWO

# Entire chart decisions, fixed in advance; all are rational.
# Segment Q={Re z>0, |z+d|<L}; h=L-d, T=sqrt(L^2-d^2).
SEGMENTS = {3: (F(83, 100), F(31, 10)),
            4: (F(88, 100), F(31, 10))}
SMALL_SEMIDISK = F(7, 5)
# Strict displayed rational floors/ceilings (not rounded measurements).
PARENT_FLOORS = {3: F(49, 100), 4: F(511, 1000),
                 **{p: F(581, 1000) for p in range(5, 13)}}
CHILD_CEILINGS = {3: F(974, 1000), 4: F(985, 1000),
                  **{p: F(988, 1000) for p in range(5, 13)}}
GAIN_FLOORS = {3: F(1, 100), 4: F(7, 100),
               **{p: F(3, 10) for p in range(5, 13)}}
CHILD_DOMAIN_SAVING = F(1, 5_000_000)  # strict uniform actual-source saving
# The certified omitted box is (s,s+1) x (0,1), with s chosen from
# the physical source radius separately for each primitive period.


def require(ok: bool, why: str) -> None:
    if not ok:
        raise AssertionError(why)


def cosh_positive(t: I) -> I:
    """cosh(t)=1+2sinh(t/2)^2, with upstream rational Taylor remainder."""
    require(t.low() >= 0 and t.high() < 8, "cosh outside certified domain")
    return ONE + TWO * v.sinh_iv(t / TWO).square()


def physical_positive_chart(p: int, x: list[I]) -> tuple[dict[int, I], I]:
    """Physical x_(jp), not x_j; xi=(-A_p)z, where A_p<0."""
    require(type(p) is int and 3 <= p <= 12, "finite physical chart period")
    A = ONE
    for j in range(1, p):
        A = A * TWO * x[j]
    require(A.negative(), "positive scale needs A_p<0")
    scale = -A
    coordinates = {j: scale*x[j*p] for j in (1, 2, 3, 4, 5)}
    R = F(1, 4) if p == 3 else F(1, 2**p)
    require((scale*I.point(R)).positive(), "normalized target radius vanished")
    return coordinates, scale*I.point(R)


def verify_full_target_disk(x: dict[int, I], normalized_R: I, h: F) -> None:
    """Whole embedded competitor, not sampled leaves: |J(-exp z)|<radius.

    |cosh(s+it)|<=cosh(s), 0<=s<h; m and r are exact interval cuts.
    """
    m = (x[2] + x[1])/TWO
    r = (x[1] - x[2])/TWO
    require(r.positive(), "nonpositive Joukowski radius")
    bound = m.abs_upper() + r.high()*cosh_positive(I.point(h)).high()
    require(bound < normalized_R.low(),
            "complete parent quadrilateral exits physical target disk")


def circular_segment_width(x: dict[int, I], h: F, T: F) -> I:
    """Exact SC competitor for right circular segment with vertices +/-iT.

    The Moebius (z-iT)/(z+iT) sends the segment to a wedge of opening
    theta=2 atan(h/T). Power gamma=pi/theta sends it to a half-plane.
    On diameter z=it, absolute boundary values are
       exp(-2 gamma atanh(t/T)).
    The symmetric electrode cross-ratio is
       k=sinh(gamma*(atanh(b/T)-atanh(a/T)))/
         sinh(gamma*(atanh(b/T)+atanh(a/T))).
    """
    require(h > 0 and T > 0, "invalid segment dimensions")
    a, b, _, _ = lim.parent_angle_data(x[1], x[2], x[5], x[3])
    TT = I.point(T)
    require(b.lt(TT) and TT.lt(v.pi_interval()),
            "segment does not separate left tip from deck seam")
    ratio = I.point(h)/TT
    require(ratio.positive() and ratio.high() < F(4, 5),
            "wedge angle arctan chart invalid")
    gamma = v.pi_interval()/(TWO*v.atan_unit(ratio))
    aa = v.log_iv((TT+a)/(TT-a))/TWO
    bb = v.log_iv((TT+b)/(TT-b))/TWO
    require(aa.positive() and aa.lt(bb), "segment ordered electrodes invalid")
    u = gamma*(bb-aa)
    w = gamma*(bb+aa)
    require(u.positive() and u.lt(w) and w.high() < 4,
            "segment sinh series outside certified interval")
    k = v.sinh_iv(u)/v.sinh_iv(w)
    require(k.positive() and k.lt(ONE), "bad segment SC cross-ratio")
    return v.upper_envelope_elliptic(k)


def certify_source_inside_target(p: int, c: I, x: list[I]) -> None:
    """Direct Rouché boundary test that central V_p is compact in U_p.

    G(z)=d+A z^2+E(z), |E|<=tail on |z|<=R.  Check
    |A|R^2>|d|+tail+R, implying |G|>R on |z|=R.
    Thus G(0)=x_p in U and its central preimage component cannot
    meet the boundary of U. The strict estimate uses no root sampling.
    """
    R = F(1, 4) if p == 3 else F(1, 2**p)
    d, A, tail = I.point(0), I.point(0), F(0)
    for j in range(1, p+1):
        tail = 2*d.abs_upper()*tail+(A.abs_upper()*R*R+tail)**2
        A = ONE if j == 1 else TWO*d*A
        d = d.square()+c
    require(A.negative() and d.positive() and d.high() < R,
            "central quadratic-like return chart invalid")
    require(-A.high()*R*R-d.abs_upper()-tail > R,
            "source V_p not certified inside U_p")


def source_missing_box_start(p: int, xp: I) -> int:
    """Find an excluded (s,s+1)x(0,1) box from exact positive Taylor sums.

    exp(s)>sum(s**n/n!, n=0..24), exp(-s)<1, so
    sinh(s)>(sum-1)/2. The search is finite and rejects failed gates.
    """
    require(type(p) is int and 3 <= p <= 12 and xp.positive(),
            "source exclusion requires a physical positive critical value")
    R = F(1, 4) if p == 3 else F(1, 2**p)
    for s in range(2, p+1):
        lower_exp = sum((F(s**n, math.factorial(n))
                         for n in range(25)), F(0))
        lower_sinh = (lower_exp - 1)/2
        if xp.low()*lower_sinh > R:
            return s
    raise AssertionError("physical source cutoff box could not be certified")


def strict_child_domain_cap(p: int, xp: I, x2: I, x5: I,
                            x4: I, alpha: I) -> tuple[I, I]:
    """Upper SC metric restricted to ACTUAL source V_p, not the plane.

    The reflected upper-side electrodes are e=(pi-d,pi-c,pi-b,pi-a).
    On the whole right-half-plane log cover F'=product(z-i*e_j)^(-1/2).
    The SC electrode-gap side H<=pi/sqrt((b-a)*(d-c)); |F'|/H
    has full plane-lift area E_p and periodizes to an admissible metric.

    The separately certified unit box (s,s+1)x(0,1) is outside U_p:
       |xp*cosh(z)| >= xp*sinh(s)>R_p.
    As 0<e_j<pi<4, each |z-i*e_j|<s+5 on the box, so its
    missing energy exceeds (b-a)*(d-c)/(16*(s+5)^4) > 1/5,000,000.
    This is a strictly tighter actual-domain upper for both children.
    """
    s = source_missing_box_start(p, xp)
    args = (x4/xp, (-x2)/xp, (-x5)/xp, alpha/xp)
    require(all(z.positive() and z.lt(ONE) for z in args),
            "child angle branches not in (0,1)")
    a, b, c, d = (gain.acos_positive(z) for z in args)
    require(a.lt(b) and b.lt(c) and c.lt(d) and d.lt(v.pi_interval()),
            "child reflected electrode order invalid")
    product = (b-a)*(d-c)
    require(product.low() > F(9, 100),
            "SC density missing-energy rational gap not certified")
    require(product.low() / (16*(s+5)**4) > CHILD_DOMAIN_SAVING,
            "not enough missing SC energy on certified physical box")
    envelope = gain.sharp_child_plane(xp, x2, x5, x4, alpha)
    cap = envelope - I.point(CHILD_DOMAIN_SAVING)
    require(cap.positive() and cap.lt(envelope),
            "domain refinement lost its strict sign")
    return cap, envelope


def finite_case(p: int, c: I, orbit: list[I]) -> dict:
    xp, x2, x3, x4, x5 = (orbit[j*p] for j in (1, 2, 3, 4, 5))
    alpha = v.alpha_interval(p, c, orbit)
    certify_source_inside_target(p, c, orbit)
    x, radius = physical_positive_chart(p, orbit)
    if p in SEGMENTS:
        h, T = SEGMENTS[p]
        verify_full_target_disk(x, radius, h)
        parent = circular_segment_width(x, h, T)
        construction = "right-circular-segment"
    else:
        verify_full_target_disk(x, radius, SMALL_SEMIDISK)
        parent = lim.parent_semidisk_width(
            x[1], x[2], x[5], x[3], SMALL_SEMIDISK)
        construction = "right-semidisk"
    cap, plane = strict_child_domain_cap(p, xp, x2, x5, x4, alpha)
    require(parent.low() > PARENT_FLOORS[p],
            f"p={p}: proposed parent floor not certified")
    require(cap.high() < CHILD_CEILINGS[p],
            f"p={p}: proposed domain-sensitive child cap not certified")
    defect_lower = TWO/cap - ONE/parent
    require(defect_lower.low() > GAIN_FLOORS[p],
            f"p={p}: positive independently optimized gain not certified")
    require(2/CHILD_CEILINGS[p] - 1/PARENT_FLOORS[p] > GAIN_FLOORS[p],
            f"p={p}: displayed rational sign would not follow")
    return {"p": p, "construction": construction,
            "parent_competitor_strict_1e-6": v.bracket_dec(parent, 6),
            "child_actual_upper_strict_1e-6": v.bracket_dec(cap, 6),
            "child_plane_upper_strict_1e-6": v.bracket_dec(plane, 6),
            "defect_strict_lower_1e-6": v.bracket_dec(defect_lower, 6),
            "proved_parent_gt": str(PARENT_FLOORS[p]),
            "proved_child_lt": str(CHILD_CEILINGS[p]),
            "proved_D_gt": str(GAIN_FLOORS[p])}


def certify() -> list[dict]:
    # Includes exact all-p predecessor and its complete read-only finite chain.
    lim.certify()
    old = json.loads(gain.s.OLD.read_text())
    require([row["p"] for row in old["periods"]] == list(range(3, 13)),
            "ten dyadic primitive-tip source packets not found")
    require(gain.s.BLOCKS[0] == (18, 19, 0, 1, 2)
            and gain.s.BLOCKS[1] == (3, 4)
            and gain.s.BLOCKS[9] == (16, 17),
            "immersion iota* not kept distinct from covering f*")
    answer = []
    for row in old["periods"]:
        p, c, orbit = v.checked_packet(row)
        answer.append(finite_case(p, c, orbit))
    return answer


def main() -> None:
    for row in certify():
        print(f'p={row["p"]:2d} {row["construction"]}: '
              f'P>{row["proved_parent_gt"]}, C<{row["proved_child_lt"]}, '
              f'D>{row["proved_D_gt"]}; '
              f'interval D*1e6={row["defect_strict_lower_1e-6"]}')
    print("PASS: all p>=3 gain; p=3..12 finite exact/outward bounds, "
          "p>=13 imported; actual KKL reading conditional on M; "
          "pairable-parent loss remains")


if __name__ == "__main__":
    main()
