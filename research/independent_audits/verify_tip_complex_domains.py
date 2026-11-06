#!/usr/bin/env python3
"""Exact 2^-224 interval margins for complex 3/9 tip returns.
Analytic Rouché, Riemann-Hurwitz and connectedness are imported separately.
"""
from __future__ import annotations
from pathlib import Path
import argparse
import json
from verify_real_nested_3_9 import (
    Interval, ZERO, ONE, UNIT, parameter, iterate, orbit_and_derivative
)
from verify_period27_misiurewicz_tip import TIP_K, certify as real_tip
from verify_complex_quadratic_like_3_9 import (
    abs_upper, abs_lower, interval_gap, evaluate_bounds, rouche_margin
)

U3, U9, SMALL9, OLD9 = UNIT//4, UNIT//32, 27*UNIT//1024, 13*UNIT//512


def certify() -> dict:
    assert real_tip()["critical_preperiod"] == 10
    lo, hi = parameter(TIP_K), parameter(TIP_K + 1)
    L, H = iterate(ZERO, lo, 18), iterate(ZERO, hi, 18)
    assert (L[18]+L[9]).positive() and (H[18]+H[9]).negative()
    C = Interval(lo.lo, hi.hi)
    X, _ = orbit_and_derivative(C, 27)
    A = [ZERO, ONE]
    for j in range(1,9):
        A.append(X[j]*A[j].times(2))
    assert all(abs_lower(A[j])>0 for j in range(1,10))
    b3 = evaluate_bounds(X,A,U3,3)
    b9 = evaluate_bounds(X,A,U9,9)
    bs = evaluate_bounds(X,A,SMALL9,9)
    old = evaluate_bounds(X,A,OLD9,9)
    assert 0<SMALL9<U9<U3
    margins={
        "rouche_period3":rouche_margin(X,b3,3,U3),
        "rouche_period9":rouche_margin(X,b9,9,U9),
        "rouche_shrink_period9":rouche_margin(X,bs,9,U9)
    }
    assert all(v>0 for v in margins.values())
    # The old shrink's nonpositive lower bound does not refute domains.
    assert rouche_margin(X,old,9,U9)<=0
    for p,b,target in ((3,b3,U3),(9,b9,U9)):
        assert abs_upper(X[p])<target
        assert all(abs_upper(X[j])+b.deviation[j]<2*UNIT for j in range(p))
        assert all(abs_lower(X[j])>b.deviation[j] for j in range(1,p))
    assert all(abs_lower(X[j])>bs.deviation[j] for j in range(1,9))
    gaps={}
    for p,b in ((3,b3),(9,bs)):
        values=[interval_gap(X[i],X[j])-b.deviation[i]-b.deviation[j]
                for i in range(p) for j in range(i+1,p)]
        gaps[p]=min(values)
        assert gaps[p]>0
    nested=min(U3-abs_upper(X[j])-b9.deviation[j] for j in (0,3,6,9))
    assert nested>0
    I3, I9 = Interval(X[6].lo,X[3].hi),Interval(X[9].lo,X[18].hi)
    assert I9.strictly_inside(I3)
    assert -U3<I3.lo<0<I3.hi<U3
    assert -U9<I9.lo<0<I9.hi<U9
    for p,I in ((3,I3),(9,I9)):
        images=iterate(I,C,p)
        assert all(images[i].below(images[j]) or images[j].below(images[i])
                   for i in range(p) for j in range(i+1,p))
        assert all(images[j].excludes_zero() for j in range(1,p))
    assert X[9].strictly_inside(I3) and X[18].strictly_inside(I3)
    assert abs_lower(X[1])>U9

    def lower_dec(a):
        n=a*10**9//UNIT
        return f"{n//10**9}.{n%10**9:09d}"
    return {
        "status":"EXACT_NONATTRACTING_TIP_COMPLEX_3_9_MARGIN_PASS",
        "parameter":"root of P18(c)+P9(c)=0 in exact 2^-128 bracket",
        "target_radii":{"U3":"1/4","U9":"1/32","V9_shrink":"27/1024"},
        "lower_rational_margins":{
            **{k:lower_dec(v) for k,v in margins.items()},
            "three_phase_separation":lower_dec(gaps[3]),
            "nine_phase_separation":lower_dec(gaps[9]),
            "four_outer_containment":lower_dec(nested)
        },
        "topological_deductions":"Using classical Rouche and Riemann-Hurwitz: proper degree-two Jordan quadratic-like restrictions at both 3 and 9, connected little filled Julia sets, K9 subset K3, phase disjointness and 9-to-3 refinement at the nonattracting tip",
        "limits":"No Levin p2 Green-level boundary condition, KL Jordan puzzle, actual renormalization-ray projection, groupoid or MLC closure"
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--check-manifest",action="store_true")
    p.add_argument("--print-json",action="store_true")
    args=p.parse_args()
    o=certify()
    rendered=json.dumps(o,indent=2,sort_keys=True)+"\n"
    if args.check_manifest:
        manifest=Path(__file__).resolve().parents[2]/"results"/"tip_complex_domains.json"
        assert manifest.read_text(encoding="utf-8")==rendered
    print(rendered if args.print_json else o["status"],end="" if args.print_json else "\n")

if __name__=="__main__":
    main()
