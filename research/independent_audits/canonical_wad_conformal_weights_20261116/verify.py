#!/usr/bin/env python3
"""Exact rational checks for one-slit physical capacities, NOT KKL q_gamma.

No floating-point operations or numerical PDE solver. The continuum gluing and
Dirichlet-domain monotonicity arguments appear in NOTE.md, not in this program.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
TIP = ROOT / 'results/tip_KKL_tree_marked_breakage_20261109.json'
PARENT = ROOT / 'results/canonical_wad_electrode_incidence_20261116.json'
OUT = ROOT / 'results/canonical_wad_conformal_weights_20261116.json'
DEN = 1 << 256
PARAM = (-607918036626757496169199575185708826140,
         -607918036626757496169199575185708826139)
# (inner ellipse inside disk, outer ellipse enclosing disk,
#  rational strict lower, rational strict upper) for the physical condenser.
CHOICES = {
    'K0': (21, 22, Q(203,100), Q(207,100)),
    'K1': (49, 340, Q(107,100), Q(162,100)),
    'K2': (25, 90, Q(139,100), Q(196,100)),
}


def require(b: bool, msg: str) -> None:
    if not b:
        raise AssertionError(msg)


def sq_interval(a: int, b: int) -> tuple[int,int]:
    require(a <= b, 'interval order')
    low = 0 if a <= 0 <= b else min(a*a,b*b)
    high = max(a*a,b*b)
    return low // DEN, (high + DEN-1) // DEN


def orbit(s: dict) -> dict[int,tuple[Q,Q]]:
    p = s['source_parameter']
    require(p['denominator_power_of_two'] == 128 and
            (p['lower_numerator'],p['upper_numerator']) == PARAM,
            'PR68 source parameter must remain unchanged')
    a, b = (v << 128 for v in PARAM)
    res = {}
    for i in range(1,19):
        if i != 1:
            a,b = sq_interval(a,b)
            a += PARAM[0] << 128
            b += PARAM[1] << 128
        res[i] = (Q(a,DEN),Q(b,DEN))
    return res


def arctan_range(z: Q, n: int = 20) -> tuple[Q,Q]:
    require(0 < z < 1 and n > 0, 'arctan input')
    partial = sum(((-1)**j*z**(2*j+1)/Q(2*j+1) for j in range(n)), Q(0))
    tail = z**(2*n+1)/Q(2*n+1)
    return (partial,partial+tail) if n%2==0 else (partial-tail,partial)


def pi_range() -> tuple[Q,Q]:
    a,b = arctan_range(Q(1,5))
    c,d = arctan_range(Q(1,239))
    return 16*a-4*d, 16*b-4*c


def log_range(x: int, n: int=20) -> tuple[Q,Q]:
    """Certified rational bounds by log(x)=k log2+2 atanh((y-1)/(y+1))."""
    require(isinstance(x,int) and x>=2 and n>0, 'integer log domain')
    k = x.bit_length()-1
    y = Q(x,2**k)
    require(1 <= y < 2, 'log dyadic reduction')
    def series(q: Q) -> tuple[Q,Q]:
        require(Q(0) <= q <= Q(1,3), 'bounded log atanh argument')
        s = 2*sum((q**(2*j+1)/Q(2*j+1) for j in range(n)),Q(0))
        rem = 2*q**(2*n+1)/(Q(2*n+1)*(1-q*q))
        return s,s+rem
    a,b = series(Q(1,3))
    c,d = series((y-1)/(y+1))
    return k*a+c,k*b+d


def rect_interval(left:tuple[Q,Q], right:tuple[Q,Q]) -> tuple[tuple[Q,Q],tuple[Q,Q]]:
    """Center m and half-length a of [left,right], outward rational intervals."""
    ll,lu=left; rl,ru=right
    require(lu<rl, 'slit endpoint order')
    return ((ll+rl)/2,(lu+ru)/2), ((rl-lu)/2,(ru-ll)/2)


def ellipses(m:tuple[Q,Q], a:tuple[Q,Q], t_in:int,t_out:int) -> tuple[Q,Q]:
    """Check E(t_in) is inside D(0,1/4) and D is inside E(t_out).

    z=m+(a/2)(w+1/w); the semiaxes of E(t) are a(t+1/t)/2,
    a(t-1/t)/2. A disk of radius minor semiaxis about m is in E(t).
    """
    require(1<t_in<t_out, 'ellipse parameter order')
    mi = max(abs(m[0]),abs(m[1]))
    major = a[1]*(Q(t_in)+Q(1,t_in))/2
    minor = a[0]*(Q(t_out)-Q(1,t_out))/2
    require(mi+major < Q(1,4), 'inner ellipse must lie strictly inside U3')
    require(Q(1,4)+mi < minor, 'outer ellipse must enclose all of U3')
    return major, minor


def certify(s:dict, parent:dict) -> dict:
    require(s['scope'].startswith('ACTUAL KKL'), 'source geometry scope')
    require(s['tree']=='[x6,x3]', 'unchanged source tree')
    require(parent['canonical_definition']['weights_numerically_enclosed'] is False,
            'input canonical q has not already been certified')
    require(parent['canonical_definition']['proof_selected_wave_constructed'] is False,
            'not a proof-selected Wave')
    require(parent['geometry']['canonical_small_julia_sets']==
            'K0=[x9,x18]; K1=[x12,x3]; K2=[x6,x15]', 'correct Julia slits')
    require(parent['physical_free_outer_Dh']['h']=='1/1024' and
            parent['physical_free_outer_Dh']['strict_lower']=='3*h/5' and
            parent['physical_free_outer_Dh']['strict_upper']=='6*h/5',
            'prior certified physical condenser input')
    xs=orbit(s)
    require(xs[6][1] < xs[15][0] < xs[9][0] < xs[18][0]
            < xs[12][0] < xs[3][0] < Q(1,4), 'strict K2<K0<K1 order')
    endpoints = {'K0':(xs[9],xs[18]),
                 'K1':(xs[12],xs[3]),
                 'K2':(xs[6],xs[15])}
    p0,p1=pi_range()
    require(Q(333,106)<p0<p1<Q(22,7), 'Machin pi bounds')
    ranges={}
    for name,(inner,outer,low,high) in CHOICES.items():
        m,a=rect_interval(*endpoints[name])
        major,minor=ellipses(m,a,inner,outer)
        # These annuli are ALSO genuinely contained in all three-hole Y_K:
        # E(t_in) does not hit a neighboring slit, despite the outer ellipse.
        if name=='K1':
            require(m[0]-major > xs[18][1], 'K1 collar must miss K0')
        elif name=='K2':
            require(m[1]+major < xs[9][0], 'K2 collar must miss K0')
        # No such all-hole collar statement is made for K0 at t_in=21.
        l_in,u_in = log_range(inner)
        l_out,u_out=log_range(outer)
        require(Q(0)<l_in<u_in<l_out<u_out,'positive, increasing log bounds')
        require(low < 2*p0/u_out and 2*p1/l_in < high,
                'all displayed strict physical-condenser capacity bounds')
        ranges[name]={
            'ellipse_t_inside_disk':inner,
            'ellipse_t_enclosing_disk':outer,
            'exact_analytic_lower':'2*pi/log('+str(outer)+')',
            'exact_analytic_upper':'2*pi/log('+str(inner)+')',
            'strict_rational_lower':str(low),
            'strict_rational_upper':str(high),
            'physical_condenser_status':'certified, conditional on written variational/gluing proof',
            'canonical_quadrilateral_width':None,
        }
    # A separately embedded K0 collar must stop before the K2 slit;
    # this gives geometric input only, not an ideal-quadrilateral bound.
    m0,a0=rect_interval(*endpoints['K0'])
    rad11 = a0[1]*(Q(11)+Q(1,11))/2
    require(max(abs(m0[0]),abs(m0[1]))+rad11 < Q(1,4), 'K0 t=11 within disk')
    require(m0[0]-rad11 > xs[15][1], 'K0 collar must miss K2')
    require(m0[1]+rad11 < xs[12][0], 'K0 collar must miss K1')
    # Log24>pi and log22<pi are exact-rational verifications, not floats.
    require(log_range(24)[0] > p1, 'log24>pi')
    require(log_range(22)[1] < p0, 'log22<pi')
    return {
      'schema_version':1,
      'source_tip':'results/tip_KKL_tree_marked_breakage_20261109.json',
      'source_audit':'results/canonical_wad_electrode_incidence_20261116.json',
      'arithmetic':'exact Fraction and integer outward 256-bit orbit, rational Machin pi and atanh log brackets; no floating point',
      'target_surface':'U3\\(K0 union K1 union K2), U3=D(0,1/4), minimal four-component marking',
      'certified_auxiliary_target_slit_outer_condenser_bounds':ranges,
      'auxiliary_condenser_theorem':'For boundary values on one real slit and the whole outer circle, floating other collinear zero-thickness slits do not affect Dirichlet energy: symmetrize then glue traces across floating slits. For a single slit, Joukowski ellipses bracket its condenser capacity.',
      'embedded_collar_t_for_each_slit':{'K0':11,'K1':49,'K2':25},
      'auxiliary_capacity_consequences':{'K0_exceeds_2':True, 'K1_below_2':True, 'K2_below_2':True},
      'canonical_WAD':{
          'formula':'W_can(gamma)=max(q_gamma-2,0)',
          'quadrilateral_enclosures_certified':False,
          'excluded_remaining_classes_proved':False,
          'support':None,
          'total_weight_certified_bounds':None,
          'horizontal_vertical_projected_support':None,
          'horizontal_vertical_weight_certified_bounds':None,
          'support_cardinality_upper_bound_from_KKL':10,
          'warning':'Physical condenser capacities are NOT per-class universal-cover q_gamma; no WAD support inference is allowed.'},
      'source_electrode_Dh':{
          'height':'1/1024',
          'strict_lower':'3/5120',
          'strict_upper':'3/2560',
          'status':'inherited from unchanged canonical_wad_electrode_incidence_20261116 finite/analytic certificate'},
      'transfer':{
          'physical_electrode_incidence_hypothesis':False,
          'hypothesis_failure':'W_can is on U3\\K, not the source C_h; deck f_* identifies A_X and B_X and iota is nonproper on the attachment',
          'positive_kappa_and_C_certified':False,
          'scalar_upper_and_lower_inequality_decided':False,
          'no_positive_constants_possible_proved':False,
          'warning':'Failure of a sufficient geometric clause is not a mathematical disproof of an accidentally true scalar inequality.'},
      'numerical_only':[],
      'open':['All q_gamma two-sided conformal enclosures and exhaustive q<=2 exclusion',
              'Canonical WAD support and norm and h+v projection weights',
              'Intrinsic scalar transfer bounds and constants for the canonical WAD'],
    }


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    g=parser.add_mutually_exclusive_group()
    g.add_argument('--check-manifest',action='store_true')
    g.add_argument('--write-manifest',action='store_true')
    args=parser.parse_args()
    obj=certify(json.loads(TIP.read_text()),json.loads(PARENT.read_text()))
    if args.write_manifest:
        OUT.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n',encoding='utf-8')
        print('WROTE',OUT)
    elif args.check_manifest:
        require(json.loads(OUT.read_text())==obj,'manifest drift')
        print('PASS exact physical condenser enclosures; canonical q_gamma remains OPEN')
    else:
        print(json.dumps(obj,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
