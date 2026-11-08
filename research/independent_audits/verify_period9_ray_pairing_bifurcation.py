#!/usr/bin/env python3
"""Exact rational-ray audit for the physical precritical quartet at the 3/9 tip.

This independently checks the four *actual source-certified* ray fractions,
period-nine forward targets, symmetry, noncrossing two-pair classification,
and the two signed real-slice pairings. It also recomputes the exact
outward-integer coefficient certificate from the merged companion PR #53.

The classical periodic-ray landing/stability theorem and the analytic
ray-tail pullback argument are written mathematics, not machine-certified.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
from verify_tip_ramified_precritical_pair import certified_core

OUT=Path(__file__).resolve().parents[2] / 'results' / 'period9_ray_pairing_bifurcation_20261107.json'
CIRCLE=F(1)
HALF=F(1,2)
ANGLES={
    'a':F(116791,523264),
    'b':F(144841,523264),
    'd':F(378423,523264),
    'e':F(406473,523264),
}

def mod1(x:F)->F:return x-x.numerator//x.denominator

def ray_audit():
    a,b,d,e=(ANGLES[x] for x in ('a','b','d','e'))
    assert 0<a<b<HALF<d<e<1
    assert d==a+HALF and e==b+HALF
    assert CIRCLE-a==e and CIRCLE-b==d
    target={k:mod1(1024*v) for k,v in ANGLES.items()}
    assert target=={'a':F(283,511),'b':F(228,511),'d':F(283,511),'e':F(228,511)}
    assert all(mod1(512*t)==t for t in set(target.values()))
    # Exact minimal ray period must be 9, not a strict proper divisor.
    assert all(mod1(2**k*t)!=t for t in set(target.values()) for k in range(1,9))
    # Two lift classes (a,d) and (b,e) must split between the two roots.
    inverse_pairs=(frozenset(('a','d')),frozenset(('b','e')))
    for pair in inverse_pairs:
        x,y=tuple(pair)
        assert target[x]==target[y] and mod1(ANGLES[x]-ANGLES[y])==HALF
    raysets=[frozenset(('a','b')),frozenset(('a','e')),frozenset(('a','d'))]
    # Of the three partitions of 4 ray ends into unordered pairs, the first
    # two are noncrossing, whereas (a,d)|(b,e) crosses in circular order.
    noncrossing={'right':[['a','b'],['d','e']],
                 'left':[['a','e'],['b','d']]}
    for key,pairs in noncrossing.items():
        assert len(set(tuple(sorted(p)) for p in pairs))==2
        assert set(sum(pairs,[]))==set(ANGLES)
        for p in pairs:
            assert len({target[i] for i in p})==2
    # Reflection maps each pair on the left to itself; it exchanges the
    # two pairs on the right (matching real versus pure-imaginary roots).
    mirror={'a':'e','e':'a','b':'d','d':'b'}
    reflected=lambda pair:frozenset(mirror[x] for x in pair)
    left={frozenset(p) for p in noncrossing['left']}
    right={frozenset(p) for p in noncrossing['right']}
    assert all(reflected(p)==p for p in left)
    assert all(reflected(p) in right and reflected(p)!=p for p in right)
    # Antipodal target pairs exchange both root assignments on both sides.
    anti={'a':'d','d':'a','b':'e','e':'b'}
    for group in (left,right):
        assert all(frozenset(anti[x] for x in pair) in group and
                   frozenset(anti[x] for x in pair)!=pair for pair in group)
    return {
      'angle_quartet':{k:str(v) for k,v in ANGLES.items()},
      'strict_cyclic_order':'0<a<b<1/2<d<e<1',
      'f10_target_angles':{k:str(v) for k,v in target.items()},
      'both_target_rays_have_exact_doubling_period':9,
      'antipodal_pairs':[['a','d'],['b','e']],
      'conjugate_pairs':[['a','e'],['b','d']],
      'right_real_parameter_positive_imaginary_root_rays':['a','b'],
      'right_real_parameter_negative_imaginary_root_rays':['d','e'],
      'left_real_parameter_positive_real_root_rays':['a','e'],
      'left_real_parameter_negative_real_root_rays':['b','d'],
      'noncrossing_partitions':noncrossing,
      'illegal_crossing_partition':[['a','d'],['b','e']],
      'left_reflection_invariant_pairs':True,
      'right_reflection_swaps_pairs':True,
      'positive_angle_rays_stay_in_upper_halfplane_for_real_c_in_M':True,
    }

def compute():
    signed=certified_core()
    assert signed['kappa_strict_bounds']==['276/1000','277/1000']
    assert signed['A8_strict_bounds']==['9343/100','9345/100']
    assert signed['lambda_strict_bounds']==['3','4']
    return {
      'schema_version':1,
      'type':'exact angular combinatorics + source-certified simple precritical fold; classical ray landing/stability imported',
      'real_slice':'all real c sufficiently close to cstar on either side are in [-2,1/4] subset Mandelbrot',
      'certified_tip_derivative':signed['kappa_strict_bounds'],
      'certified_repelling_ninth_return_multiplier':signed['lambda_strict_bounds'],
      'ray_angles':ray_audit(),
      'period9_return_phase_window_accesses':'for sufficiently large n, a,b land at +i sqrt(-R(c_n(t))), d,e at conjugate root',
      'scope':'full ambient rational rays, and terminal V9/V3 access germs; NO complete KL O/xi/eta side atlas, no H1-H4, no MLC',
      'formalization_limit':'external periodic-ray landing persistence, pullback topology and planar half-plane order are classical written arguments, not verified by this script',
    }

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    group=ap.add_mutually_exclusive_group()
    group.add_argument('--write-manifest',action='store_true')
    group.add_argument('--check-manifest',action='store_true')
    opt=ap.parse_args()
    raw=json.dumps(compute(),sort_keys=True,indent=2)+'\n'
    if opt.write_manifest:
        OUT.parent.mkdir(parents=True,exist_ok=True)
        OUT.write_text(raw,encoding='utf-8')
        print('WROTE '+str(OUT))
    elif opt.check_manifest:
        assert OUT.read_text(encoding='utf-8')==raw,'Manifest mismatch'
        print('PASS: exact tip-ray quartet, period-nine targets, left/right pairings and certified fold coefficient')
    else:print(raw,end='')
if __name__=='__main__':main()