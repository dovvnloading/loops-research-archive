#!/usr/bin/env python3
"""Exact finite certificates for complete period-3/9 precritical ray fibers.

Imports the already merged, exact 2^-256 interval arithmetic at the same
Misiurewicz tip. The analytic input (polynomial-like properness, landing,
Levin monotonicity, and Milnor primitive-portrait bound) is proved/imported
in the companion mathematical note, not by this finite program.

python research/independent_audits/verify_tip_nested_full_ray_census.py --check-manifest
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from verify_tip_ramified_precritical_pair import (certified_core, D, orbit,
                                                    K, PREC, TIP_BITS)

OUT=Path(__file__).resolve().parents[2]/'results'/'tip_nested_full_ray_census_20261107.json'
ZERO=Q(0); HALF=Q(1,2); ONE=Q(1)
BASE_A=Q(283,511); BASE_B=Q(228,511)
A=Q(116791,523264); B=Q(144841,523264)
DANGLE=Q(378423,523264); E=Q(406473,523264)
P_L=Q(114,511); P_R=Q(397,511)
Q_L=Q(283,1022); Q_R=Q(739,1022)

def mod1(x:Q)->Q:return x % 1

def tip_distinct_critical_arrival():
    core=certified_core()
    bracket=D(K*(1<<(PREC-TIP_BITS)),(K+1)*(1<<(PREC-TIP_BITS)))
    orbit_points,_=orbit(bracket)
    target=orbit_points[10]
    gaps=[]
    for j in range(10):
        z=orbit_points[j]
        if z.hi<target.lo:
            dist=Q(target.lo-z.hi,1<<PREC)
        else:
            assert target.hi<z.lo,('overlapping interval',j)
            dist=Q(z.lo-target.hi,1<<PREC)
        assert dist>Q(1,2048),(j,float(dist))
        gaps.append(dist)
    assert core['Gprime_bounds']==['-71','-70']
    assert core['kappa_strict_bounds']==['276/1000','277/1000']
    assert core['lambda_strict_bounds']==['3','4']
    return {'all_10_earlier_critical_arrivals_avoided':True,
            'smallest_critical_arrival_gap_gt':'1/2048',
            'tightest_earlier_time':min(range(10),key=lambda i:gaps[i]),
            'computed_minimum_gap_approx':round(float(min(gaps)),15),
            'analytic_local_branch_derivative':'-kappa, 0.276<kappa<0.277'}

def full_inverse_angle_census():
    assert mod1(512*BASE_A)==BASE_A
    assert mod1(512*BASE_B)==BASE_B
    assert all(mod1(2**j*t)!=t for t in (BASE_A,BASE_B) for j in range(1,9))
    full_angles=[]
    for t in (BASE_A,BASE_B):
        for k in range(1024):
            v=(t+k)/1024
            assert 0<=v<1 and mod1(1024*v)==t
            full_angles.append(v)
    assert len(full_angles)==2048==len(set(full_angles))
    assert full_angles==sorted(full_angles[:1024])+sorted(full_angles[1024:])
    orbit_pairs=[]
    for j in range(9):
        pair=sorted((mod1(2**j*BASE_A),mod1(2**j*BASE_B)))
        orbit_pairs.append([str(x) for x in pair])
    assert len({x for pair in orbit_pairs for x in pair})==18
    p={P_L,P_R}
    q={Q_L,Q_R}
    s={A,B,DANGLE,E}
    assert len(p|q|s)==8
    assert set(full_angles).issuperset(p|q|s)
    assert {mod1(512*t) for t in p}==p  # periodic p for f^9
    assert {mod1(512*t) for t in q}==p  # F9(-p)=p
    assert {mod1(512*t) for t in s}==q  # F9(s)=-p
    assert mod1(512*A)==mod1(512*DANGLE)==Q_L
    assert mod1(512*B)==mod1(512*E)==Q_R
    assert {mod1(1024*t) for t in p|q|s}=={BASE_A,BASE_B}
    target_counts={str(z):sum(mod1(1024*t)==z for t in p|q|s) for z in (BASE_A,BASE_B)}
    assert all(n==4 for n in target_counts.values())
    return {'ambient_degree_10':1024,
            'full_inverse_angle_count':len(full_angles),
            'two_repelling_fixed_angles':[str(BASE_B),str(BASE_A)],
            'repelling_orbit_periods':9,
            'complete_nine_cycle_pairs':orbit_pairs,
            'nine_cycle_total_distinct_ray_angles':18,
            'stage_fiber_degree_counts':{'whole_fiber':1024,'K3':16,'K9':4},
            'at_tip_distinct_point_counts':{'whole_fiber':1023,'K3':15,'K9':3},
            'near_tip_distinct_point_counts':{'whole_fiber':1024,'K3':16,'K9':4},
            'near_tip_angle_incidence_counts':{'whole_fiber':2048,'K3':32,'K9':8},
            'tip_angle_incidence_counts':{'whole_fiber':2048,'K3':32,'K9':8},
            'stage_nine_complete_angles':sorted(str(x) for x in p|q|s),
            'periodic_p_rays':sorted(str(x) for x in p),
            'preperiodic_minus_p_rays':sorted(str(x) for x in q),
            'ramified_s_rays':sorted(str(x) for x in s),
            'stage_nine_rays_per_f10_periodic_target':target_counts,
            'stage_three_extra_preimages':12}

def candidates(target:Q,l:Q,r:Q,exponent:int=8):
    return [(target+k)/exponent for k in range(16) if l<=(target+k)/exponent<=r]

def levin_eight_ray_ladder():
    order=[('pL',P_L),('a',A),('b',B),('qL',Q_L),
           ('qR',Q_R),('d',DANGLE),('e',E),('pR',P_R)]
    assert [t for _,t in order]==sorted(t for _,t in order)
    # The period-3 values on the two actual rays at p=P18 are a
    # separately source-licensed, exact six-ray monotone enumeration.
    outer_pL=Q(5,7);outer_pR=Q(2,7)
    # By antipodality, these are distinct preimages of the same
    # first g3-image ray and cannot share an internal angle at p and -p.
    outer_qL=Q(11,14);outer_qR=Q(3,14)
    # The lifted degree-one monotone outer-map interval lies between
    # pL and qL for (a,b), and between qR and pR for (d,e).
    interval1=(outer_pL,outer_qL)
    interval2=(outer_qR+1,outer_pR+1)
    lookup={
        'a':(outer_qL,*interval1),
        'b':(outer_qR,*interval1),
        'd':(outer_qL,*interval2),
        'e':(outer_qR,*interval2)
    }
    outer={}
    for key,(target,l,r) in lookup.items():
        opts=candidates(target,l,r)
        assert len(opts)==1,(key,opts)
        outer[key]=mod1(opts[0])
        assert mod1(8*outer[key])==target
    assert outer=={'a':Q(81,112),'b':Q(87,112),'d':Q(25,112),'e':Q(31,112)}
    outer_order=[outer_pL,outer['a'],outer['b'],outer_qL,
                 outer_qR+1,outer['d']+1,outer['e']+1,outer_pR+1]
    assert all(a<b for a,b in zip(outer_order,outer_order[1:])),outer_order
    # Fine = period-9: p's two rays both map to 0;
    # -p's two distinct rays must map to 1/2, and the four 0 rays map
    # to one of the two preimages 1/4, 3/4, fixed by circular order.
    inner={'pL':ZERO,'a':Q(1,4),'b':Q(1,4),'qL':HALF,
           'qR':HALF,'d':Q(3,4),'e':Q(3,4),'pR':ZERO}
    inner_lift=[inner[k]+(1 if k=='pR' else 0) for k,_ in order]
    assert all(x<=y for x,y in zip(inner_lift,inner_lift[1:])),inner_lift
    outer_complete={'pL':outer_pL,'a':outer['a'],'b':outer['b'],
                    'qL':outer_qL,'qR':outer_qR,'d':outer['d'],
                    'e':outer['e'],'pR':outer_pR}
    assert len(set(outer_complete.values()))==8
    assert len(set(inner.values()))==4
    # The internal action of g3^3 is multiplication by 8 and of g9 by 2.
    ray_g9={'a':'qL','b':'qR','d':'qL','e':'qR'}
    for src,tgt in ray_g9.items():
        assert mod1(8*outer_complete[src])==outer_complete[tgt]
        assert mod1(2*inner[src])==inner[tgt]
    for src,tgt in [('qL','pR'),('qR','pL')]:
        # g9 ray image of qL=283/1022 is pR=397/511;
        # g9 ray image of qR=739/1022 is pL=114/511.
        assert mod1(512*dict(order)[src])==dict(order)[tgt]
        assert mod1(8*outer_complete[src])==outer_complete[tgt]
        assert mod1(2*inner[src])==inner[tgt]
    return {'input_cyclic_order':[(key,str(angle)) for key,angle in order],
            'Pi3_outer_internal':{k:str(outer_complete[k]) for k,_ in order},
            'Pi9_inner_internal':{k:str(inner[k]) for k,_ in order},
            'outer_eight_distinct_angles':8,
            'inner_four_angle_values':4,
            'outer_critical_quartet':{k:str(outer[k]) for k in ('a','b','d','e')},
            'inner_critical_quartet':{k:str(inner[k]) for k in ('a','b','d','e')},
            'monotone_strict_outer':True,
            'monotone_weak_inner':True,
            'one_step_outer_semiconjugacy_9_to_3':True,
            'single_stage_ray_fiber_sizes':{'K3':32,'K9':8},
            'no_global_cross_scale_naturality_claim':True}

def build():
    return {'schema_version':1,
            'scope':'FULL 10-step ray census at the actual tip plus exact two-scale selected Levin angle ladder; not full KL sheet functor',
            'first_critical_arrival':tip_distinct_critical_arrival(),
            'precritical_fiber':full_inverse_angle_census(),
            'actual_Levin_3_to_9_ladder':levin_eight_ray_ladder(),
            'classical_inputs':['Milnor primitive orbit-portrait valence <=2','positive-Green Böttcher inverse lifting','actual proper degree-2 period-3 and period-9 restrictions','Levin monotone degree-one semiconjugacies','already certified period-3 internal 5/7 and 2/7 values'],
            'status':'integer/rational identities exact; analytic continuations and connected little-set at tip source-imported; H1-H4 UPTCR MLC open'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    mode=ap.add_mutually_exclusive_group()
    mode.add_argument('--write-manifest',action='store_true')
    mode.add_argument('--check-manifest',action='store_true')
    args=ap.parse_args()
    text=json.dumps(build(),indent=2,sort_keys=True)+'\n'
    if args.write_manifest:
        OUT.parent.mkdir(parents=True,exist_ok=True)
        OUT.write_text(text)
        print('WROTE',OUT)
    elif args.check_manifest:
        assert OUT.read_text()==text,'manifest drift'
        print('PASS: exact first arrival, degree 1024/16/4, all 2048 angles, and unique 8-ray two-scale Levin ladder')
    else:print(text,end='')
if __name__=='__main__':main()
