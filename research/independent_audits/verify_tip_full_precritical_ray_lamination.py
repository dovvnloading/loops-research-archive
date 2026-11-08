#!/usr/bin/env python3
"""Full 1023-class critical-slit ray census for the actual twice-tuned real tip.

Finite arithmetic uses exact Fractions. Classical inputs (not Python proofs):
actual Zakeri critical-value ray landing, completeness of the repelling
nine-cycle ray pair, source analytic slit inverse branches, physical ray
landing and periodic-ray stability. See the companion paper for hypotheses.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

RESULT = Path(__file__).resolve().parents[2] / 'results' / 'tip_full_precritical_ray_lamination_20261107.json'
COARSE = Path(__file__).resolve().parents[2] / 'results' / 'tip_actual_coarse_only_ray_pairing_20261107.json'
TAU = Q(116791,261632)
KAPPA = TAU/2
HALF = Q(1,2)
TARGET = (Q(228,511), Q(283,511))
DEN = 1024*511
CRITICAL = tuple(sorted((Q(116791,DEN),Q(144841,DEN),Q(378423,DEN),Q(406473,DEN))))


def lift_angle(angle:Q, sheet:int)->Q:
    """L_i: the unique inverse ray inside the source's actual slit half-circle."""
    assert sheet in (0,1)
    options=(angle/2,(angle+1)/2)
    def sector(x):
        assert x != KAPPA and x != KAPPA+HALF, 'critical-ray slit endpoint requires special handling'
        return 0 if KAPPA<x<KAPPA+HALF else 1
    choices=[x for x in options if sector(x)==sheet]
    assert len(choices)==1, (angle,sheet,options)
    return choices[0]


def lift_group(group:tuple[Q,...])->list[tuple[tuple[Q,...],str]]:
    critical_value_pair=tuple(sorted((TAU,1-TAU)))
    if group==critical_value_pair:
        # The TRUE critical-value preimage has one local degree-two point,
        # so four ray lifts co-land at 0; never create two fictitious roots.
        return [(tuple(sorted({q for angle in group for q in (angle/2,(angle+1)/2)})), 'C')]
    assert len(group)==2,group
    return [(tuple(sorted(lift_angle(a,i) for a in group)),str(i)) for i in (0,1)]


def make_levels():
    first=tuple(sorted(TARGET))
    frontier={first:''}
    rows=[]
    for depth in range(0,11):
        groups=sorted(frontier, key=lambda group:group[0])
        flat=[a for g in groups for a in g]
        assert len(flat)==len(set(flat))
        assert all(len(g) in (2,4) for g in groups)
        counts=Counter(map(len,groups))
        assert len(flat)==2**(depth+1)
        assert counts.get(4,0)==(1 if depth==10 else 0)
        assert len(groups)==(2**depth if depth<=9 else 1023)
        assert all((2**depth *a)%1 in TARGET for a in flat)
        row={'depth':depth,'actual_inverse_ray_count':len(flat),
             'distinct_landing_classes':len(groups),'two_ray_classes':counts.get(2,0),
             'four_ray_classes':counts.get(4,0)}
        rows.append(row)
        if depth==10:break
        next_group={}
        for group, address in frontier.items():
            for child,label in lift_group(group):
                assert child not in next_group
                next_group[child]=address+label
        frontier=next_group
    return frontier,rows


def numerators(group:tuple[Q,...])->list[int]:
    nums=[int(a*DEN) for a in group]
    assert all(a*DEN==n for a,n in zip(group,nums))
    assert nums==sorted(nums)
    return nums


def chord_crosses(p:list[int],q:list[int])->bool:
    a,b=p;c,d=q
    return (a<c<b) != (a<d<b)


def check_non_crossing(groups)->int:
    """O(1M) exact integer tests; no float geometry or sampled chords."""
    pairs=[numerators(g) for g in groups if len(g)==2]
    count=0
    for k,p in enumerate(pairs):
        for q in pairs[k+1:]:
            count+=1
            assert not chord_crosses(p,q),('crossing actual simple-point rays',p,q)
    return count


def verify_15_coarse(groups)->dict:
    """Independent inverse-slit pairing vs prior actual G sector/Levin sieve."""
    source=json.loads(COARSE.read_text())
    known={frozenset(rec['ambient_523264_numerators']) for rec in source['complete_15_landing_points']}
    present={frozenset(numerators(g)) for g in groups}
    assert len(known)==15 and known.issubset(present)
    fine={frozenset((116736,406528)),frozenset((144896,378368)),frozenset((116791,144841,378423,406473))}
    assert fine.issubset(known)
    assert sum(len(group)==2 for group in known)==14
    assert sum(len(group)==4 for group in known)==1
    return {'all_15_true_K3_landing_classes_match_independent_G_sieve':True,
            'K3_distinct_points_at_tip':15,
            'K9_distinct_points_at_tip':3,
            'coarse_only_distinct_points':12,
            'coarse_only_rays':24}


def build():
    groups,rows=make_levels()
    nums={g:numerators(g) for g in groups}
    assert len(groups)==1023
    quadruplets=[g for g in groups if len(g)==4]
    assert quadruplets==[CRITICAL]
    seen=[n for v in nums.values() for n in v]
    assert len(seen)==2048==len(set(seen))
    assert sorted(seen)==sorted([int((t+k)/1024*DEN) for t in TARGET for k in range(1024)])
    assert all(len(g)==2 or g==CRITICAL for g in groups)
    # Every regular group carries one source angle per periodic target.
    assert all(sorted({(2**10*a)%1 for a in group})==list(TARGET) for group in groups if len(group)==2)
    assert Counter((2**10*a)%1 for a in CRITICAL)==Counter({TARGET[0]:2,TARGET[1]:2})
    crossing_count=check_non_crossing(groups)
    old=verify_15_coarse(groups)
    left=(tuple(sorted((CRITICAL[0],CRITICAL[3]))),tuple(sorted((CRITICAL[1],CRITICAL[2]))))
    right=(tuple(sorted((CRITICAL[0],CRITICAL[1]))),tuple(sorted((CRITICAL[2],CRITICAL[3]))))
    assert {x for pair in left for x in pair}==set(CRITICAL)
    assert {x for pair in right for x in pair}==set(CRITICAL)
    ordinary=sorted(((nums[g],groups[g]) for g in groups if len(g)==2),key=lambda x:x[0])
    complete=sorted(((nums[g],groups[g]) for g in groups),key=lambda x:x[0])
    # Rigid byte checksum for the COMPLETE finite pairing, besides full JSON.
    canonical=json.dumps([x[0] for x in complete],separators=(',',':'))
    digest=hashlib.sha256(canonical.encode('ascii')).hexdigest()
    sample=complete[:8]+complete[-8:]
    return {
        'schema_version':1,
        'scope':'actual connected real Misiurewicz-tip dynamic rays, critical-slit inverse branches, not generic complex KL localization sheets',
        'source_critical_value_lower_ray':str(TAU),
        'source_critical_value_upper_ray':str(1-TAU),
        'source_inverse_branch_cut_angles':[str(KAPPA),str(KAPPA+HALF)],
        'source_periodic_target_rays':[str(x) for x in TARGET],
        'common_denominator':DEN,
        'complete_depth_wise_counts':rows,
        'complete_1023_landing_class_numerators_and_actual_inverse_branch_words':[
          [n,word] for n,word in complete],
        'strict_simple_chord_pair_non_crossing_tests':crossing_count,
        'critical_only_quadruplet':[int(a*DEN) for a in CRITICAL],
        'critical_inverse_word':groups[CRITICAL],
        'all_2048_ambient_inverse_rays_exactly_once':True,
        'complete_fiber_pairing_sha256':digest,
        'left_of_tip_critical_ray_splitting':[[int(a*DEN) for a in pair] for pair in left],
        'right_of_tip_critical_ray_splitting':[[int(a*DEN) for a in pair] for pair in right],
        'all_other_1022_pairs_are_unchanged_under_nearby_REAL_parameter_variation':True,
        'five_plus_five_representative_end_groups':[
            {'angles':p,'address':q} for p,q in sample],
        'independent_nested_3_9_cross_check':old,
        'trust_boundary':'All finite rational checks are exact. Actual ray landing, slit geometry, 1022-root persistence and critical real bifurcation rely on cited prior written/classical theorems. H1-H4 UPTCR MLC open.'
    }


def main():
    parser=argparse.ArgumentParser()
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--write-manifest',action='store_true')
    mode.add_argument('--check-manifest',action='store_true')
    args=parser.parse_args()
    raw=json.dumps(build(),sort_keys=True,separators=(',',':'))+'\n'
    if args.write_manifest:
        RESULT.parent.mkdir(parents=True,exist_ok=True)
        RESULT.write_text(raw)
        print('WROTE',RESULT)
    elif args.check_manifest:
        assert RESULT.read_text()==raw,'Deterministic full pairing manifest drift'
        print('PASS: 2048 angles, 1023 full actual landing classes, unique critical quartet, 521731 noncrossing chord tests and all 15 K3 classes')
    else:print(raw,end='')
if __name__=='__main__':main()
