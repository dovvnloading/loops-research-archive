#!/usr/bin/env python3
"""Finite exact checks for serial Levin rays at the real period-3/9 tip.

This verifies *angular arithmetic* and the merged source's finite landing
partitions. It does not prove Levin's analytic prime-end/straightening
theorem or the properness of curves; see companion mathematical proof.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'results' / 'tip_levin_composition_escape_20261108.json'
SOURCE = ROOT / 'results' / 'tip_actual_coarse_only_ray_pairing_20261107.json'
PARENT = ROOT / 'results' / 'tip_nested_full_ray_census_20261107.json'
DEN = 523264
SEAMS = ((41,43),(53,55),(137,139),(149,151))
FINE = (116736,116791,144841,144896,378368,378423,406473,406528)
COARSE_112 = (80,81,87,88,24,25,31,32)
FINE_4 = (0,1,1,2,2,3,3,0)
RETURN = (0,3,4,7,0,3,4,7)

def face(n: int) -> bool:
    x = n % DEN
    return any(lo*DEN < 192*x < hi*DEN for lo,hi in SEAMS)

def compute() -> dict:
    angles = sorted(t + 511*k for t in (228,283) for k in range(1024))
    assert len(angles)==len(set(angles))==2048
    first = [n for n in angles if face(n)]
    coarse = [n for n in first if face(8*n)]
    assert len(first)==80 and len(coarse)==32
    assert all(face(64*n) for n in coarse)
    assert len(set(FINE))==8 and set(FINE)<=set(coarse)
    lost = sorted(set(coarse)-set(FINE))
    assert len(lost)==24

    previous = json.loads(SOURCE.read_text(encoding='utf-8'))
    from_previous = [int(F(t)*DEN) for t,_ in previous[
        'Levin_cyclic_ranking']['sorted_ambient_internal_pairs']]
    assert from_previous == coarse
    groups = previous['complete_15_landing_points']
    assert len(groups)==15
    fine_groups=[g for g in groups if g['G_top_critical_Y3_face']]
    coarse_groups=[g for g in groups if not g['G_top_critical_Y3_face']]
    assert len(fine_groups)==3 and len(coarse_groups)==12
    assert sorted(n for g in fine_groups for n in g['ambient_523264_numerators']) == list(FINE)
    assert sorted(n for g in coarse_groups for n in g['ambient_523264_numerators']) == lost
    assert sorted(len(g['ambient_523264_numerators']) for g in fine_groups)==[2,2,4]
    assert all(len(g['ambient_523264_numerators'])==2 for g in coarse_groups)
    counts={}
    for g in coarse_groups:
        s=g['G_original_depth3_alpha_face_signature']
        counts[s]=counts.get(s,0)+1
    assert sorted(counts.values())==[2,2,4,4]

    parent=json.loads(PARENT.read_text(encoding='utf-8'))
    assert sorted(int(F(a)*DEN) for a in parent[
        'precritical_fiber']['stage_nine_complete_angles']) == list(FINE)
    q={COARSE_112[i]:FINE_4[i] for i in range(8)}
    assert len(q)==8
    for i in range(8):
        j=RETURN[i]
        assert (512*FINE[i])%DEN == FINE[j]
        assert (8*COARSE_112[i])%112 == COARSE_112[j]
        assert (2*FINE_4[i])%4 == FINE_4[j]
        assert q[COARSE_112[i]]==FINE_4[i]
        assert q[(8*COARSE_112[i])%112]==(2*q[COARSE_112[i]])%4
    assert sorted(FINE_4.count(k) for k in range(4)) == [2,2,2,2]
    assert len(coarse_groups)+len(set(FINE_4))==16
    assert all(len(g['ambient_523264_numerators'])==2 for g in coarse_groups)

    return {
      'schema_version':1,
      'stratified_target_objects':16,
      'fine_boundary_prime_end_objects':4,
      'coarse_only_interior_point_objects':12,
      'each_stratified_target_fiber_size':2,
      'full_candidate_count':2048,
      'first_original_alpha_sector_count':80,
      'second_original_alpha_sector_count':32,
      'coarse32_numerators':coarse,
      'fine8_numerators':list(FINE),
      'escaped24_numerators':lost,
      'original_G_face_class_counts':dict(sorted(counts.items())),
      'selected_coarse_internal_numerators_over112':list(COARSE_112),
      'selected_fine_internal_numerators_over4':list(FINE_4),
      'selected_f9_return_target_indices':list(RETURN),
      'source_limit':'Levin analytic composition/physical properness are written proofs, NOT formalized by this checker',
      'global_circle_warning':'semiconjugacy Q o sigma8=sigma2 o Q holds only on eligible domain'
    }

def main()->None:
    p=argparse.ArgumentParser(description=__doc__)
    g=p.add_mutually_exclusive_group()
    g.add_argument('--check-manifest',action='store_true')
    g.add_argument('--write-manifest',action='store_true')
    a=p.parse_args()
    payload=compute()
    if a.write_manifest:
        DATA.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n',encoding='utf-8')
        print('WROTE', DATA)
    elif a.check_manifest:
        expected=json.loads(DATA.read_text(encoding='utf-8'))
        assert expected==payload,'Exact finite manifest mismatch'
        print('PASS: 2048 -> 80 -> 32; 8 fine, 24 escaped; 12 original face groups; eight exact Levin return clocks')
    else:
        print(json.dumps(payload,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
