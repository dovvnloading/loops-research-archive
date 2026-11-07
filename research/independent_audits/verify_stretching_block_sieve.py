#!/usr/bin/env python3
"""Exact finite checks for the SOURCE-DEFINED stretching-block candidate sieve.

The source-native dynamical assertion is a mathematical consequence of the
KKL Proposition 6.8 corridor and the source's limb relations; these integer
regressions check ONLY marked-circle combinatorics, NOT KKL analytic geometry.

    python research/independent_audits/verify_stretching_block_sieve.py --check-manifest
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

MANIFEST = Path(__file__).resolve().parents[2] / 'results' / 'stretching_block_sieve_20261106.json'


def atoms(start: int, length: int, m: int) -> frozenset[int]:
    assert 0 <= start < m and 1 <= length < m
    return frozenset((start + j) % m for j in range(length))


def audit(max_m: int = 40) -> dict:
    checked = 0
    touching = 0
    inside = 0
    straddling = 0
    disjoint = 0
    scan_states = 0
    contact_s1 = contact_s2_inside = contact_s2_straddle = 0
    # Enumerates full cyclic placements, including a two-atom block wrapping 0.
    for m in range(3, max_m+1):
        for r in range(1, m):
            limb = frozenset(range(r))
            for k in range(1, m-r+1):
                critical = [(a, atoms(a, k, m)) for a in range(m)
                            if not atoms(a, k, m).isdisjoint(limb)]
                assert len(critical) == r + k - 1
                scan_states += len(critical)
                for t in (1, 2):
                    for b in range(m):
                        B = atoms(b, t, m)
                        touching_limb = bool(B & limb)
                        in_limb = B <= limb
                        surviving = sum(not (limb <= J) and not (B <= J)
                                        for _, J in critical)
                        source_forbidden = sum(B <= J for _, J in critical)
                        if touching_limb:
                            # For a length-k interval containing B, touching L is automatic.
                            assert source_forbidden == max(0, k-t+1), (
                                'stretch coverage', m, r, k, t, b, source_forbidden)
                            if t == 1:
                                expected = r - 1
                                contact_s1 += 1
                            elif in_limb:
                                expected = r
                                contact_s2_inside += 1
                            else:
                                # Two-atom B overlaps L in exactly one atom and
                                # crosses a boundary cut of L.
                                expected = r - int(k >= r)
                                contact_s2_straddle += 1
                            assert surviving == expected, (
                                'root-free gate count', m,r,k,t,b,surviving,expected)
                            touching += 1
                            if in_limb: inside += 1
                            else: straddling += 1
                        else:
                            disjoint += 1
                        checked += 1
    # NEGATIVE: a remote source block does not give any local critical pruning.
    m,r,k,t,b = 10,3,1,1,6
    L = frozenset(range(r)); B = atoms(b,t,m)
    remote_survivors = sum(not (L <= atoms(a,k,m)) and not (B <= atoms(a,k,m))
                           for a in range(m) if atoms(a,k,m)&L)
    assert remote_survivors == r != r-1

    # NEGATIVE: a closed crest containing the shared CUT may fail to contain the
    # entire two-atom stretching block; it must not be called root-exposed by
    # Proposition 6.8 without a separately proved singleton-access statement.
    m=10; J=atoms(1,1,m); B=atoms(1,2,m); selected_shared_cut=2
    crest_cuts=frozenset((1,2))
    assert selected_shared_cut in crest_cuts and not B <= J

    return {
        'verified_marking_sizes': '3 <= M <= %d' % max_m,
        'regime': '1 <= r < M; 1 <= k <= M-r; 1 <= t <= 2',
        'exact_critical_meeting_states': 'r+k-1',
        'tested_placements': checked,
        'critical_state_enumerations': scan_states,
        'stretch_block_touching_cases': touching,
        'stretch_block_inside_cases': inside,
        'stretch_block_straddling_cases': straddling,
        'stretch_block_disjoint_cases': disjoint,
        'touching_one_atom_cases': contact_s1,
        'touching_two_atom_inside_cases': contact_s2_inside,
        'touching_two_atom_boundary_cases': contact_s2_straddle,
        'survivor_one_atom': 'r-1',
        'survivor_two_atom_inside': 'r',
        'survivor_two_atom_crossing_boundary': 'r - 1_{k>=r}',
        'negative_remote_block': {'M':10,'r':3,'k':1,'block_start':6,'survivors':remote_survivors},
        'negative_closed_cut_only': 'crest contains shared marked cut but not full 2-atom stretch block',
    }


def arithmetic(max_b: int = 1000) -> dict:
    for b in range(1,max_b+1):
        q=24*b; r=6*b; K=12*b-1
        assert q-2*b-1 >= 12*b  # Source long corridor excludes all short crests.
        assert K <= q-r  # All critical-meeting start cuts uniquely lift.
        assert r <= K   # For boundary-straddling two-block total cap formula.
        assert (r-1)*K <= r*K
        assert (r-1)*12*b <= r*K
    return {
        'max_b_checked': max_b,
        'large_rotation': 'q >= 24*b; M >= q; r <= 6*b; 1 <= k < 12*b',
        'long_corridor_limb_count': 'q-2*b-1 >= 12*b',
        'candidate_cap_t1': '(r-1)*(12*b-1)',
        'candidate_cap_t2_inside': 'r*(12*b-1)',
        'candidate_cap_t2_straddling': '(r-1)*12*b',
        'placement_free_touching_cap': 'r*(12*b-1)',
        'native_bridge': 'requires actual I_str to touch critical limb, typed closed crest inclusion, and proper dynamics; not proved by cyclic test',
    }


def data() -> dict:
    return {
        'schema_version':1,
        'method':'Exact cyclic marked intervals; not holomorphic KKL proof',
        'source':'KKL arXiv:2606.27272v1 Proposition 6.8 stretching multi-interval; source dynamics used only in written argument',
        'sieve':audit(),
        'high_rotation':arithmetic(),
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    g=p.add_mutually_exclusive_group()
    g.add_argument('--check-manifest',action='store_true')
    g.add_argument('--write-manifest',action='store_true')
    args=p.parse_args()
    result=json.dumps(data(),sort_keys=True,indent=2)+'\n'
    if args.write_manifest:
        MANIFEST.parent.mkdir(parents=True,exist_ok=True)
        MANIFEST.write_text(result,encoding='utf-8')
        print('Wrote '+str(MANIFEST))
    elif args.check_manifest:
        assert MANIFEST.read_text(encoding='utf-8') == result
        print('PASS: all exact stretch-block counts and manifest')
    else:
        print(result,end='')


if __name__ == '__main__':
    main()
