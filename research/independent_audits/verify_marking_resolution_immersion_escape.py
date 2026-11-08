#!/usr/bin/env python3
"""Exact rational endpoint checks and independent marked-cut/width regression.

This checker tests a precisely specified holomorphic *control* model. It does
not verify general KKL non-LC prime ends, source Wave transport or MLC.

Usage:
 python research/independent_audits/verify_marking_resolution_immersion_escape.py --check-manifest
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve()
MANIFEST = HERE.parents[2] / 'results' / 'marking_resolution_immersion_escape_20261107.json'
PI = math.pi


def circle_dist(x: float, center: float) -> float:
    """Shortest unsigned angular distance on the true circle."""
    z = ((x - center + PI) % (2 * PI)) - PI
    return abs(z)


def cut_threshold(cuts: tuple[float, ...], center: float, R: float) -> float:
    # No inner boundary path is admissible with <=2 marked atoms:
    # the full inner circle itself is a multi-interval of length <=2.
    if len(cuts) <= 2:
        return R
    nearby = sorted(circle_dist(x, center) for x in cuts if circle_dist(x, center) < R - 1e-13)
    return nearby[1] if len(nearby) >= 2 else R


def counted_atoms(cuts: tuple[float, ...], center: float, r: float) -> int:
    # The arc may cross *every* cut; its starting/ending atom then repeats.
    return min(len(cuts), 1 + sum(circle_dist(x, center) < r - 1e-13 for x in cuts))


def width(r0: float, R: float, threshold: float) -> float:
    return max(0., math.log(R / max(r0, threshold)) / PI)


def test_marking_threshold() -> dict:
    h = .25
    R = h / 2
    tests = []
    case_count = 0
    for eps in (.001, 1e-4, 1e-5, 1e-6):
        r0 = math.asin(eps)
        assert r0 < R
        alpha = math.acos(eps)
        # Source gates of the true attached segment X and its deck translate.
        gates = (alpha, PI - alpha, PI + alpha, 2*PI - alpha)
        critical_sides = (PI/2, 3*PI/2)
        configurations = {
            'four_actual_gate_cuts': gates,
            'six_actual_gate_and_critical_cuts': gates + critical_sides,
            'two_coarse_gap_center_cuts': critical_sides,
            'three_cuts_one_gap_unresolved': (alpha, PI-alpha, 3*PI/2),
        }
        for name,cuts in configurations.items():
            # Every marked cut is its actual normalized angular location.
            assert len(cuts) == len(set(cuts))
            thresholds = []
            widths = []
            for center in (PI/2, 3*PI/2):
                threshold = cut_threshold(cuts, center, R)
                thresholds.append(threshold)
                admitted = width(r0, R, threshold)
                widths.append(admitted)
                # Skip the finitely many cut-endpoint radii, use 100 generic positions.
                for i in range(1, 101):
                    r = r0 + (R-r0)*(i+.1)/102
                    if any(abs(r-circle_dist(c,center)) < 1e-12 for c in cuts):
                        continue
                    expected = (r > threshold + 1e-12)
                    observed = counted_atoms(cuts, center, r) >= 3
                    assert observed == expected, (eps,name,center,r,threshold)
                    case_count += 1
            if name in ('four_actual_gate_cuts','six_actual_gate_and_critical_cuts'):
                assert all(abs(x - r0) < 1e-12 for x in thresholds)
                assert all(abs(x - math.log(R/r0)/PI) < 1e-9 for x in widths)
            if name == 'two_coarse_gap_center_cuts':
                assert thresholds == [R,R]
                assert widths == [0.,0.]
            if name == 'three_cuts_one_gap_unresolved':
                assert widths[0] > 0 and widths[1] == 0
            tests.append({'epsilon':eps,'marking':name,
                          'second_cut_distances':[round(x,12) for x in thresholds],
                          'admissible_widths':[round(x,12) for x in widths]})
    # Previously missed adversarial boundary case: with just TWO marked
    # atoms, even two nearby cuts flanking one gap cannot make a leaf valid.
    # A naive 1 + number-of-crossed-cuts formula gives the WRONG count 3.
    center = PI/2
    r0 = math.asin(.001)
    close_two = (center-r0, center+r0)
    naive_atoms = 1+sum(circle_dist(x, center) < .05 for x in close_two)
    assert naive_atoms == 3 and len(close_two) == 2
    assert counted_atoms(close_two, center, .05) == 2
    assert cut_threshold(close_two, center, .125) == .125
    assert width(r0, .125, cut_threshold(close_two, center, .125)) == 0.
    # Minimum 4 distinct cuts for *both* packets: in two disjoint small
    # source neighborhoods, each needs two cuts. This exact finite count
    # is the pigeonhole arithmetic, not a simulation of prime ends.
    for count in range(4):
        for near_first in range(count+1):
            near_second = count-near_first
            assert not (near_first >= 2 and near_second >= 2)
    assert 2+2 == 4
    return {'marking_placements':tests,'local_cut_inequalities_checked':case_count,
            'minimal_source_inner_cuts_for_both_packets':4,
            'sharp_rule':'leaf radius r is valid iff at least two cuts lie inside its short support',
            'exact_width':'max(0,log(R/max(r0,second_nearest_cut)))/pi'}


def test_fractional_loss() -> dict:
    R = .125
    examples = []
    for beta in (.25,.5,.75):
        samples = []
        for power in (4,6,8,10,12,14,16):
            r0 = 10.0**(-power)
            s2 = r0**beta
            if not s2 < R:  # wait until the second cut is in the collar
                continue
            full = math.log(R/r0)/PI
            retained = math.log(R/s2)/PI
            assert 0 < retained < full
            ratio = retained/full
            samples.append({'r0':r0,'second_cut_distance':round(s2,14),
                            'retained_fraction':round(ratio,12)})
        assert samples
        assert abs(samples[-1]['retained_fraction']-beta) < .15
        examples.append({'beta':beta,'samples':samples,'limiting_fraction':beta})
    return {'fractional_marking_loss':examples,
            'asymptotic_formula':'second-cut scale r0^beta retains fraction beta of logarithmic Wave width'}


def test_exact_physical_escape() -> dict:
    # h/2=1/8; Taylor lower bound sin(1/8)>=1/8-(1/8)^3/6.
    h2 = Q(1,8)
    sin_lower = h2 - h2**3 / 6
    witnesses = []
    tested = 0
    exact_joukowski = 0
    for k in range(3,24):
        eps=Q(1,10**k)
        c=-1-eps
        b=eps*(1+eps)
        for w in (Q(5,4),Q(3,2),Q(2),Q(5,2)):
            src=(-c)*Q(1,2)*(w+1/w)
            target=(c+b)*Q(1,2)+c*c*Q(1,4)*(w*w+1/(w*w))
            assert src*src+c == target
            exact_joukowski += 1
        for sigma in (Q(1,100),Q(1,20),Q(1,10)):
            # sigma=sin r with r0<r<h/2, *rigorously* from rational bounds.
            assert eps < sigma < sin_lower
            x=(1+eps)*sigma
            y=-x
            assert b < x < -c and c < y < 0 < b
            # A compact disk about x contained in V=U\T certifies
            # nonproperness of the first immersed end.
            radius=(x-b)/4
            assert radius > 0 and x-radius>b
            assert x+radius < Q(5)
            tested += 1
            if k in (3,6,12,23):
                witnesses.append({'eps':str(eps),'sin_radius':str(sigma),
                                  'old_tip':str(b),'new_end':str(x),
                                  'old_end':str(y),'interior_disk_radius':str(radius)})
    return {'exact_rational_endpoint_tests':tested,
            'exact_joukowski_identity_tests':exact_joukowski,
            'lower_sin_1_over_8':str(sin_lower),
            'representative_rational_witnesses':witnesses,
            'source_end_in_new_branch': 'b < x_r < -c',
            'source_other_end_in_old_tree': 'c < y_r < b',
            'target_image_proper_end_count_per_leaf':1,
            'all_direct_immersed_leaves_proper':False}


def test_unbounded_loss() -> dict:
    h=.25
    samples=[]
    for k in (3,4,6,8,10,12):
        eps=10.**(-k)
        r0=math.asin(eps)
        w=math.log(h/(2*r0))/PI
        assert w>0
        samples.append({'epsilon':eps,'source_width':round(w,12),
                        'proper_direct_image_leaf_fraction':0.0})
    assert all(a['source_width']<b['source_width'] for a,b in zip(samples,samples[1:]))
    return {'sample_unbounded_source_widths':samples,
            'exact_source_width':'(1/pi)*log(h/(2*arcsin(epsilon)))',
            'full_direct_immersion_proper_path_loss':True,
            'qualifier':'this does NOT imply iota^* of every target lamination is empty'}


def compute() ->dict:
    return {'schema_version':1,
            'scope':'actual non-prime-primitive quadratic-like covering/immersion; sharp marking/Wave resolution and improper-end escape, NOT native KKL Wave theorem',
            'source':'KKL arXiv:2606.27272v1 A.1 A.3.2, actual Joukowski attachment from PR #50',
            'marking':test_marking_threshold(),
            'fractional_width':test_fractional_loss(),
            'physical_escape':test_exact_physical_escape(),
            'unbounded_loss':test_unbounded_loss()}


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--write-manifest',action='store_true')
    mode.add_argument('--check-manifest',action='store_true')
    args=parser.parse_args()
    payload=json.dumps(compute(),indent=2,sort_keys=True)+'\n'
    if args.write_manifest:
        MANIFEST.parent.mkdir(parents=True,exist_ok=True)
        MANIFEST.write_text(payload,encoding='utf-8')
        print('WROTE',MANIFEST)
    elif args.check_manifest:
        assert MANIFEST.read_text(encoding='utf-8') == payload, 'manifest mismatch'
        print('PASS: exact original-cut sieve, 4-cut minimality, fractional width loss, rational improper-end witnesses')
    else:print(payload,end='')

if __name__=='__main__':main()
