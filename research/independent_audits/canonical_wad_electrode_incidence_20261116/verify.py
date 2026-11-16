#!/usr/bin/env python3
"""Exact finite checks of KKL native opposed-electrode typing, NOT a WAD solver.

Continuum prime-end / canonical-quadrilateral assertions are written arguments
in NOTE.md. Finite tests use integer/dyadic/Fraction arithmetic only.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[3]
TIP = ROOT / 'results/tip_KKL_tree_marked_breakage_20261109.json'
OUT = ROOT / 'results/canonical_wad_electrode_incidence_20261116.json'
DEN = 1 << 256
PARAM = (-607918036626757496169199575185708826140,
         -607918036626757496169199575185708826139)
BLOCKS = ((18, 19, 0, 1, 2), (3, 4), (5,), (6,), (7, 8, 9),
          (10,), (11, 12, 13), (14,), (15,), (16, 17))


def require(p: bool, why: str) -> None:
    if not p:
        raise AssertionError(why)


def sq(a: int, b: int) -> tuple[int, int]:
    v = (a*a, b*b) if a >= 0 or b <= 0 else (0, max(a*a, b*b))
    return min(v)//DEN, -(-max(v)//DEN)


def orbit(s: dict) -> dict[int, tuple[Q, Q]]:
    param = s['source_parameter']
    require(param['denominator_power_of_two'] == 128 and
            (param['lower_numerator'], param['upper_numerator']) == PARAM,
            'unchanged PR68 exact parameter')
    lo, hi = (n << 128 for n in PARAM)
    a = b = 0
    result = {}
    for k in range(1, 19):
        a, b = sq(a, b)
        a, b = a + lo, b + hi
        result[k] = Q(a, DEN), Q(b, DEN)
        require(a <= b, 'outward dyadic orbit ordering')
    require(Q(9, 50) < result[3][0] <= result[3][1] < Q(1, 5), 'x3')
    require(Q(-1, 5) < result[6][0] <= result[6][1] < Q(-7, 50), 'x6')
    require(result[6][1] < result[9][0] < 0 < result[18][0], 'ordered orbit')
    require(result[18][1] < result[12][0] < result[3][0], 'K0 to K1 geometry')
    require(result[6][1] < result[15][0] < result[9][0], 'K2 to K0 geometry')
    return result


def arctan(x: Q, n: int = 16) -> tuple[Q, Q]:
    require(0 < x < 1, 'atan reduction')
    p = sum(((-1)**k * x**(2*k+1) / (2*k+1) for k in range(n)), Q())
    e = x**(2*n+1)/(2*n+1)
    return (p, p+e) if n % 2 == 0 else (p-e, p)


def pi_range() -> tuple[Q, Q]:
    a, b = arctan(Q(1, 5))
    c, d = arctan(Q(1, 239))
    return 16*a-4*d, 16*b-4*c


def cos_range(x: Q) -> tuple[Q, Q]:
    require(0 <= x <= 1, 'Taylor cosine domain')
    terms = [(-1)**k*x**(2*k)/factorial(2*k) for k in range(9)]
    return sum(terms[:8], Q()), sum(terms, Q())


def log_range(x: Q) -> tuple[Q, Q]:
    require(x >= 1, 'log reduction domain')
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    z = (x-1)/(x+1)
    def atanh(t: Q) -> tuple[Q, Q]:
        s = sum((2*t**(2*j+1)/(2*j+1) for j in range(40)), Q())
        return s, s + 2*t**81/(81*(1-t*t))
    a,b = atanh(z)
    c,d = atanh(Q(1,3))
    return k*c+a, k*d+b


def marking(s: dict) -> dict:
    require(s['scope'].startswith('ACTUAL KKL'), 'not physical KKL marking')
    require(s['tree'] == '[x6,x3]' and
            s['tree_preimage_in_V3'] == '[-x3,x3]' and
            s['single_new_attachment'] == '[-x3,x6)', 'native trees')
    require(s['target_inner_marking_atoms'] == [
        'K2_terminal','edge_K2_K0_upper','K0_upper','edge_K0_alpha_upper',
        'edge_alpha_K1_upper','K1_terminal','edge_alpha_K1_lower',
        'edge_K0_alpha_lower','K0_lower','edge_K2_K0_lower'], 'ten original atoms')
    require(s['source_inner_cut_positions_increasing'] == [
        '-x12','x6','x15','-alpha','x9','x18','alpha','-x15','-x6','x12'],
            'ten physical source cut positions')
    flat = [i for block in BLOCKS for i in block]
    require(len(flat) == 20 and set(flat) == set(range(20)), '20-atom partition')
    require(s['inner_pullback_blocks'] == [list(x) for x in BLOCKS], 'source blocks')
    iota = [None] * 20
    for label, block in enumerate(BLOCKS):
        for atom in block:
            require(iota[atom] is None, 'nonoverlapping pullback blocks')
            iota[atom] = label
    f = [i % 10 for i in range(20)]
    require(iota == s['source_inclusion_pullback_atom_map'], 'immersion pullback labels')
    require(f == s['source_f_cover_atom_map'], 'degree-two covering labels')
    attachment = s['attachment_boundary_source_atoms']
    require(attachment == [19,0,1], 'attachment source atoms')
    opposed = [(atom + 10) % 20 for atom in attachment]
    require(opposed == [9,10,11], 'deck halfturn, not an arbitrary second arc')
    require(set(attachment).isdisjoint(opposed), 'two distinct source electrodes')
    require([f[i] for i in attachment] == [f[i] for i in opposed] == [9,0,1],
            'cover identifies both electrodes, not opposed target electrodes')
    require([iota[i] for i in attachment] == [0,0,0] and
            [iota[i] for i in opposed] == [4,5,6],
            'immersion does not send the two electrodes to the same host')
    require(all(i not in attachment for block in BLOCKS for i in (block[0],block[-1])),
            'attachment is interior to nonproper pullback block')
    require(s['not_proper_on_target_inner_atoms'] == [0] and
            s['end_proper_on_all_ten_inner_intervals'], 'nonproper vs end-proper')
    pairs = s['crossing_circle_source_restrictions']
    require(pairs == [[3,1],[19,17]], 'genuine filtered source pieces')
    require(s['marked_breakable_wave']['target_base_atoms'] == [9,0,1] and
            s['marked_breakable_wave']['target_crest_atom'] == 0,
            'source wave crest/base, not proof-selected')
    for pair in pairs:
        require(not (any(a in attachment for a in pair) and
                     any(b in opposed for b in pair)),
                'native restriction cannot be A_X to B_X')
    require(s['both_crossing_restrictions_pass_A1_and_single_pullback_cell_filters'],
            'A.1/A.3.2 restrictions valid')
    return {'attachment_atoms': attachment, 'deck_opposite_atoms': opposed,
            'f_star_attachment': [f[i] for i in attachment],
            'f_star_opposite': [f[i] for i in opposed],
            'iota_star_attachment': [iota[i] for i in attachment],
            'iota_star_opposite': [iota[i] for i in opposed],
            'known_wave_source_restrictions': pairs}


def certify() -> dict:
    s = json.loads(TIP.read_text(encoding='utf-8'))
    v = orbit(s)
    label = marking(s)
    p0,p1 = pi_range()
    require(Q(333,106) < p0 < p1 < Q(22,7), 'pi enclosure')
    x3a,x3b = v[3]; x6a,x6b = v[6]
    # A_X has angular length 2 acos(-x6/x3) on the physical source slit.
    ratio_low, ratio_high = -x6b/x3b, -x6a/x3a
    cos06low,_ = cos_range(Q(3,5))
    _,cos07high = cos_range(Q(7,10))
    require(cos07high < ratio_low <= ratio_high < cos06low,
            'source angular length strictly between 6/5 and 7/5')
    require(Q(7,5) < p0, 'deck-opposed inner electrode arcs disjoint')
    # G=f^3 is even. G([-x3,x6])=G([-x6,x3])=[x6,x9]
    # because G' = 8z*f(z)*f^2(z), with f<0<f^2 on [-x3,x3].
    c_lo = Q(PARAM[0], 1<<128); c_hi = Q(PARAM[1],1<<128)
    require(c_lo > -Q(9,5) and c_hi+x3b*x3b < -Q(17,10), 'f sign')
    require(Q(17,10)**2 - Q(9,5) > 0, 'f^2 sign')
    require(-x3a < x6a < x6b < v[9][0] < 0 < -x6b < x3a,
            'disjoint electrode segments, same target image [x6,x9]')
    h = Q(1,1024)
    displacement = x3b*h/(1-h)
    require(displacement < Q(1,4096) and x3b+displacement < Q(1,4),
            'whole physical source collar inside physical domain')
    derivative = 8*Q(1,4)*Q(33,16)*Q(1601,256)
    require(derivative < 26, 'whole disk complex G derivative')
    require(Q(1,5) + 26*displacement < Q(1,4), 'entire collar G image bound')
    require(1/(1-h) < Q(4,3), 'actual subwave remains within full wave')
    # Analytic free-outer condenser estimate (prior note, theorem (10)).
    # ell in (6/5,7/5), log(1+2/ell)<log(3)<3/2.
    require(sum((Q(3,2)**k/factorial(k) for k in range(4)), Q()) > 3,
            'rigorous log(3)<3/2')
    dlow = h/(p1/2 + 12*h/p0)
    dhigh = 2*h/(p0-Q(7,5))
    require(Q(3,5)*h < dlow < dhigh < Q(6,5)*h,
            'strict free-outer full contact capacity bracket')
    lo43,hi43 = log_range(Q(4,3))
    require(Q(1,25) < lo43/(2*p1) < hi43/(2*p0) < Q(1,20),
            'native EXHIBITED Wave width, not canonical WAD weight')
    require(h/(2*p0) < dlow and dhigh < lo43/(2*p1),
            'unmatched native subwave and full-wave strict order')
    return {
      'schema_version': 1,
      'source_tip': 'results/tip_KKL_tree_marked_breakage_20261109.json',
      'arithmetic': 'exact Fraction; 256-bit outward dyadic orbit; alternating rational pi/cos and atanh-log brackets',
      'canonical_definition': {
        'surface': 'U3\\K; K=K0 union K1 union K2 (three disjoint small Julia intervals)',
        'minimal_marking': 'four entire ideal boundary components: K0, K1, K2 and outer U3',
        'tree_wave_surface': 'U3\\T, ten-atom induced tree marking; distinct from proof-used canonical WAD',
        'formula': 'W_can(alpha)=max(0, Width(ideal_quadrilateral_of_lifted_end_intervals(alpha))-2)',
        'source': 'KKL Appendix A.2.1 and A.2.3; NOT the unbuffered width of a hand-chosen Wave',
        'proof_wave_selection': 'KKL Section 6: existential nearly maximal eta-controllable Wave; no specified canonical Wave at this tip',
        'weights_numerically_enclosed': False,
        'proof_selected_wave_constructed': False
      },
      'geometry': {
        'target': 'U3\\T, T=[x6,x3]',
        'canonical_small_julia_sets': 'K0=[x9,x18]; K1=[x12,x3]; K2=[x6,x15]',
        'canonical_WAD_surface': 'U3\\K, three-hole domain with minimal marking',
        'source': 'V3\\Tprime, Tprime=[-x3,x3]',
        'cover': 'G=f_c^3, even, degree two on V3; f_star',
        'immersion': 'iota: V3\\Tprime -> U3\\T, identity inclusion; iota_star restriction',
        'source_slit_chart': 'z=x3*(w+w^-1)/2, w->-w is deck halfturn',
        'attachment': 'X=[-x3,x6), A_X=prime-end sides of X',
        'opposite': 'B_X=deck translate of A_X, corresponding to [-x6,x3]',
        'covered_real_image': 'G(X)=G(-X)=[x6,x9] (appropriate endpoint closures)',
        'source_electrode_angle_interval': ['6/5','7/5'],
        'source_electrodes_disjoint': True,
        'physical_collar': '0<h<=1/1024; finite contact check at h=1/1024'
      },
      'marking': label,
      'incidence': {
        'theorem_6_applicable_to_canonical_target_WAD_and_source_Dh': False,
        'failed_clause': 'same C_h and every curve has endpoints in A_X and B_X; canonical U3\\K and tree Wave U3\\T are different surfaces',
        'countercheck': 'canonical U3\\K is not tree-Wave U3\\T or source C_h; cover folds A_X and B_X; iota is nonproper at A_X; marked restrictions fail',
        'comparison_from_this_certificate': 'none for canonical W_can; conditional general 0<=W(S)<=D_h has constant 1 only under verified inclusion'
      },
      'physical_free_outer_Dh': {
        'h': '1/1024', 'strict_lower': '3*h/5', 'strict_upper': '6*h/5',
        'analytic_input': 'prior wave_vs_dirichlet_contact_transfer_20261115 NOTE theorem (10)'
      },
      'exhibited_noncanonical_wave': {
        'full_width': 'log(4/3)/(2*pi)', 'strict_full_interval': ['1/25','1/20'],
        'subwave_width': 'h/(2*pi)',
        'relationship': 'W(subwave)<D_h<W(full wave); does not estimate W_can'
      },
      'numerical_only_observations': [],
      'open': ['evaluate all canonical buffered ideal quadrilaterals rigorously',
               'specify or establish existence of Section 6 proof-selected wide Wave at tip',
               'construct a surface/endpoint respecting transfer with quantitative richness',
               'uniform stage bounds and any large-rotation application']
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--check-manifest', action='store_true')
    group.add_argument('--write-manifest', action='store_true')
    args = parser.parse_args()
    result = certify()
    if args.write_manifest:
        OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n', encoding='utf-8')
        print('WROTE', OUT)
    elif args.check_manifest:
        require(json.loads(OUT.read_text(encoding='utf-8')) == result, 'result drift')
        print('PASS exact physical orbit, f_star/iota_star electrode mismatch, typed Wave and capacity bounds')
    else:
        print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
