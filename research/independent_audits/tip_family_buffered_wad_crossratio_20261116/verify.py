#!/usr/bin/env python3
"""Exact comparison-domain cross-ratios; NOT ideal-lift uniformization.

All arithmetic here is Fraction/isqrt. Previous selected-root and p>=13
interval charts are imported read-only. Continuum conformal/topological
arguments (SC, AGM, conjugation, KKL) are separated in NOTE.md.
"""
from __future__ import annotations

import importlib.util
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUDITS = HERE.parent
# All production deployments put this new directory next to predecessor.
PREVIOUS = AUDITS / 'tip_family_buffered_wad_inner_20261116' / 'verify.py'
ENDPOINTS = {'K2': (2, 5), 'K0': (3, 6), 'K1': (4, 1)}
PAIRS = (('K2', 'K0'), ('K0', 'K1'), ('K2', 'K1'))
BITS = 128
Q_GRID = 1000
S_GRID = 10**9


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def pinned_predecessor():
    require(PREVIOUS.is_file(), 'missing immutable inner WAD predecessor')
    tag = 'tip_crossratio_pinned_inner'
    spec = importlib.util.spec_from_file_location(tag, PREVIOUS)
    require(spec is not None and spec.loader is not None, 'bad predecessor loader')
    mod = importlib.util.module_from_spec(spec)
    sys.modules[tag] = mod
    spec.loader.exec_module(mod)
    return mod


def sqrt_bounds(x: Q, bits: int = BITS) -> tuple[Q, Q]:
    """Rational enclosing interval for sqrt(x) rounded at 2^-bits."""
    require(type(x) is Q and x >= 0 and 32 <= bits <= 256,
            'nonrational/negative square root or invalid precision')
    unit = 1 << bits
    n = math.isqrt((x.numerator * unit * unit)//x.denominator)
    low = Q(n, unit)
    high = low if low*low == x else Q(n+1, unit)
    require(low*low <= x <= high*high and high-low <= Q(1, unit),
            'incorrect outward square root')
    return low, high


def agm_bounds(xlo: Q, xhi: Q, steps: int = 7) -> tuple[Q, Q]:
    """Enclose AGM(1,x), x in [xlo,xhi]; b_n <= AGM <= a_n."""
    require(type(xlo) is Q and type(xhi) is Q and
            0 < xlo <= xhi <= 1 and 1 <= steps <= 12,
            'invalid AGM initial interval')
    alo = ahi = Q(1)
    blo, bhi = xlo, xhi
    for _ in range(steps):
        next_alo, next_ahi = (alo+blo)/2, (ahi+bhi)/2
        next_blo = sqrt_bounds(alo*blo)[0]
        # The true geometric iterate is <= the arithmetic iterate.
        # Intersect the outward square-root cap with that exact bound:
        # without this step rounding can make b_hi > a_hi by one ulp.
        next_bhi = min(sqrt_bounds(ahi*bhi)[1], next_ahi)
        alo, ahi, blo, bhi = next_alo, next_ahi, next_blo, next_bhi
        require(0 < blo <= bhi <= 1 and 0 < alo <= ahi <= 1 and
                blo <= alo and bhi <= ahi,
                'AGM enclosure/order failure')
    return blo, ahi


def elliptic_E_bounds(s: Q) -> tuple[Q, Q]:
    """Exact certified bracket of E(s)=K(sqrt(s))/K(sqrt(1-s)).

    E(s)=AGM(1,sqrt(s)) / AGM(1,sqrt(1-s)). Elliptic/AGM
    identity itself is a standard analytic input, not proved by Python.
    """
    require(type(s) is Q and 0 < s < 1, 'invalid elliptic modulus')
    nlo, nhi = agm_bounds(*sqrt_bounds(s))
    dlo, dhi = agm_bounds(*sqrt_bounds(1-s))
    lo, hi = nlo/dhi, nhi/dlo
    require(0 < lo <= hi, 'invalid elliptic ratio enclosure')
    return lo, hi


def strict_floor(x: Q, denominator: int) -> Q:
    require(type(x) is Q and x > 0 and denominator >= 2, 'bad grid floor')
    n = (x.numerator * denominator)//x.denominator - 1
    y = Q(n, denominator)
    require(y < x, 'non-strict downward enclosure')
    return y


def strict_ceil(x: Q, denominator: int) -> Q:
    require(type(x) is Q and x >= 0 and denominator >= 2, 'bad grid ceiling')
    n = (x.numerator * denominator)//x.denominator + 1
    y = Q(n, denominator)
    require(x < y, 'non-strict upward enclosure')
    return y


def threshold_sign(s: Q) -> int:
    """Sign of s-(12 sqrt(2)-16), with EXACT integer arithmetic.

    On (0,1), x^2+32*x-32 increases strictly, vanishing at s*.
    Returns -1 or +1; zero is impossible for rational s in (0,1).
    """
    require(type(s) is Q and 0 < s < 1, 'threshold argument outside (0,1)')
    poly = s*s+32*s-32
    require(poly != 0, 's* is irrational; rational equality impossible')
    return -1 if poly < 0 else 1


def t_halfdisk(x: Q, radius: Q) -> Q:
    require(type(x) is Q and type(radius) is Q and -radius < x < radius,
            'half-disk endpoint outside physical diameter')
    return ((radius+x)/(radius-x))**2


def standard_crossratio(a: Q, b: Q, c: Q, d: Q) -> Q:
    require(all(type(x) is Q for x in (a,b,c,d)) and a<b<c<d,
            'wrong order for cross-ratio')
    s = (b-a)*(d-c)/((c-a)*(d-b))
    require(0 < s < 1, 'invalid ordered cross-ratio')
    return s


def halfdisk_crossratio(a: Q, b: Q, c: Q, d: Q,
                        radius: Q | None) -> Q:
    """Cross-ratio of four *physical comparison-domain* endpoints.

    radius=None means the R->infinity (upper-halfplane) limit.
    This is NOT a cross-ratio of four ideal lifts of Y_K,p.
    """
    s_inf = standard_crossratio(a,b,c,d)
    if radius is None:
        return s_inf
    require(type(radius) is Q and radius > 0 and
            -radius < a < b < c < d < radius,
            'invalid whole physical halfdisk comparison')
    t = radius*radius
    # Rational cancellation avoids enormous four Möbius squares.
    s = s_inf*(t-a*b)*(t-c*d)/((t-a*c)*(t-b*d))
    require(0 < s < s_inf and
            s == standard_crossratio(*(t_halfdisk(x,radius)
                                       for x in (a,b,c,d))),
            'halfdisk formula/cancellation mismatch')
    return s


def physical_slit_corners(xi, name: str, inscribed: bool) -> tuple[Q,Q]:
    require(name in ENDPOINTS, 'not one of the actual three complete slits')
    left,right = ENDPOINTS[name]
    a = xi[left].high() if inscribed else xi[left].low()
    b = xi[right].low() if inscribed else xi[right].high()
    require(type(a) is Q and type(b) is Q and a < b,
            'endpoints misordered or uncertified')
    return a,b


def physical_pair_interval(xi, radius_low: Q,
                           radius_high: Q | None, pair: tuple[str,str]) -> dict:
    """Enclose the complete physical H_{rho} cross-ratio, not q_gamma.

    For a<b<c<d, cross-ratio increases when a,c decrease, b,d
    increase; it also increases as halfdisk radius grows. In the tail,
    rho is unbounded and the upper comparison uses R=infinity.
    """
    require(pair in PAIRS and type(radius_low) is Q and radius_low > 0 and
            (radius_high is None or
             (type(radius_high) is Q and radius_low <= radius_high)),
            'invalid class or target radius interval')
    a,b = physical_slit_corners(xi,pair[0],True)
    c,d = physical_slit_corners(xi,pair[1],True)
    A,B = physical_slit_corners(xi,pair[0],False)
    C,D = physical_slit_corners(xi,pair[1],False)
    require(-radius_low < A <= a < b <= B < C <= c < d <= D < radius_low,
            'four corners do not enclose true ordered physical electrodes')
    slo = halfdisk_crossratio(a,b,c,d,radius_low)
    shi = halfdisk_crossratio(A,B,C,D,radius_high)
    require(0 < slo <= shi < 1, 'invalid outward physical s interval')
    elo, _ = elliptic_E_bounds(slo)
    _, ehi = elliptic_E_bounds(shi)
    require(0 < elo <= ehi, 'elliptic monotonicity/certification failed')
    s_lo_grid = strict_floor(slo,S_GRID)
    s_hi_grid = strict_ceil(shi,S_GRID)
    q_lo_grid = strict_floor(elo,Q_GRID)
    q_hi_grid = strict_ceil(ehi,Q_GRID)
    require(0 < s_lo_grid < slo <= shi < s_hi_grid < 1 and
            0 < q_lo_grid < elo <= ehi < q_hi_grid < 2,
            'grid cannot separate physical comparison quadrilateral below 2')
    require(threshold_sign(shi) == -1,
            'halfdisk full-endpoint upper crossratio exceeds q=2 threshold')
    return {
        'physical_halfdisk_crossratio_strict_bracket':
            [str(s_lo_grid),str(s_hi_grid)],
        'physical_halfdisk_elliptic_width_strict_bracket':
            [str(q_lo_grid),str(q_hi_grid)],
        'named_upper_direct_true_q_strict_lower': str(q_lo_grid),
        'true_q_strict_upper_from_prior_all_class_cap': None,
        'comparison_upper_is_NOT_true_q_upper': True,
        'ideal_lift_endpoints_certified': False,
        'q_greater_than_two_certified': False,
    }


def certify() -> dict:
    previous = pinned_predecessor()
    prior = previous.certify()   # includes all predecessor interval/radius/collar checks
    require(prior['support_classes_effectively_enumerated'] is False and
            prior['any_positive_canonical_weight_certified'] is False,
            'predecessor no longer matches open classification')
    outer = previous.old
    finite = outer.load_verifier('tip_family_finite_p_wave_gain_20261116',
                                 'crossratio_pinned_finite')
    packets = json.loads(outer.OLD.read_text(encoding='utf-8'))['periods']
    require([r['p'] for r in packets] == list(range(3,13)),
            'selected charts p=3..12 not complete')
    caps = previous.type_caps()
    require(set(caps) == {'K0-K0','K0-K1','K0-K2',
                           'K1-K1','K1-K2','K2-K2'},
            'lost one of six inner endpoint types')
    finite_results = []
    for packet in packets:
        p, xi, radius = outer.chart_for_finite(finite,packet)
        outer.check_order(xi)
        results = {}
        for pair in PAIRS:
            key = '-'.join(pair)
            data = physical_pair_interval(xi, radius.low(), radius.high(), pair)
            data['true_q_strict_upper_from_prior_all_class_cap'] = caps.get(
                '-'.join(sorted(pair)))
            # sorted alpha K0,K1,K2, reverse K2-K0 etc
            require(data['true_q_strict_upper_from_prior_all_class_cap'] is not None,
                    'missing true classwise q bound')
            results[key] = data
        finite_results.append({'p':p, 'pair_comparison_domains':results,
                               'outer_incident_excluded':p>=11,
                               'canonical_norm_nonnegative_strict_upper':
                               prior['finite_p3_to_p12'][p-3]
                                    ['canonical_norm_nonnegative_strict_upper']})
    xi,radius_floor = outer.tail_chart(finite)
    tail = {}
    for pair in PAIRS:
        key = '-'.join(pair)
        data = physical_pair_interval(xi,radius_floor.low(),None,pair)
        data['true_q_strict_upper_from_prior_all_class_cap'] = caps['-'.join(sorted(pair))]
        tail[key] = data
    require(all(v['true_q_strict_upper_from_prior_all_class_cap'] is not None
                for v in tail.values()), 'lost all-p q upper')
    return {
        'status': 'PARTIAL: physical halfdisk crossratios certified; ideal-lift crossratios and canonical support OPEN',
        'method': 'exact rational physical endpoints; monotonic radius/corners; AGM enclosing elliptic E(s)',
        'finite_p3_to_p12': finite_results,
        'all_p_ge_13': {'pair_comparison_domains':tail,
                        'outer_incident_excluded':True,
                        'canonical_norm_nonnegative_strict_upper':
                            prior['all_p_ge_13']['canonical_norm_nonnegative_strict_upper']},
        'all_six_inner_type_q_strict_upper': caps,
        'returning_types': ('K0-K0','K1-K1','K2-K2'),
        'reflection_K2_K1_upper_lower_equal_q':
            'ANALYTIC: two distinct classes; conjugation preserves q (not checked by finite arithmetic)',
        'support_cardinality_upper_KKL': 10,
        'effective_deck_word_exclusion': False,
        'uniformization_of_actual_four_hole_surface': False,
        'no_inner_q_comparison_with_two': True,
        'any_positive_canonical_weight_certified': False,
        'norm_vanishing_certified': False,
        'numerical_only': [],
        'open': ['ideal-lift endpoints for every simple class',
                 'effective deck-word tail theorem',
                 'q threshold decisions (including returning classes)',
                 'full W_can support and norm lower',
                 'leafwise buffered-WAD/Wave amplification comparison'],
    }


def main() -> None:
    out = certify()
    for row in out['finite_p3_to_p12'] + [{'p':'>=13', **out['all_p_ge_13']}]:
        parts = []
        for pair,values in row['pair_comparison_domains'].items():
            parts.append(pair+': s_H in '+str(values['physical_halfdisk_crossratio_strict_bracket'])+
                         ', E(s_H) in '+str(values['physical_halfdisk_elliptic_width_strict_bracket']))
        print('p='+str(row['p'])+'; '+'; '.join(parts))
    print('PASS: physical comparison enclosures exact; ideal-lift crossratio/support OPEN')


if __name__ == '__main__':
    main()
