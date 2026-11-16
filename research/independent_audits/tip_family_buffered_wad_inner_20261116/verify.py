#!/usr/bin/env python3
"""Read-only exact inner-arc bounds for the real primitive-tip KKL surface.

Not a uniformization or a solution of the six inner support problems.
The continuum inputs (KKL canonical lamination, SC map, AGMs, covering
comparison and annular comparison) are explicitly proved/cited in NOTE.md.
All decisions made here use Fraction and integer isqrt, never floats.
"""
from __future__ import annotations

import importlib.util
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUDITS = HERE.parent
OLD_FILE = AUDITS / 'tip_family_buffered_wad_20261116' / 'verify.py'


def require(ok: bool, why: str) -> None:
    if not ok:
        raise AssertionError(why)


def import_file(path: Path, tag: str):
    require(path.is_file(), 'missing pinned predecessor: ' + str(path))
    spec = importlib.util.spec_from_file_location(tag, path)
    require(spec is not None and spec.loader is not None, 'bad Python import')
    mod = importlib.util.module_from_spec(spec)
    sys.modules[tag] = mod
    spec.loader.exec_module(mod)
    return mod


old = import_file(OLD_FILE, 'buffered_wad_inner_pinned_outer')
# Endpoint lengths in all selected charts, with no new physical assumptions.
INNER = {'K0': (3, 6), 'K1': (4, 1), 'K2': (2, 5)}
DIRECT = (('K2', 'K0'), ('K0', 'K1'), ('K2', 'K1'))
# Rational lower bounds on exp(-ell_I/2); checked against the *strict*
# rational upper on ell_I via 2*pi^2/log(t_I).
KPRIME_FLOORS = {'K0': F(1, 62), 'K1': F(3, 38), 'K2': F(2, 43)}
# Rational upper bounds for q of *every* admissible arc incident on I.
Q_CAPS = {'K0': F(351, 100), 'K1': F(5, 2), 'K2': F(57, 20)}
GRID = 1000


def sqrt_floor(x: F, bits: int = 96) -> F:
    """Certified dyadic floor for sqrt(x), using no approximate floats."""
    require(type(x) is F and x >= 0 and bits >= 32, 'bad sqrt input')
    unit = 1 << bits
    val = F(math.isqrt((x.numerator * unit * unit) // x.denominator), unit)
    require(val * val <= x < (val + F(1, unit))**2,
            'integer square-root outward rounding error')
    return val


def agm_lower(r: F, steps: int = 4) -> F:
    """Lower bound on AGM(1,r) from monotone geometric iterates."""
    require(type(r) is F and 0 < r < 1 and steps >= 1, 'bad AGM input')
    a, b = F(1), r
    for _ in range(steps):
        a, b = (a + b) / 2, sqrt_floor(a * b)
        require(0 < b <= a <= 1, 'AGM iteration lost order')
    return b


def prove_q_cap(quad, label: str, t: F, r: F, cap: F) -> tuple[F, F]:
    """Elliptic K/AGM upper: ell < 2log(1/r), q < cap.

    For k'=exp(-ell/2) > r, q=AGM(1,sqrt(1-k'^2))/AGM(1,k')
    <= AGM(1,sqrt(1-r^2))/AGM(1,r).
    Numerator <= (1+sqrt(1-r^2))/2 <= 1-r^2/4; denominator
    >= the certified geometric AGM iterate. All inequalities strict at cap.
    """
    require(label in INNER and type(t) is F and type(r) is F and
            type(cap) is F and 0 < r < 1, 'bad q cap constants')
    _, ell_hi = old.width_log_length_bounds(quad, t)
    log_inv_lo, _ = quad.log_range(1 / r)
    require(ell_hi < 2 * log_inv_lo,
            label + ': collar cannot certify k-prime floor')
    upper = (1 - r*r/4) / agm_lower(r)
    require(upper < cap, label + ': AGM bound does not certify q cap')
    return ell_hi, upper


def mobius_halfdisk(x: F, R: F) -> F:
    """Boundary restriction of ((R+z)/(R-z))^2 from upper halfdisk to H."""
    require(-R < x < R, 'electrode not strictly in diameter')
    return ((R + x)/(R - x))**2


def strict_root_fourth_floor(s: F, grid: int = GRID) -> F:
    """Find largest n/grid with (n/grid)^4 < s, purely by integer tests."""
    require(type(s) is F and 0 < s < 1 and grid >= 2, 'bad crossratio')
    lo, hi = 0, grid
    while lo + 1 < hi:
        mid = (lo + hi)//2
        if F(mid, grid)**4 < s:
            lo = mid
        else:
            hi = mid
    out = F(lo, grid)
    require(out**4 < s and (lo == grid - 1 or
            s <= F(lo+1, grid)**4), 'incorrect exact fourth-root floor')
    require(out > 0, 'selected direct lower certificate vanished')
    return out


def direct_subquadrilaterals(xi, R: F) -> dict[str, dict[str, str]]:
    """Three *named upper-side simple classes*, not all inner classes.

    Inscribe rational electrode subsegments into each actual slit using
    outward predecessor endpoint intervals. Inscribe the upper halfdisk of
    radius R inside the physical disk. Its SC crossratio is an exact lower
    bound for the universal-cover ideal quadrilateral of each direct class.
    """
    require(type(R) is F and R > 0, 'bad exact inscribed radius')
    cuts = {}
    for name, (i, j) in INNER.items():
        a, b = xi[i].high(), xi[j].low()
        require(-R < a < b < R, name + ': no valid inner electrode')
        cuts[name] = (a, b)
    require(cuts['K2'][1] < cuts['K0'][0] and
            cuts['K0'][1] < cuts['K1'][0], 'false physical inner order')
    report = {}
    for left, right in DIRECT:
        a, b = cuts[left]
        c, d = cuts[right]
        A, B, C, D = (mobius_halfdisk(x, R) for x in (a,b,c,d))
        require(0 < A < B < C < D, 'incorrect SC endpoint order')
        s = (B-A)*(D-C)/((C-A)*(D-B))
        require(0 < s < 1, 'incorrect ideal quadrilateral crossratio')
        low = strict_root_fourth_floor(s)
        report[left + '-' + right] = {
            'certified_direct_class_q_strict_lower': str(low),
            'method': 'upper-halfdisk embedded SC rectangle; q>crossratio^(1/4)',
            'buffered_weight_positive_certified': False,
        }
    return report


def type_caps() -> dict[str, str]:
    """All six inner types, *every* simple class, including returning ones.

    The local weight estimate improves the returning-type cap but is valid
    even if its buffered weight is zero. Self arcs count twice locally.
    """
    caps = {}
    labels = ('K0', 'K1', 'K2')
    for i, a in enumerate(labels):
        for b in labels[i:]:
            local = (F(2) + old.INNER_B[a]/2 if a == b
                     else F(2) + min(old.INNER_B[a], old.INNER_B[b]))
            caps[a + '-' + b] = str(min(local, Q_CAPS[a], Q_CAPS[b]))
    return caps


def strict_ceiling(x: F, denominator: int = GRID) -> F:
    """Always strictly above x, including when x is exactly on the grid."""
    require(type(x) is F and x >= 0 and denominator >= 1,
            'invalid upper enclosure')
    return F(x.numerator * denominator // x.denominator + 1, denominator)


def certify() -> dict:
    predecessor = old.certify()  # exact roots / all-p boxes / existing collars
    require(predecessor['all_classes_enumerated'] is False and
            predecessor['any_positive_canonical_weight_certified'] is False,
            'pinned predecessor has different logical scope')
    quad = old.load_verifier('canonical_wad_quadrilateral_moduli_20261116',
                             'wad_inner_pinned_quad')
    ell = {}
    for label, (r, cap) in ((i, (KPRIME_FLOORS[i], Q_CAPS[i]))
                             for i in INNER):
        e, cap_raw = prove_q_cap(quad, label, old.INNER_T[label], r, cap)
        ell[label] = {'peripheral_ell_strict_upper': str(e),
                      'certified_agm_q_strict_upper_raw': str(cap_raw),
                      'all_incident_class_q_strict_upper': str(cap)}

    finite = old.load_verifier('tip_family_finite_p_wave_gain_20261116',
                                'wad_inner_pinned_finite')
    packets = json.loads(old.OLD.read_text(encoding='utf-8'))['periods']
    require([row['p'] for row in packets] == list(range(3,13)),
            'missing selected-root chart')
    finite_data = []
    pi_lo, pi_hi = quad.pi_range()
    for row in packets:
        p, xi, radius = old.chart_for_finite(finite, row)
        old.check_order(xi)
        for label in INNER:
            old.ellipse_check(xi, radius, label, old.INNER_T[label])
        old.ellipse_check(xi, radius, 'outer', old.OUTER_T[p])
        q_lowers = direct_subquadrilaterals(xi, radius.low())
        if p < 11:
            log_lower, _ = quad.log_range(old.OUTER_T[p])
            out_width_hi = 2*pi_hi/log_lower
            norm_upper = strict_ceiling((sum(old.INNER_B.values(), F(0))+
                                         out_width_hi)/2)
        else:
            norm_upper = old.MAX_NORM_TAIL
        finite_data.append({
            'p': p, 'three_direct_inner_classes': q_lowers,
            'all_six_inner_type_q_upper': type_caps(),
            'canonical_norm_nonnegative_strict_upper': str(norm_upper),
            'outer_incident_excluded': p >= 11,
        })

    tail_xi, tail_R = old.tail_chart(finite)
    for label in INNER:
        old.ellipse_check(tail_xi, tail_R, label, old.INNER_T[label])
    old.ellipse_check(tail_xi, tail_R, 'outer', old.TAIL_OUTER_T)
    tail_lowers = direct_subquadrilaterals(tail_xi, tail_R.low())
    return {
        'status': 'PARTIAL: qualitative finiteness and per-class upper bounds; support/positivity still OPEN',
        'analytic_inputs': ['KKL A.2.2-A.2.5', 'cyclic-cover theorem of pinned audit',
                            'SC upper-halfdisk comparison', 'complete-elliptic-integral AGM identity'],
        'numerical_only': [],
        'agms_for_all_p_ge_3': ell,
        'type_q_upper_applies_to_every_inner_class': type_caps(),
        'finite_p3_to_p12': finite_data,
        'all_p_ge_13': {
            'three_direct_inner_classes': tail_lowers,
            'all_six_inner_type_q_upper': type_caps(),
            'canonical_norm_nonnegative_strict_upper': str(old.MAX_NORM_TAIL),
            'outer_incident_excluded': True,
        },
        'support_cardinality_upper_by_KKL': 10,
        'support_classes_effectively_enumerated': False,
        'any_inner_q_shown_greater_than_2': False,
        'any_positive_canonical_weight_certified': False,
        'norm_vanishing_certified': False,
        'remaining_extremal_problem':
            'effective finite inner-class reduction and rigorous uniform-cover crossratio enclosures relative to q=2',
    }


def main() -> None:
    out = certify()
    print('Exact AGM classwise upper bounds: ' +
          ', '.join(k + ': q<' + str(v) for k,v in type_caps().items()))
    for row in out['finite_p3_to_p12']:
        lowers = row['three_direct_inner_classes']
        print('p=%d: direct lower q > %s; norm < %s' %
              (row['p'], ', '.join(k+' '+v['certified_direct_class_q_strict_lower']
                                 for k,v in lowers.items()),
               row['canonical_norm_nonnegative_strict_upper']))
    print('p>=13: uniform direct lower q > ' +
          ', '.join(k+' '+v['certified_direct_class_q_strict_lower']
                    for k,v in out['all_p_ge_13']['three_direct_inner_classes'].items()))
    print('PASS: exact arithmetic for stated analytic inputs; buffered support remains OPEN')


if __name__ == '__main__':
    main()