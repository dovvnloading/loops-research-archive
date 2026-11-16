#!/usr/bin/env python3
"""Exact finite/gate certificate for a four-step physical marked Wave descendant.

Only integer/fixed-point interval and Fraction arithmetic is used by the
certificate.  Prime ends, central degree two, the KKL filters, conformal
univalence and extremal width are stated analytic inputs/proofs in NOTE.md.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PHASE = ROOT / 'results/tip_root_interval_geometry.json'
PR68 = ROOT / 'results/tip_KKL_tree_marked_breakage_20261109.json'
ISSUE40 = ROOT / 'results/issue40_native_attachment_edge_incidence_20261115.json'
RESULT = ROOT / 'results/issue40_crest_transport_20261116.json'
UNIT = 1 << 256
C0, A, B = Q(-9, 64), Q(1, 80), Q(1, 77)
ORIGINAL_A, ORIGINAL_B = Q(3, 256), Q(1, 64)


def demand(ok: bool, reason: str) -> None:
    if not ok:
        raise AssertionError(reason)


def ceildiv(a: int, b: int) -> int:
    return -((-a) // b)


@dataclass(frozen=True)
class Ball:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        demand(self.lo <= self.hi, 'bad interval')

    @staticmethod
    def point(x: Q | int) -> 'Ball':
        v = Q(x) * UNIT
        return Ball(v.numerator // v.denominator, ceildiv(v.numerator, v.denominator))

    @staticmethod
    def range(a: Q, b: Q) -> 'Ball':
        demand(a <= b, 'backwards rational range')
        return Ball(Ball.point(a).lo, Ball.point(b).hi)

    def __add__(self, b: 'Ball') -> 'Ball':
        return Ball(self.lo + b.lo, self.hi + b.hi)

    def __neg__(self) -> 'Ball':
        return Ball(-self.hi, -self.lo)

    def __sub__(self, b: 'Ball') -> 'Ball':
        return self + -b

    def __mul__(self, b: 'Ball') -> 'Ball':
        vals = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        return Ball(min(vals)//UNIT, ceildiv(max(vals), UNIT))

    def square(self) -> 'Ball':
        lo = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        hi = max(self.lo**2, self.hi**2)
        return Ball(lo//UNIT, ceildiv(hi, UNIT))

    def __pow__(self, n: int) -> 'Ball':
        demand(n >= 0, 'negative interval power')
        out = ONE
        for _ in range(n):
            out = out * self
        return out

    def less(self, b: 'Ball') -> bool:
        return self.hi < b.lo

    def within(self, a: 'Ball', b: 'Ball') -> bool:
        return a.less(self) and self.less(b)

    def abs_upper(self) -> Q:
        return Q(max(abs(self.lo), abs(self.hi)), UNIT)

    def rational_bounds(self) -> list[str]:
        return [str(Q(self.lo, UNIT)), str(Q(self.hi, UNIT))]


ZERO, ONE, TWO = Ball.point(0), Ball.point(1), Ball.point(2)


def G(z: Ball, c: Ball) -> Ball:
    for _ in range(3):
        z = z.square() + c
    return z


def polynomial_at(center: Q, c: Ball) -> list[Ball]:
    """Compute the *actual* degree-eight G(center+z), not a transition table."""
    p = [Ball.point(center), ONE]
    for _ in range(3):
        out = [ZERO] * (2 * len(p) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(p):
                out[i+j] = out[i+j] + a*b
        out[0] = out[0] + c
        p = out
    demand(len(p) == 9, 'wrong physical polynomial degree')
    return p


def dominate_linear(p: list[Ball], radius: Q, *, chebyshev: bool, sign: int) -> None:
    """Bound Im G / Im z and d(Re G)/d(cos theta) on a whole disk.

    |Im(z^k)/Im z| <= k R^(k-1); |T_k'(u)| <= k^2 for |u|<=1.
    """
    rest = sum(p[k].abs_upper() * (k*k if chebyshev else k) * radius**(k-1)
               for k in range(2, len(p)))
    if sign == 1:
        demand(Q(p[1].lo, UNIT) > rest, 'positive linear term not dominant')
    else:
        demand(-Q(p[1].hi, UNIT) > rest, 'negative linear term not dominant')


def real_G_of_circle(p: list[Ball], r: Ball, u: Ball) -> Ball:
    """Re G(C0+r exp(i theta)), u=cos theta; exact Chebyshev recurrence."""
    t0, t1 = ONE, u
    power, out = ONE, p[0]
    for k in range(1, len(p)):
        power = power * r
        tk = t1 if k == 1 else TWO*u*t1-t0
        out = out + p[k]*power*tk
        if k >= 2:
            t0, t1 = t1, tk
    return out


def imag_factor(p: list[Ball], r: Ball, u: Ball) -> Ball:
    """Im G(C0+r exp(i theta)) / (r sin theta); U_(k-1) recurrence."""
    v0, v1 = ONE, TWO*u
    power, out = ONE, ZERO
    for k in range(1, len(p)):
        vk = v0 if k == 1 else v1 if k == 2 else TWO*u*v1-v0
        out = out + p[k]*power*vk
        power = power*r
        if k >= 3:
            v0, v1 = v1, vk
    return out


def root_bracket(p: list[Ball], radius: Ball) -> tuple[Q, Q]:
    """Uniform cos(theta) enclosure over an entire rational radius bin."""
    lo, hi = Q(0), Q(1, 2)
    demand(real_G_of_circle(p, radius, Ball.point(lo)).hi < 0, 'cos 0-sign')
    demand(real_G_of_circle(p, radius, Ball.point(hi)).lo > 0, 'cos 1/2-sign')
    for _ in range(32):
        mid = (lo + hi)/2
        v = real_G_of_circle(p, radius, Ball.point(mid))
        if v.hi < 0:
            lo = mid
        elif v.lo > 0:
            hi = mid
        else:
            break
    demand(0 <= lo < hi <= Q(1,2), 'no unique angular gate interval')
    return lo, hi


def run(phase_path: Path = PHASE, pr68_path: Path = PR68,
        issue40_path: Path = ISSUE40, bins: int = 384) -> dict:
    demand(bins >= 64, 'too few radius bins for certified gate')
    phase = json.loads(phase_path.read_text())
    earlier = json.loads(pr68_path.read_text())
    audit = json.loads(issue40_path.read_text())
    par = phase['parameter_bracket']
    demand(par == {
        'denominator_power_of_two': 128,
        'lower_numerator': -607918036626757496169199575185708826140,
        'upper_numerator': -607918036626757496169199575185708826139},
        'physical parameter drift')
    demand('x18=-x9' in phase['exact_orbit_relations'], 'lost preperiodic identity')
    demand(phase['inner_root_exact_interval'] == '[x9,x18]', 'real root-tree drift')
    phase_rows = {row['physical_phase']: row for row in phase['phase_intervals']}
    for k, interval in ((0,'[x9,x18]'),(3,'[x12,x3]'),(6,'[x6,x15]')):
        demand(phase_rows[k]['coarse_phase'] == 0 and
               phase_rows[k]['exact_interval'] == interval,
               'real physical vertex geometry drift')
    demand(earlier['marked_breakable_wave']['target_base_atoms'] == [9,0,1]
           and earlier['marked_breakable_wave']['two_pushed_crest_atoms'] == [2,8]
           and earlier['marked_breakable_wave']['target_crest_atom'] == 0,
           'PR68 Wave changed')
    demand(audit['all_ten_iota_star_source_blocks'] == [
        [18,19,0,1,2], [3,4], [5], [6], [7,8,9], [10],
        [11,12,13], [14], [15], [16,17]], 'iota pullback drift')
    demand(audit['cover_f_star_source_to_target_atom'] == [j % 10 for j in range(20)],
           'covering drift')
    demand(audit['zero_old_edge_target_crest_atoms'] == [0,2,5,8],
           'old-edge carrier drift')
    demand(audit['target_atom_physical_regions'] ==
           ['K2','E20','K0','E0a','Ea1','K1','Ea1','E0a','K0','E20'],
           'physical edge types drift')

    c0 = Q(par['lower_numerator'], 1 << 128)
    c1 = Q(par['upper_numerator'], 1 << 128)
    c = Ball.range(c0, c1)
    x = [ZERO]
    for _ in range(18):
        x.append(x[-1].square()+c)
    alpha = Ball.range(Q(3,32),Q(1,10))
    coords = {'x3': x[3], 'x6': x[6], 'x9': x[9],
              'x12': x[12], 'x15': x[15], 'x18': x[18], 'alpha': alpha,
              '-x3': -x[3], '-x12': -x[12]}
    demand(x[18].lo <= (-x[9]).hi and (-x[9]).lo <= x[18].hi,
           'x18=-x9 rejected by interval arithmetic')
    demand(A > ORIGINAL_A and B < ORIGINAL_B and A < B, 'slab outside original Wave')
    demand(Q(80,77)**8 > Q(4,3), 'exact c=1/2 inequality failed')

    # Exact continuum disk containment for original selected slab through G^4.
    mid, err = (c0+c1)/2, (c1-c0)/2
    center, rad = C0, B
    disk_rows = []
    for n in range(1, 13):
        rad = 2*abs(center)*rad + rad*rad + err
        center = center*center + mid
        if n % 3 == 0:
            demand(abs(center)+rad < Q(1,4), 'selected entire disk leaves G^-1(U3)')
            disk_rows.append((n//3, center, rad))
    demand(abs(C0)+B < Q(1,4), 'original disk outside U3')
    for k, d, R in disk_rows[:3]:
        if k == 1:
            demand(abs(d)+R < Q(1,20), 'image lacks small disk bound')
        if k == 2:
            demand(d-R > 0, 'n=2 wave support crosses critical symmetry axis')
        if k == 3:
            demand(d+R < 0, 'n=3 wave support crosses critical symmetry axis')
    demand(C0+B < 0, 'original support not on negative side')
    # Each disk's center is in T', selecting the central inverse component.
    for _, d, _ in [(0,C0,B)] + disk_rows[:3]:
        demand(Q(coords['-x3'].hi, UNIT) < d < Q(coords['x3'].lo, UNIT),
               'disk-center/component selector failed')

    # Exact continuum sign controls: no extra real crossings.
    p0 = polynomial_at(C0,c)
    dominate_linear(p0,B,chebyshev=False,sign=1)
    dominate_linear(p0,B,chebyshev=True,sign=1)
    # G(w)=P(w^2), P'(0)<0; |w|<1/20 on the first image disk.
    p1 = Ball.point(4)*c*(c.square()+c)
    p2 = Ball.point(6)*c.square()+Ball.point(2)*c
    p3 = Ball.point(4)*c
    corr = (p2.abs_upper()*2*Q(1,400)
            +p3.abs_upper()*3*Q(1,400)**2 + 4*Q(1,400)**3)
    demand(Q(p1.hi,UNIT)+corr < 0, 'n=2 fold may have extraneous real crossings')
    d2,R2 = disk_rows[1][1:]
    dominate_linear(polynomial_at(d2,c),R2,chebyshev=False,sign=-1)

    min_gate_margin = None
    max_gate_margin = None
    root_limits = [Q(1,2),Q(0)]
    for j in range(bins):
        left = A+(B-A)*j/bins
        right = A+(B-A)*(j+1)/bins
        rb = Ball.range(left,right)
        u_left,u_right = root_bracket(p0,rb)
        root_limits[0] = min(root_limits[0],u_left)
        root_limits[1] = max(root_limits[1],u_right)
        ub = Ball.range(u_left,u_right)
        H = imag_factor(p0,rb,ub)
        demand(H.lo>0, 'first image no longer upper-half-plane')
        Y = rb.square()*(ONE-ub.square())*H.square()
        demand(Y.lo>0, 'crossing height vanished')
        # At Re G(z)=0, G(z)=i sqrt(Y); these are exact real polynomials.
        r2 = ((c-Y).square()+c).square()+c
        r3 = G(r2,c)
        r4 = G(r3,c)
        demand(r2.within(coords['x3'], Ball.point(Q(1,4))),
               f'n=2 real crossing is not beyond x3 (bin {j})')
        demand(r3.within(coords['-x3'], coords['-x12']),
               f'n=3 gate not in SOURCE S0 attachment (bin {j})')
        demand(r4.within(coords['x6'], coords['x15']),
               f'n=4 gate image not inside K2 (bin {j})')
        q, w = Ball.point(C0)+rb, Ball.point(C0)-rb
        demand(q.within(coords['x15'], -alpha), 'initial right endpoint not in E20')
        demand(w.within(coords['-x12'], coords['x6']), 'first gate changed')
        for n in range(1,5):
            q,w = G(q,c), G(w,c)
            if n == 1:
                demand(q.within(coords['x18'],alpha) and
                       w.within(-alpha,coords['x9']), 'n=1 S6 / S4 gate drift')
            if n == 2:
                demand(q.within(-coords['x6'],coords['x12']) and
                       w.within(-coords['x6'],coords['x12']),
                       'n=2 S9 / S11 gate drift')
            if n == 3:
                demand(q.within(coords['x15'],-alpha) and
                       w.within(coords['x15'],coords['x9']),
                       'n=3 S3 / E20 lower-side gate drift')
            if n == 4:
                demand(q.within(coords['x18'],alpha), 'n=4 positive edge base drift')
        margin_lo = Q(r3.lo-coords['-x3'].hi,UNIT)
        margin_hi = Q(coords['-x12'].lo-r3.hi,UNIT)
        low = min(margin_lo,margin_hi)
        min_gate_margin = low if min_gate_margin is None else min(min_gate_margin,low)
        high = max(margin_lo,margin_hi)
        max_gate_margin = high if max_gate_margin is None else max(max_gate_margin,high)

    demand(min_gate_margin > Q(1,4096), 'gate is not separated by a fixed rational margin')
    demand(Q(3,32) <= root_limits[0] and root_limits[1] <= Q(7,64),
           'angular certificate weakened')
    # Source-defined q-side wave: first iota*, then covering G*.
    pullback = audit['all_ten_iota_star_source_blocks']
    host = {s: i for i, block in enumerate(pullback) for s in block}
    cover = audit['cover_f_star_source_to_target_atom']
    demand(host[0] == 0 and host[3] == 1 and host[17] == 9,
           'iota* source hosts collapsed')
    demand(cover[0] == 0 and cover[3] == 3 and cover[17] == 7,
           'G* covering hosts collapsed')
    demand(1+min((6-4)%20,(4-6)%20) == 3 and
           1+min((11-9)%20,(9-11)%20) == 3 and
           1+min((3-0)%20,(0-3)%20) == 4 and
           1+min((3-0)%10,(0-3)%10) == 4,
           'native KKL short family exclusions not cleared')
    demand(audit['target_atom_physical_regions'][1] == 'E20' and
           audit['target_atom_physical_regions'][9] == 'E20',
           'closed crest lacks actual old-tree edge sides')

    return {
        'schema_version':1,
        'claim':'four covering pushes and distinct immersion restrictions yield TWO genuine crest-positive marked sub-Waves on a certified rational radius slab',
        'input_parameter_bracket':par,
        'source_lock':{'PR68_target_wave_base':[9,0,1],
                       'PR68_two_pushed_crests':[2,8],
                       'issue40_zero_edge_atoms':[0,2,5,8]},
        'slab_radius_open':[str(A),str(B)],
        'original_radius_open':[str(ORIGINAL_A),str(ORIGINAL_B)],
        'whole_radius_bin_count':bins,
        'first_image_imaginary_axis_gate_cosine_strict_bounds':[
            str(root_limits[0]),str(root_limits[1])],
        'n3_gate_source_atom':'S0 (between -x3 and -x12, one terminal atom through the tip)',
        'n3_gate_min_strict_margin_lower_bound':'1/4096',
        'n4_gate_image':'I0 K2 interior',
        'first_three_closed_crest_types':[[2,8],[5,5],[0,0]],
        'fourth_closed_crest_atoms':{'upper_q_side':[1,2], 'lower_q_side':[8,9]},
        'fourth_closed_crest_old_tree_edge_atoms':{'upper_q_side':[1], 'lower_q_side':[9]},
        'source_q_side_endpoint_atoms':[0,3],
        'source_q_side_iota_pullback_hosts':[0,1],
        'source_q_side_covering_endpoint_atoms':[0,3],
        'KKL_short_span_source_and_target':4,
        'exact_original_width':'log(4/3)/(2*pi)',
        'exact_new_width':'integral_{1/80}^{1/77} dr/(r*theta(r)), theta(r)=arccos(u(r)), Re G(-9/64+r*(u+i*sqrt(1-u^2)))=0, 0<u<1/2',
        'exact_ratio':'(2*pi/log(4/3))*integral_{1/80}^{1/77} dr/(r*theta(r))',
        'certified_lower_bound':{'c':'1/2',
              'analytic_comparison':'theta(r)<pi/2 implies W_new>2*log(80/77)/pi',
              'rational_witness':'(80/77)^8 > 4/3'},
        'finite_proof_scope':[
            'All radius bins, exact orbit/cut endpoint orders, degree-two source and covering labels, unique cos(theta) gate, and margin from cut endpoints are certified by 256-bit outward balls.',
            'Univalence, entire central component and slit prime ends use existing native analytic inputs. The integral formula is proved by Cauchy-Schwarz and Fubini, not inferred by machine arithmetic.',
            'This 1/2 is a fixed physical-tip statement USING a quantitatively certified analytic collar; it is not a theorem from finite atom counts or Perron eigenvalues alone.',
            'No arbitrary proof-selected or non-LC Wave, no uniform return-step count, and no global KKL crest-transport theorem is certified.'
        ]}


def negative_controls() -> None:
    import tempfile
    from copy import deepcopy
    phase, earlier, audit = (json.loads(p.read_text()) for p in (PHASE,PR68,ISSUE40))
    wrong = []
    v=deepcopy(phase)
    v['parameter_bracket']['upper_numerator'] += 1
    wrong.append(('parameter mutation',v,earlier,audit))
    v=deepcopy(earlier)
    v['marked_breakable_wave']['two_pushed_crest_atoms']=[1,9]
    wrong.append(('fake edge crests at step one',phase,v,audit))
    v=deepcopy(audit)
    v['all_ten_iota_star_source_blocks'][0].remove(0)
    wrong.append(('lost terminal S0 attachment',phase,earlier,v))
    v=deepcopy(audit)
    v['cover_f_star_source_to_target_atom'][0]=1
    wrong.append(('conflated G* and iota*',phase,earlier,v))
    with tempfile.TemporaryDirectory() as tmp:
        f=[Path(tmp)/n for n in ('phase.json','earlier.json','audit.json')]
        for label,x,y,z in wrong:
            for path,data in zip(f,(x,y,z)):
                path.write_text(json.dumps(data))
            try:
                run(*f,bins=64)
            except AssertionError:
                pass
            else:
                raise AssertionError('negative control accepted: '+label)
    print('PASS: adversarial phase, first-wave edge, missing S0, and conflated G*/iota* rejected')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write-manifest', action='store_true')
    mode.add_argument('--check-manifest', action='store_true')
    mode.add_argument('--adversarial', action='store_true')
    args = parser.parse_args()
    if args.adversarial:
        negative_controls()
        return
    result = run()
    if args.write_manifest:
        RESULT.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
        print('WROTE',RESULT)
    elif args.check_manifest:
        demand(json.loads(RESULT.read_text()) == result, 'locked manifest drift')
        print('PASS: 384 whole-radius interval bins, unique real gate in S0, two crest-positive depth-four marked descendants, rational c=1/2')
    else:
        print(json.dumps(result,sort_keys=True,indent=2))


if __name__ == '__main__':
    main()
