#!/usr/bin/env python3
"""Source-derived tip KKL attachment and Hubbard-edge incidence certificate.

The only dynamical input is the existing certified parameter/phase certificate
and G(z)=(z^2+c)^2+c, iterated once more (G=f_c^3).  In particular NO finite
transition matrix is an input.  The real slit/prime-end identification, the
central degree-two V3 restriction and KKL Prop. 6.5 are ANALYTIC inputs, not
purportedly proved by this integer program.
"""
from __future__ import annotations

import argparse
import json
import hashlib
from copy import deepcopy
from tempfile import TemporaryDirectory
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PHASE = ROOT / 'results/tip_root_interval_geometry.json'
PREVIOUS = ROOT / 'results/tip_KKL_tree_marked_breakage_20261109.json'
RESULT = ROOT / 'results/issue40_native_attachment_edge_incidence_20261115.json'
UNIT = 1 << 256


def check(value: bool, why: str) -> None:
    if not value:
        raise AssertionError(why)


@dataclass(frozen=True)
class Ball:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        check(self.lo <= self.hi, 'inverted dyadic interval')

    @staticmethod
    def at(v: Q | int) -> 'Ball':
        n = Q(v) * UNIT
        return Ball(n.numerator // n.denominator,
                    -((-n.numerator) // n.denominator))

    def __add__(self, other: 'Ball') -> 'Ball':
        return Ball(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> 'Ball':
        return Ball(-self.hi, -self.lo)

    def square(self) -> 'Ball':
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        high = max(self.lo**2, self.hi**2)
        return Ball(low // UNIT, (high + UNIT - 1) // UNIT)

    def less(self, other: 'Ball') -> bool:
        return self.hi < other.lo

    def overlaps(self, other: 'Ball') -> bool:
        return self.lo <= other.hi and other.lo <= self.hi

    def middle(self) -> Q:
        return Q(self.lo + self.hi, 2 * UNIT)


# These are the physical *vertex* locations of KKL §2.5, not an
# independently chosen adjacency matrix.  They are evaluated from x_k.
TARGET_CUTS = ['x15', 'x9', 'x18', 'alpha', 'x12']
SOURCE_CUTS = ['-x12', 'x6', 'x15', '-alpha', 'x9', 'x18',
               'alpha', '-x15', '-x6', 'x12']
VERTICES = [('K2', 'x6', 'x15'), ('K0', 'x9', 'x18'),
            ('alpha', 'alpha', 'alpha'), ('K1', 'x12', 'x3')]
EDGES = [('E20', 'x15', 'x9'), ('E0a', 'x18', 'alpha'),
         ('Ea1', 'alpha', 'x12')]
TARGET_ATOM_TYPES = ['K2', 'E20', 'K0', 'E0a', 'Ea1',
                     'K1', 'Ea1', 'E0a', 'K0', 'E20']


def between(x: Ball, a: Ball, b: Ball) -> bool:
    return a.less(x) and x.less(b)


def class_at(x: Ball, coords: dict[str, Ball], *, source: bool) -> str:
    if source and between(x, coords['-x3'], coords['x6']):
        return 'attachment'
    for key, a, b in VERTICES:
        if a != b and between(x, coords[a], coords[b]):
            return key
    for key, a, b in EDGES:
        if between(x, coords[a], coords[b]):
            return key
    raise AssertionError('point not strictly in a physical vertex/edge/attachment interior')


def sample(s: int, cut: list[Ball], left: Ball, right: Ball) -> tuple[Q, int]:
    n = len(cut)
    if s == 0:
        return (left.middle() + cut[0].middle()) / 2, +1
    if s == n:
        return (cut[-1].middle() + right.middle()) / 2, +1
    j, side = (s, +1) if s < n else (2*n-s, -1)
    v = (cut[j-1].middle() + cut[j].middle()) / 2
    if abs(v) < Q(1, 10**6):
        v = (2*cut[j-1].middle() + cut[j].middle()) / 3
    return v, side


def label_at(value: Ball, side: int, cuts: list[Ball]) -> int:
    n = len(cuts)
    if value.less(cuts[0]):
        return 0
    if cuts[-1].less(value):
        return n
    for i in range(1, n):
        if between(value, cuts[i-1], cuts[i]):
            return i if side > 0 else 2*n-i
    raise AssertionError('atom image lies on/over cut: need tighter enclosure')


def endpoint(between_atoms: int, cuts: list[str]) -> dict:
    """Access at the joint of S[k-1] and S[k], k in Z/(2n)."""
    n = len(cuts)
    k = between_atoms % (2*n)
    # The two terminal T' tips occur INSIDE S0 and S10, not at marking
    # endpoints.  S19/S0 and S0/S1 are the lower/upper accesses at -x12;
    # S9/S10 and S10/S11 are the upper/lower accesses at x12.
    if k == 0:
        return {'landing': cuts[0], 'access': 'lower'}
    if 0 < k <= n:
        return {'landing': cuts[k-1], 'access': 'upper'}
    return {'landing': cuts[2*n-k], 'access': 'lower'}


def cyclic(start: int, count: int, n: int) -> list[int]:
    return [(start+i) % n for i in range(count)]


def det3(a: list[list[int]]) -> int:
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            - a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            + a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def mmul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def F_next(word: list[int] | None, blocks: list[list[int]], f_atom: list[int]) -> list[int] | None:
    """iota* first (concatenate genuine blocks), then f* as a circle cover.

    A projected word with >10 consecutive source atoms includes a full
    turn and its joining endpoints. Exactly 10 would miss a point and
    MUST NOT be mistaken for a closed saturated circle.
    """
    if word is None:
        return None
    joined = [s for i in word for s in blocks[i]]
    check(all((b-a) % 20 == 1 for a,b in zip(joined, joined[1:])),
          'iota* blocks did not join as one real source access')
    check(all(f_atom[b] == (f_atom[a]+1) % 10 for a,b in zip(joined, joined[1:])),
          'f* is not the degree-two monotone cyclic covering')
    return None if len(joined) > 10 else [f_atom[s] for s in joined]


def compute(phase_path: Path = PHASE, previous_path: Path = PREVIOUS) -> dict:
    base = json.loads(phase_path.read_text())
    old = json.loads(previous_path.read_text())
    par = base['parameter_bracket']
    check(par['denominator_power_of_two'] == 128 and
          par['upper_numerator']-par['lower_numerator'] == 1 and
          par['lower_numerator'] == -607918036626757496169199575185708826140,
          'tip parameter has changed; this audit must be redone')
    check('x18=-x9' in base['exact_orbit_relations'],
          'imported exact preperiodic relation absent')
    phase_rows = {v['physical_phase']: v for v in base['phase_intervals']}
    for i, title in [(0, '[x9,x18]'), (3, '[x12,x3]'), (6, '[x6,x15]')]:
        check(phase_rows[i]['coarse_phase'] == 0 and
              phase_rows[i]['exact_interval'] == title,
              'physical small Julia vertex cycle changed')
    den = 1 << 128
    c0 = Q(par['lower_numerator'], den)
    c1 = Q(par['upper_numerator'], den)
    c = Ball(Ball.at(c0).lo, Ball.at(c1).hi)
    orbit = [Ball.at(0)]
    for _ in range(18):
        orbit.append(orbit[-1].square() + c)
    d = {f'x{i}': orbit[i] for i in range(19)}
    def G(x: Ball) -> Ball:
        for _ in range(3):
            x = x.square() + c
        return x

    alpha_lo, alpha_hi = Ball.at(Q(3,32)), Ball.at(Q(1,10))
    check(alpha_lo.less(G(alpha_lo)) and G(alpha_hi).less(alpha_hi),
          'G(alpha)=alpha has no certified sign bracket')
    d['alpha'] = Ball(alpha_lo.lo, alpha_hi.hi)
    for k in ('x3','x6','x9','x12','x15','alpha'):
        d['-'+k] = -d[k]
    check(d['-x3'].less(d['-x12']) and d['-x12'].less(d['x6']) and
          d['x12'].less(d['x3']) and d['x3'].less(Ball.at(Q(1,4))),
          'attachment/domain-tip inequalities fail')
    # G'(x)=8x f(x) f^2(x); hence each open half of T' is strictly
    # monotone, including ALL subsegments, not merely the sample points.
    first = Ball(0, d['x3'].hi).square() + c
    second = first.square() + c
    check(first.hi < 0 < second.lo, 'physical branch monotonicity failed')
    # This gives uniqueness of the positive fixed point in the alpha bracket.
    # Orbit identities, evenness and G(alpha)=alpha fix EVERY source cut image.
    target_of_cut = ['x15','x9','x18','alpha','x12',
                     'x12','alpha','x18','x9','x15']
    for src, target in zip(SOURCE_CUTS, target_of_cut):
        check(G(d[src]).overlaps(d[target]), f'wrong image for {src} -> {target}')
    source_cuts = [d[k] for k in SOURCE_CUTS]
    target_cuts = [d[k] for k in TARGET_CUTS]
    check(all(x.less(y) for x,y in zip(source_cuts,source_cuts[1:])) and
          all(x.less(y) for x,y in zip(target_cuts,target_cuts[1:])),
          'native target or covering-source cut order failed')
    check(d['x9'].less(Ball.at(0)) and Ball.at(0).less(d['x18']) and
          d['x18'].overlaps(-d['x9']),
          'critical zero / preperiodic ±x9 identity failed')

    # Distinguish S_s (source marking) from P_i=iota*I_i (open blocks).
    f_atom, iota_atom, physical, output_region, source_rows = [],[],[],[],[]
    for s in range(20):
        value, side = sample(s,source_cuts,d['-x3'],d['x3'])
        box = Ball.at(value)
        a = class_at(box,d,source=True)
        y = G(box)
        b = class_at(y,d,source=False)
        f = label_at(y,side if value<0 else -side,target_cuts)
        p = 0 if box.less(d['x6']) else label_at(box,side,target_cuts)
        check(b == TARGET_ATOM_TYPES[f], 'f* physical region does not match target marking')
        physical.append(a)
        output_region.append(b)
        f_atom.append(f)
        iota_atom.append(p)
        source_rows.append({'atom':s,'physical_region':a,'cover_image_region':b,
                            'f_star_target_atom':f,'iota_pullback_host':p,
                            'attachment_side':a=='attachment'})
    check(f_atom == [i%10 for i in range(20)], 'physical f* labeling drift')
    check(iota_atom == old['source_inclusion_pullback_atom_map'],
          'old certified proper-path pullback labeling disagrees with physical check')
    blocks = []
    for i in range(10):
        idx = [s for s in range(20) if iota_atom[s] == i]
        start = next(s for s in idx if (s-1)%20 not in idx)
        block = cyclic(start,len(idx),20)
        check(block == cyclic(start,len(idx),20) and set(block)==set(idx),
              f'nonconnected iota* interval for I{i}')
        blocks.append(block)
    check(blocks == old['inner_pullback_blocks'], 'prior complete attachment census disagrees')
    check([len(x) for x in blocks] == [5,2,1,1,3,1,3,1,1,2],
          'native pullback interval lengths changed')
    check(sorted(sum(blocks,[])) == list(range(20)), 'pullback not disjoint/exhaustive')
    # P0 has the COMPLETE attached boundary: S19,S0,S1, with its two
    # original K2 end-sides S18 and S2.  No attachment birth at a cut.
    attachment = [s for s in range(20) if physical[s]=='attachment']
    check(attachment == [0,1,19] and blocks[0] == [18,19,0,1,2],
          'entire (not partial) attached boundary missing')
    check(all(physical[b[0]]!='attachment' and physical[b[-1]]!='attachment'
              for b in blocks), 'KKL end-properness failed')
    endpoint_rows = []
    for i,block in enumerate(blocks):
        ep1 = endpoint(block[0],SOURCE_CUTS)
        ep2 = endpoint((block[-1]+1)%20,SOURCE_CUTS)
        endpoint_rows.append({'target_atom':i,'open_source_atoms':block,
                              'closed_endpoint_accesses':[ep1,ep2],
                              'is_end_proper':True,
                              'is_proper':i!=0})
    check(endpoint_rows[0]['closed_endpoint_accesses'] == [
        {'landing':'x15','access':'lower'},
        {'landing':'x15','access':'upper'}],
        'root/outer endpoint access collision: physical x15 sides lost')
    check(endpoint_rows[4]['closed_endpoint_accesses'][-1] ==
          {'landing':'x12','access':'upper'} and
          endpoint_rows[5]['closed_endpoint_accesses'] == [
            {'landing':'x12','access':'upper'}, {'landing':'x12','access':'lower'}] and
          endpoint_rows[9]['closed_endpoint_accesses'][-1] ==
            {'landing':'x15','access':'lower'},
          'critical terminal tip was mistaken for a marking endpoint')

    # Each upper-side physical open cell corresponds to one real segment;
    # its lower-side mate is a second prime-end ACCESS, NOT a second edge.
    check(all(physical[s] == physical[20-s] and
              output_region[s] == output_region[20-s]
              for s in range(1,10)), 'upper/lower image symmetry failed')
    expected_carriers = ['attachment','K2','E20','K0','E0a','Ea1','K1']
    check(set(physical) == set(expected_carriers), 'unknown physical carrier region')
    edge_names = [e[0] for e in EDGES]
    segments_by_carrier = {key:[] for key in ['attachment']+edge_names}
    upper_real_cuts = ['-x3']+SOURCE_CUTS+['x3']
    for s in range(11):
        if physical[s] in segments_by_carrier:
            segments_by_carrier[physical[s]].append({
                'upper_source_atom':s, 'lower_source_atom':20-s if s else 0,
                'real_open_segment':[upper_real_cuts[s],upper_real_cuts[s+1]],
                'image_region':output_region[s],
                'target_atom':f_atom[s]})
    # Attachment physical cut -x12 separates preimage of K2 from the
    # NEW preimage of E20.  Its other preimage is in OLD edge Ea1.
    sheets = {edge:[] for edge in edge_names}
    for carrier,segs in segments_by_carrier.items():
        for entry in segs:
            if entry['image_region'] in sheets:
                sheets[entry['image_region']].append({
                    'carrier':carrier,'upper_atom':entry['upper_source_atom']})
    for edge in edge_names:
        check(len(sheets[edge]) == 2 and len({z['upper_atom'] for z in sheets[edge]}) == 2,
              f'incomplete or duplicated degree-two real sheet of {edge}')
    check(sheets['E20'] == [{'carrier':'attachment','upper_atom':1},
                            {'carrier':'Ea1','upper_atom':9}],
          'E20 must have exactly ONE new and ONE old edge sheet')
    traces = {edge:[x['image_region'] for x in segments_by_carrier[edge]]
              for edge in edge_names}
    check(traces == {'E20':['E0a','Ea1'],
                     'E0a':['Ea1'],
                     'Ea1':['E0a','K0','E20']},
          'source real edge-word verification failed')
    check(all(len(t) == len(set(t)) for t in
              ([v for v in word if v in edge_names] for word in traces.values())),
          'an edge is double-counted/backtracked within one monotone image')
    # M[out][in] counts physical old edge crossings, not two contour sides.
    M = [[sum(s['image_region']==out for s in segments_by_carrier[old_edge])
          for old_edge in edge_names] for out in edge_names]
    check(M == [[0,0,1],[1,0,1],[1,1,0]], 'derived core incidence mismatch')
    check(all(det3([[x*(i==j)-M[i][j] for j in range(3)] for i in range(3)])
              == x**3 - 2*x - 1 for x in [-2,-1,0,1,2,3]),
          'integer characteristic polynomial / matrix orientation wrong')
    fourth = M
    for _ in range(3):
        fourth = mmul(fourth,M)
    check(all(a>0 for row in fourth for a in row), 'M^4 is not primitive/positive')
    # The exact positive left eigenvector is (phi,1,phi), with phi^2=phi+1;
    # algebraic arithmetic, not a floating approximation.
    check([sum(M[i][j] * (1 if i==1 else 0) for i in range(3))
           for j in range(3)] == [1,0,1], 'matrix row convention mismatch')
    # Direct exact eigen-identity, reducing phi^2 to phi+1.
    # coefficients (constant,phi): for v=(phi,1,phi), M^T v = phi*v.
    v = [(0,1),(1,0),(0,1)]
    mtv = [tuple(sum(M[i][j]*v[i][k] for i in range(3)) for k in (0,1))
           for j in range(3)]
    # phi*v: phi*(a+b phi)=(b, a+b) after phi^2=phi+1
    phiv = [(b,a+b) for a,b in v]
    check(mtv == phiv and all(a>=0 and b>=0 and (a+b)>0 for a,b in v),
          'Perron edge weights are not verified exactly')

    interval_incidence = []
    for i,b in enumerate(blocks):
        carriers = sorted({physical[s] for s in b if physical[s] in edge_names},
                          key=edge_names.index)
        new_sheets = sorted({output_region[s] for s in b if physical[s]=='attachment'
                             and output_region[s] in edge_names}, key=edge_names.index)
        image = F_next([i],blocks,f_atom)
        check(image is not None, 'atomic F* interval unexpectedly saturated')
        interval_incidence.append({'target_atom':i,'source_atom_block':b,
            'old_tree_edge_sides':carriers,
            'new_attached_preimage_edge_sides':new_sheets,
            'F_star_target_atom_word':image,
            'F_star_image_edge_side_set':sorted({TARGET_ATOM_TYPES[s] for s in image
                                                  if TARGET_ATOM_TYPES[s] in edge_names},
                                                  key=edge_names.index)})
    # Adversarial boundary control: ten complete consecutive covering atoms
    # map to a punctured circle, not a closed saturated circle.  Eleven map
    # to the entire circle including the missing endpoint.
    half = F_next([2,3,4,5,6,7],blocks,f_atom)
    check(half is not None and len(half)==10 and half[0]==5 and half[-1]==4,
          'halfturn open/closed endpoint distinction has been lost')
    check(F_next([8,9,0,1,2],blocks,f_atom) is None,
          'eleven-atom proper saturation is lost')
    zero = [row['target_atom'] for row in interval_incidence
            if not row['old_tree_edge_sides']]
    check(zero == [0,2,5,8], 'some zero-old-edge native sector omitted')
    zero_source_old = [s for s in range(20) if physical[s] not in edge_names]
    check(zero_source_old == [0,1,2,5,10,15,18,19],
          'missed a zero-old-edge source sector (attachment is not an old edge)')
    zero_outputs = [s for s in range(20) if output_region[s] not in edge_names]
    check(zero_outputs == [0,2,5,8,10,12,15,18],
          'some zero-F-output-edge source atom omitted')
    escaped = []
    for crest in zero:
        current:list[int]|None = [crest]
        first_positive = None
        saturation = None
        stages = []
        for n in range(1,6):
            current = F_next(current,blocks,f_atom)
            stages.append({'step':n,'target_atoms':current if current is not None else 'whole_circle'})
            if first_positive is None and current is not None and any(
                    TARGET_ATOM_TYPES[x] in edge_names for x in current):
                first_positive=n
            if current is None:
                saturation=n
                break
        check(first_positive is not None and saturation is not None and saturation<=5,
              f'no finite zero-sector edge escape for target I{crest}')
        escaped.append({'crest_atom':crest,'first_old_edge_side_step':first_positive,
                        'first_circle_saturation_step':saturation,'F_star_stages':stages})
    check([(z['crest_atom'],z['first_old_edge_side_step'],z['first_circle_saturation_step'])
           for z in escaped] == [(0,1,2),(2,3,4),(5,2,3),(8,3,4)],
          'zero-edge escape/saturation drift')

    # Appendix A.1 Wave crest C=B\(E_- cup E_+) is CLOSED.  These are
    # candidate minimal 3-atom crest TYPES, not an enumeration of all actual
    # positive-width canonical laminations.  Wave geometry is not a matrix.
    wave_types = [{'crest_atom':i,'minimal_three_atom_base':[(i-1)%10,i,(i+1)%10],
         'crest_physical_region':TARGET_ATOM_TYPES[i],
         'old_edge_crest_mass':int(TARGET_ATOM_TYPES[i] in edge_names),
         'positive_old_edge_charge_required_for_edge_transfer':TARGET_ATOM_TYPES[i] in edge_names}
         for i in range(10)]
    check([row['crest_atom'] for row in wave_types if not
           row['positive_old_edge_charge_required_for_edge_transfer']] == zero,
          'Wave vertex/edge incidence mismatch')

    # Re-certify the earlier ACTUAL positive-width wave's entire disks/endpoint
    # ranges.  No sampled curves and no numerical logarithms.
    center,r0,r1 = Q(-9,64),Q(3,256),Q(1,64)
    check(r1>r0>0 and r1/r0==Q(4,3), 'wave is not a positive-width annulus')
    q0,q1 = center+r0,center+r1
    w0,w1 = center-r1,center-r0
    check(between(Ball.at(q0),d['x15'],d['-alpha']) and
          between(Ball.at(q1),d['x15'],d['-alpha']) and
          between(Ball.at(w0),d['-x12'],d['x6']) and
          between(Ball.at(w1),d['-x12'],d['x6']),
          'one extreme Wave leaf crosses the wrong gate')
    # Full outer disk: center is an actual point of the connected T' interval.
    check(between(Ball.at(center),d['-x3'],d['x3']),
          'disk center not in the central physical V3 component')
    mid,rad=(c0+c1)/2,(c1-c0)/2
    diskcenter,diskradius=center,r1
    for _ in range(3):
        diskradius=2*abs(diskcenter)*diskradius+diskradius**2+rad
        diskcenter=diskcenter**2+mid
    check(abs(diskcenter)+diskradius<Q(1,20) and
          Q(1,4)-abs(diskcenter)-diskradius>Q(1,5),
          'whole complex disk no longer certified in V3')
    check(old['marked_breakable_wave']['target_base_atoms']==[9,0,1] and
          old['marked_breakable_wave']['target_crest_atom']==0 and
          old['marked_breakable_wave']['two_pushed_crest_atoms']==[2,8],
          'original genuine marked Wave witness has changed')
    check(f_atom[5]==f_atom[15]==5 and f_atom[0]==f_atom[10]==0,
          'critical fold / two distinct terminal sources were conflated')
    check(f_atom[1]==1 and f_atom[19]==9 and
          iota_atom[1]==iota_atom[19]==0,
          'two real gate accesses wrongly glued under covering or inclusion')

    return {
      'schema_version':1,
      'scope':'physical degree-two G=f_c^3:V3->D(0,1/4), one-step actual KKL tree; no non-LC/canonical-psi generalization',
      'input_parameter_bracket':par,
      'precision_bits':256,
      'target_tree':'[x6,x3]',
      'source_tree':'[-x3,x3]',
      'new_attachment':'[-x3,x6)',
      'target_tree_vertices': [{'name':n,'left':a,'right':b} for n,a,b in VERTICES],
      'target_marked_tree_edges':[{'name':n,'left':a,'right':b} for n,a,b in EDGES],
      'target_atom_physical_regions':TARGET_ATOM_TYPES,
      'source_cut_locations_increasing':SOURCE_CUTS,
      'target_cut_locations_increasing':TARGET_CUTS,
      'ideal_boundary_types':{
          'target_inner':'one slit-tree Caratheodory prime-end circle, 10 marked open atoms',
          'source_inner':'one slit-preimage Caratheodory prime-end circle, 20 covering-marked open atoms',
          'target_outer':'one boundary circle, one whole-component marking atom',
          'source_outer':'one boundary circle, outer properness not inferred'},
      'cover_f_star_source_to_target_atom':f_atom,
      'immersion_iota_star_source_to_target_host':iota_atom,
      'source_atom_real_incidence':source_rows,
      'iota_star_open_and_closed_attachment_intervals':endpoint_rows,
      'new_attachment_source_boundary_atoms':[19,0,1],
      'new_attachment_two_distinct_gate_accesses':['S19 lower','S1 upper'],
      'source_upper_real_segments_by_carrier':segments_by_carrier,
      'full_two_sheet_preimages_of_each_marked_edge':sheets,
      'old_edge_forward_traversals_with_vertex_gaps':traces,
      'T_F_rows_output_columns_old_input':M,
      'T_F_characteristic_polynomial':'t^3-2*t-1=(t+1)*(t^2-t-1)',
      'T_F_primitive_positive_power':4,
      'T_F_exact_Perron_eigenvalue':'(1+sqrt(5))/2',
      'T_F_positive_left_edge_weights':['phi','1','phi'],
      'atomic_iota_pullback_and_F_star_incidence':interval_incidence,
      'zero_old_edge_target_crest_atoms':zero,
      'zero_old_edge_source_atoms':zero_source_old,
      'zero_f_output_edge_source_atoms':zero_outputs,
      'zero_old_edge_sector_dynamics':escaped,
      'minimal_three_atom_wave_crest_types_not_actual_wave_enumeration':wave_types,
      'existing_physical_Wave_witness':{
          'base_atoms':[9,0,1], 'closed_crest_atom':0,
          'width_from_analytic_rectangle':'log(4/3)/(2*pi)',
          'radius_ratio_exact':'4/3',
          'two_child_crest_atoms':[2,8],
          'old_tree_edge_mass_of_crest':0,
          'old_tree_edge_mass_of_each_pushed_child_crest':[0,0],
          'full_F_star_I0_contains_edge_sides':True,
          'first_failed_edge_transfer_hypothesis':'positive Wave width DOES NOT imply positive old-tree edge mass of its closed crest'},
      'proof_boundary':[
          'The integers certify strict orbit/vertex/cut/gate order, whole-disk bounds, complete physical segment and attachment incidence, and exact matrix arithmetic.',
          'The existing Misiurewicz dendrite/connected quadratic-like source and KKL Proposition 6.5 identify real slit sides with the actual ideal-boundary pullback; they are imported analytic results, not proved by this Python file.',
          'All ten three-atom entries are formal crest TYPES only; Appendix A.1 gives arbitrary laminations with closed crests, not a finite canonical Wave family. Their existence and widths are not deduced from this table.',
          'The actual positive-width witness is the earlier explicitly constructed concentric wave; its extremal rectangle width and path properness rely on analytic arguments.',
          'No arbitrary proper-path zero-sector escape, universal no-cancellation for analytic immersed lifts, higher iterates in a non-locally-connected model, or Issue #40 theorem is established.'
      ]}


def compact_result(full: dict) -> dict:
    """Small locked manifest AND a digest of every emitted source-incidence row.

    `compute` still recomputes, tests and prints the *entire* table; its exact
    canonical JSON hash prevents any unreported row silently drifting.
    """
    canonical = json.dumps(full,sort_keys=True,separators=(',',':')).encode()
    keys = (
        'schema_version','scope','input_parameter_bracket','precision_bits',
        'target_tree','source_tree','new_attachment',
        'target_tree_vertices','target_marked_tree_edges',
        'cover_f_star_source_to_target_atom',
        'immersion_iota_star_source_to_target_host',
        'new_attachment_source_boundary_atoms',
        'full_two_sheet_preimages_of_each_marked_edge',
        'old_edge_forward_traversals_with_vertex_gaps',
        'T_F_rows_output_columns_old_input',
        'T_F_characteristic_polynomial','T_F_primitive_positive_power',
        'T_F_exact_Perron_eigenvalue','T_F_positive_left_edge_weights',
        'zero_old_edge_target_crest_atoms','zero_old_edge_source_atoms',
        'zero_f_output_edge_source_atoms','existing_physical_Wave_witness',
        'proof_boundary'
    )
    result={k:full[k] for k in keys}
    result['all_full_source_incidence_sha256'] = hashlib.sha256(canonical).hexdigest()
    result['all_twenty_source_physical_regions']=[row['physical_region'] for row in
                 full['source_atom_real_incidence']]
    result['all_twenty_source_cover_image_regions']=[row['cover_image_region'] for row in
                 full['source_atom_real_incidence']]
    result['all_ten_iota_star_edge_incidence']=[{
        'old_tree_edge_sides':row['old_tree_edge_sides'],
        'new_attached_preimage_edge_sides':row['new_attached_preimage_edge_sides'],
        'F_star_image_edge_side_set':row['F_star_image_edge_side_set']}
        for row in full['atomic_iota_pullback_and_F_star_incidence']]
    result['all_ten_iota_star_source_blocks']=[x['open_source_atoms'] for x in
                  full['iota_star_open_and_closed_attachment_intervals']]
    result['all_ten_iota_star_closure_endpoints']=[x['closed_endpoint_accesses'] for x in
                  full['iota_star_open_and_closed_attachment_intervals']]
    result['all_ten_atomic_F_star_words']=[x['F_star_target_atom_word'] for x in
                  full['atomic_iota_pullback_and_F_star_incidence']]
    result['all_zero_edge_sector_escape_steps']=[{
        'crest':z['crest_atom'], 'first_edge':z['first_old_edge_side_step'],
        'saturation':z['first_circle_saturation_step']}
        for z in full['zero_old_edge_sector_dynamics']]
    return result


def adversarial() -> None:
    """Force known wrong hypotheses to fail; useful against manifest laundering."""
    check(endpoint(0,SOURCE_CUTS)=={'landing':'-x12','access':'lower'},
          'lower attachment entrance was replaced by the tip')
    check(endpoint(1,SOURCE_CUTS)=={'landing':'-x12','access':'upper'},
          'upper attachment entrance was replaced by the tip')
    check(endpoint(10,SOURCE_CUTS)=={'landing':'x12','access':'upper'} and
          endpoint(11,SOURCE_CUTS)=={'landing':'x12','access':'lower'},
          'K1 terminal atom incorrectly introduces a cut at x3')
    phase=json.loads(PHASE.read_text())
    previous=json.loads(PREVIOUS.read_text())
    tests=[('parameter changed',deepcopy(phase),deepcopy(previous)),
           ('phase vertex changed',deepcopy(phase),deepcopy(previous)),
           ('attachment atom omitted',deepcopy(phase),deepcopy(previous)),
           ('f/iota falsely conflated',deepcopy(phase),deepcopy(previous)),
           ('wave crest changed',deepcopy(phase),deepcopy(previous))]
    tests[0][1]['parameter_bracket']['upper_numerator'] += 1
    by_phase={x['physical_phase']:x for x in tests[1][1]['phase_intervals']}
    by_phase[6]['exact_interval']='[x6,x3]'
    tests[2][2]['inner_pullback_blocks'][0].remove(19)
    tests[3][2]['source_inclusion_pullback_atom_map'][1]=1
    tests[4][2]['marked_breakable_wave']['target_crest_atom']=1
    with TemporaryDirectory() as directory:
        a,b=Path(directory)/'phase.json',Path(directory)/'prior.json'
        for label,left,right in tests:
            a.write_text(json.dumps(left))
            b.write_text(json.dumps(right))
            try:
                compute(a,b)
            except AssertionError:
                pass
            else:
                raise AssertionError('wrong input incorrectly accepted: '+label)
    print('PASS: adversarial cut endpoints, halfturn, altered phase, missing attachment, switched f*/iota*, and false Wave crest')


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--phase',type=Path,default=PHASE)
    parser.add_argument('--previous',type=Path,default=PREVIOUS)
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--write-manifest',action='store_true')
    mode.add_argument('--check-manifest',action='store_true')
    mode.add_argument('--adversarial',action='store_true')
    args=parser.parse_args()
    if args.adversarial:
        adversarial()
        return
    value=compute(args.phase,args.previous)
    if args.write_manifest:
        RESULT.write_text(json.dumps(compact_result(value),sort_keys=True,indent=2)+'\n')
        print('WROTE',RESULT)
    elif args.check_manifest:
        check(json.loads(RESULT.read_text())==compact_result(value),'source-derived results manifest drift')
        print('PASS: actual single-attachment 10/20 prime-end sectors, 2 sheets per edge, T_F, 4 zero-old-edge sectors, closed Wave-crest incompatibility')
    else:
        print(json.dumps(value,sort_keys=True,indent=2))


if __name__=='__main__':
    main()
