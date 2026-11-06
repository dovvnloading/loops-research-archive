#!/usr/bin/env python3
"""Exact native-boundary BRIDGE diagnostic: coupled circular-cover and collapse data.

This is a synthetic topological boundary certificate, NOT a native KKL
prime-end realization, polynomial, or proof of interval-growth for KKL.
All arithmetic uses integers/Fraction; target boundary circumference M=10,
source boundary circumference 2M=20.  Generated edge incidence is derived
from the SAME map used for interval dynamics rather than independently entered.

Execute in repository root after PR #38's checker is present:
  python research/independent_audits/verify_native_boundary_bridge.py --check-manifest
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from dataclasses import dataclass
from typing import Optional

@dataclass(frozen=True, order=True)
class Interval:
    start: int
    length: int

@dataclass(frozen=True)
class Contour:
    words: tuple[tuple[int, ...], ...]
    weights: tuple[int, ...]
    expansion: Q

    @property
    def m(self):
        return len(self.words)

    def validate(self):
        if len(self.weights) != self.m or self.expansion <= 1 or not any(self.weights):
            raise ValueError('Missing weights or strict expansion')
        word = tuple(v for w in self.words for v in w)
        if any(not w for w in self.words) or len(word) != 2*self.m:
            raise ValueError('Not a degree-two word')
        if any((word[j]+1)%self.m != word[(j+1)%len(word)] for j in range(len(word))):
            raise ValueError('Incorrect cyclic order')

    def image(self,i:Optional[Interval]):
        if i is None: return None
        letters = [v for j in range(i.length)
                     for v in self.words[(i.start+j)%self.m]]
        if len(letters) > self.m: return None
        return Interval(letters[0],len(letters))

    def mass(self,i:Interval):
        return sum(self.weights[(i.start+j)%self.m] for j in range(i.length))

def proper_orbit(c:Contour, start:Interval):
    seen=set();out=[];i=start
    while i is not None:
        if i in seen:raise AssertionError('Proper periodic state: '+str(i))
        seen.add(i);out.append(i);i=c.image(i)
    return out

M = 10
PHASE = 5
ATOMS = ('vertex', 'X', 'Y', 'vertex', 'Z', 'vertex', 'Z', 'vertex', 'Y', 'X')
EDGE_TYPES = ('X', 'Y', 'Z')
WEIGHTS = {'vertex': 0, 'X': 3, 'Y': 2, 'Z': 3}
LENGTHS = (1, 3, 1, 1, 2, 5, 2, 1, 1, 3)
CUMULATIVE = tuple(sum(LENGTHS[:i]) for i in range(M + 1))


def q0_on_fundamental(t: Q) -> Q:
    """Old boundary quotient with no flat fibers; q0(T_i)=i."""
    if not Q(0) <= t <= Q(2*M):
        raise ValueError('point outside the fundamental source interval')
    if t == 2*M:
        return Q(M)
    i = next(i for i in range(M) if CUMULATIVE[i] <= t < CUMULATIVE[i+1])
    return Q(i) + (t-Q(CUMULATIVE[i])) / Q(LENGTHS[i])


def q1_on_fundamental(t: Q) -> Q:
    """Same marking endpoints, but an interior fiber [9,10] over 11/2."""
    if not Q(0) <= t <= Q(2*M):
        raise ValueError('point outside the fundamental source interval')
    if Q(8) <= t <= Q(13):
        if t <= Q(9):
            return Q(5) + (t-Q(8))/2
        if t <= Q(10):
            return Q(11,2)
        return Q(11,2) + (t-Q(10))/6
    return q0_on_fundamental(t)


def q2_on_fundamental(t: Q) -> Q:
    """Negative control: a flat fiber at MARKED endpoint 5 changes the action."""
    if Q(8) <= t <= Q(9):
        return Q(5)
    if Q(9) < t <= Q(13):
        return Q(5) + (t-Q(9))/4
    return q0_on_fundamental(t)


def p_lift(t: Q) -> Q:
    """Degree-two covering R/(20Z)->R/(10Z) in unwrapped coordinates."""
    return t + Q(PHASE)


def boundary_words() -> tuple[tuple[int,...],...]:
    """Derive all target letters from p and the common inverse marking cuts."""
    assert CUMULATIVE[-1] == 2*M
    return tuple(tuple((PHASE + t) % M for t in range(CUMULATIVE[s], CUMULATIVE[s+1]))
                 for s in range(M))


def derived_matrix(words: tuple[tuple[int,...],...]):
    """Every source edge side of one type must have exactly the same typed row."""
    rows = {}
    source_counts = {}
    for s, typ in enumerate(ATOMS):
        if typ == 'vertex':
            continue
        row = tuple(sum(ATOMS[t] == dest for t in words[s]) for dest in EDGE_TYPES)
        if typ in rows and rows[typ] != row:
            raise AssertionError(f'Typed edge row inconsistency {typ}: {rows[typ]} vs {row}')
        rows[typ] = row
        source_counts[typ] = source_counts.get(typ, 0) + 1
    if set(rows) != set(EDGE_TYPES):
        raise AssertionError('Missing an edge type')
    return tuple(rows[typ] for typ in EDGE_TYPES), source_counts


def image_from_marking_endpoints(s: int, k: int):
    """Both q0 and q1 give exactly this image of (s,s+k)."""
    assert 0 <= s < M and 1 <= k <= M
    n = s+k
    hi = CUMULATIVE[n%M] + (n//M)*2*M
    lo = CUMULATIVE[s]
    length = hi-lo
    # An open source interval of length > M covers the entire target circle.
    return None if length > M else Interval((PHASE+lo)%M, length)


def check_both_boundary_maps():
    # Exact interpolation checks: endpoints, cyclic degrees and one flat fiber.
    for i, cut in enumerate(CUMULATIVE):
        assert q0_on_fundamental(Q(cut)) == Q(i)
        assert q1_on_fundamental(Q(cut)) == Q(i)
    # Any piecewise-linear map with nonnegative slopes between these knots
    # is monotone, and the endpoint increments prove degree one.
    k0 = sorted({Q(x) for x in CUMULATIVE})
    k1 = sorted(set(k0) | {Q(9),Q(10)})
    q0_slopes = tuple((q0_on_fundamental(y)-q0_on_fundamental(x))/(y-x)
                      for x,y in zip(k0,k0[1:]))
    q1_slopes = tuple((q1_on_fundamental(y)-q1_on_fundamental(x))/(y-x)
                      for x,y in zip(k1,k1[1:]))
    assert all(x>0 for x in q0_slopes)
    assert all(x>=0 for x in q1_slopes)
    flats = [(x,y) for x,y,sl in zip(k1,k1[1:],q1_slopes) if sl==0]
    assert flats == [(Q(9), Q(10))]
    assert q0_on_fundamental(Q(21,2))==Q(11,2)
    assert q1_on_fundamental(Q(9)) == q1_on_fundamental(Q(10)) == Q(11,2)
    assert q0_on_fundamental(Q(9))!=q0_on_fundamental(Q(10))
    # Marked-endpoint flat fibers cannot pass the unique-preimage condition:
    # q2^{-1}(5) contains [8,9], so q2^{-1}((5,6)) starts at 9, not 8.
    assert q2_on_fundamental(Q(8)) == q2_on_fundamental(Q(9)) == Q(5)
    assert q0_on_fundamental(Q(9)) > Q(5)
    assert p_lift(Q(2*M))-p_lift(Q(0))==Q(2*M) # degree 2 target turns
    assert q0_on_fundamental(Q(2*M))-q0_on_fundamental(Q(0))==Q(M)
    assert q1_on_fundamental(Q(2*M))-q1_on_fundamental(Q(0))==Q(M)
    return k0,k1,flats


def q_lift(fun, t: Q) -> Q:
    # Extend the degree-one monotone map by its exact deck relation.
    period = t // Q(2*M)
    base = t - Q(2*M)*period
    return fun(base) + Q(M)*period


def check_all_marked_preimages():
    # Evaluate q0 and q1 on EVERY knot and interior midpoint of their
    # combined rational piecewise-linear partition, over two turns. Because
    # both are monotone affine/constant on every such piece, these exact
    # observations plus singleton endpoint fibers determine the whole set
    # preimages of all marked open and closed arcs, not only test samples.
    fundamental = sorted(set(map(Q,CUMULATIVE)) | {Q(9),Q(10)})
    knots = sorted(set(fundamental) | {t+Q(2*M) for t in fundamental})
    probes = sorted(set(knots) | {(a+b)/2 for a,b in zip(knots,knots[1:])})
    checked = 0
    for start in range(M):
        for length in range(1,M+1):
            end = start+length
            cutend = CUMULATIVE[end%M]+Q(2*M)*(end//M)
            cutstart = CUMULATIVE[start]
            for t in probes:
                for fun in (q0_on_fundamental,q1_on_fundamental):
                    target = q_lift(fun,t)
                    # The two set-theoretic inverse statements are checked
                    # separately: strict (open) and weak (closed) membership.
                    assert (Q(start)<target<Q(end)) == (cutstart<t<cutend)
                    assert (Q(start)<=target<=Q(end)) == (cutstart<=t<=cutend)
                    checked += 2
    return {'states':M*M,'common_piecewise_linear_probes':len(probes),
            'open_and_closed_exact_membership_checks':checked}


def coherent_certificate():
    k0,k1,flats=check_both_boundary_maps()
    preimages=check_all_marked_preimages()
    words=boundary_words()
    # The original abstract positive example from PR #38 is now reconstructed
    # from a single p and common marking cuts rather than a free-floating word list.
    c=Contour(words=words,weights=tuple(WEIGHTS[t] for t in ATOMS),expansion=Q(3,2))
    c.validate()
    rows,source_counts=derived_matrix(words)
    # This expected fingerprint is an adversarial regression, not source input.
    assert rows==((0,1,1),(1,0,0),(1,1,0))
    w=tuple(WEIGHTS[t] for t in EDGE_TYPES)
    Aw=tuple(sum(row[j]*w[j] for j in range(3)) for row in rows)
    assert Aw==(5,3,5)
    assert all(Q(Aw[i])>=Q(3,2)*w[i] for i in range(3))
    for i in range(M):
        assert tuple(words[i]) == tuple((PHASE+CUMULATIVE[i]+j)%M for j in range(LENGTHS[i]))
    # Test all 100 possible old marked *proper* open intervals, including
    # the ten punctured-circle states of length M. The proof of equality
    # for all these states comes from identical integer endpoint preimages.
    states=[Interval(s,k) for s in range(M) for k in range(1,M+1)]
    for I in states:
        assert c.image(I)==image_from_marking_endpoints(I.start,I.length)
        orbit=proper_orbit(c,I)  # detects any proper periodic state
        assert len(orbit)<=2*M
        for J in orbit:
            nxt=c.image(J)
            if nxt is not None:
                assert nxt.length>=J.length
                assert c.mass(nxt)>=Q(3,2)*c.mass(J)
    assert c.image(None) is None
    # Derive (not input) the length from source cuts, and verify that the
    # words preserve cyclic order and make exactly two turns.
    assert sum(map(len,words)) == 2*M
    concatenation=[t for word in words for t in word]
    assert concatenation==[(PHASE+t)%M for t in range(2*M)]
    # The same 100 marked interval images arise from q0 and q1. Yet a
    # new 11/2 mark distinguishes them: q0^{-1}(11/2)={21/2}, whereas
    # q1^{-1}(11/2)=[9,10]. Their p-images are a singleton versus arc.
    new_point=q0_on_fundamental(Q(21,2))
    assert new_point==Q(11,2)
    assert (p_lift(Q(21,2))-M)==Q(11,2)
    assert p_lift(Q(9))-M==Q(4)
    assert p_lift(Q(10))-M==Q(5)
    # A deliberately inconsistent row must fail the same-word test.
    corrupt=list(words)
    corrupt[9]=(1,2,3)  # breaks cyclic order and typed row simultaneously
    try:
        wrong, _ = derived_matrix(tuple(corrupt))
    except AssertionError:
        pass
    else:
        raise AssertionError('Did not detect inconsistent source edge incidence')
    return {
      'scope':'Synthetic marked-circle / degree-two boundary-cover model; no KKL polynomial or native prime-end conjugacy claimed',
      'source_circumference':2*M,'target_circumference':M,
      'source_p_lift':'p(t)=t+5 mod 10, period 20 on source',
      'q_degrees':[1,1], 'p_degree':2,
      'marking_cuts':CUMULATIVE,
      'target_atom_types':ATOMS,
      'target_edge_types':EDGE_TYPES,
      'word_lengths':LENGTHS,
      'cover_derived_words':words,
      'edge_matrix_derived_from_same_words':rows,
      'edge_source_side_counts':source_counts,
      'edge_weight_vector':w,'A_times_w':Aw,'expansion_lower_bound':'3/2',
      'checked_proper_marked_interval_states':len(states),
      'exact_piecewise_linear_preimage_regression':preimages,
      'marked_open_and_closed_preimages_agree':'all interval endpoints are at integer marking cuts; neither q has a flat fiber over any integer',
      'full_circle_image':'full circle',
      'q0_flat_fibers':0,
      'q1_flat_fibers':len(flats),
      'q1_interior_flat_fiber_source_endpoints':['9','10'],
      'q1_flat_fiber_target':'11/2',
      'q0_inverse_11_2':'{21/2}',
      'q1_inverse_11_2':'[9,10]',
      'p_q0_inverse_11_2':'{11/2} mod 10',
      'p_q1_inverse_11_2':'[4,5] mod 10',
      'same_finite_interval_action_but_different_attached_fibers':True,
      'marked_endpoint_plateau_negative_control':{
         'flat_source_interval':'[8,9]',
         'target_endpoint':'5',
         'old_interval_5_image_source_length':5,
         'new_interval_5_image_source_length':4,
         'scope':'This alteration changes marked interval action; it is not part of the indistinguishable pair'},
      'corrupted_edge_row_detected':True,
    }


def check_exception_window():
    # Native analytic content is NOT checked. Pure arithmetic corollary of
    # KKL 4.8 (limb length <=6b) and 6.7 (proper for b..q-b-2).
    for b in range(1,51):
        for q in range(2,201):
            exceptional=set(range(q)) - set(range(b,q-b-1)) if q>=2*b+2 else set(range(q))
            assert len(exceptional)<=min(q,2*b+1)
            assert len(exceptional)*6*b<=6*b*(2*b+1)
    return {'parabolic_b_tested':[1,50],'rotation_q_tested':[2,200],
            'excluded_limb_count_upper_bound':'min(q,2b+1)',
            'excluded_marking_atom_upper_bound':'6b min(q,2b+1) <= 6b(2b+1)',
            'source_dependencies':'KKL Lemma 4.8 and Proposition 6.7 (native hypotheses only)',
            'claim_boundary':'Bound on one-step exceptional locus, not iterate horizon or protected-lift realization'}


def manifest():
    return {
      'schema_version':1,
      'date':'2026-11-06',
      'target':'KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR',
      'status':'finite boundary interface coherence and nonidentifiability; native prime-end bridge open',
      'ledger_status_changes':[],
      'coupled_boundary':coherent_certificate(),
      'native_corridor_counting_consequence':check_exception_window(),
      'trust_boundary':'Proofs are exact finite/topological lemmas. No certification of the native KKL immersed prime-end maps, analytic forest, or MLC.'
    }


def main():
    arg=argparse.ArgumentParser(description=__doc__)
    g=arg.add_mutually_exclusive_group()
    g.add_argument('--write-manifest',action='store_true')
    g.add_argument('--check-manifest',action='store_true')
    arg.add_argument('--manifest',type=Path,
         default=Path(__file__).resolve().parents[2]/'results'/'native_boundary_bridge_20261106.json')
    a=arg.parse_args()
    text=json.dumps(manifest(),sort_keys=True,indent=2)+'\n'
    if a.write_manifest:
        a.manifest.parent.mkdir(parents=True,exist_ok=True)
        a.manifest.write_text(text,encoding='utf-8')
    if a.check_manifest:
        if not a.manifest.is_file():raise SystemExit('Missing manifest')
        if a.manifest.read_text(encoding='utf-8')!=text:raise SystemExit('Manifest mismatch')
    print('native boundary bridge: exact checks passed; '+str(len(text))+' manifest bytes')

if __name__=='__main__':main()
