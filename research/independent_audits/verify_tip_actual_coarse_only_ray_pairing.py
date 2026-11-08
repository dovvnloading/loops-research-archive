#!/usr/bin/env python3
"""Pure-rational audit of the actual 3/9 Misiurewicz precritical ray atlas.

The finite arithmetic certifies which 10-step inverse-ray angles pass the
source's genuine ambient f-alpha critical Y^6 face at two successive G=f^3
checkpoints. Classical landing, Jordan puzzle and Levin/straightening facts
are WRITTEN analytic inputs, not machine-verified by this file.

Run from repository root:
python research/independent_audits/verify_tip_actual_coarse_only_ray_pairing.py --check-manifest
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
import json
from pathlib import Path

RESULT = Path(__file__).resolve().parents[2] / 'results' / 'tip_actual_coarse_only_ray_pairing_20261107.json'
TWO = Q(2)
MOD1 = lambda q: q % 1

# These are exactly the four source-certified landing/escape intervals of
# the physical F=f critical Y^6, not an independently chosen symbolic gate.
F_Y6_SEAMS = tuple((Q(a, 192), Q(b, 192)) for a,b in
                 ((41,43), (53,55), (137,139), (149,151)))
# The source's G=f^3 ordinary depth-three central critical-puzzle face.
G_Y3_SEAMS = ((Q(5,24),Q(7,24)), (Q(17,24),Q(19,24)))
G_Y6_SEAMS = F_Y6_SEAMS

PARENT_TARGETS=(Q(228,511),Q(283,511))
P_L=Q(114,511); P_R=Q(397,511)
Q_L=Q(283,1022); Q_R=Q(739,1022)
A=Q(116791,523264);B=Q(144841,523264)
D=Q(378423,523264);E=Q(406473,523264)

KNOWN_OUTER = {
    'pL': (P_L,Q(5,7)), 'pR': (P_R,Q(2,7)),
    'qL': (Q_L,Q(11,14)), 'qR': (Q_R,Q(3,14)),
    'a':(A,Q(81,112)), 'b':(B,Q(87,112)),
    'd':(D,Q(25,112)), 'e':(E,Q(31,112)),
}

def in_seams(q:Q, seams=F_Y6_SEAMS)->bool:
    q = MOD1(q)
    return any(lo < q < hi for lo,hi in seams)


def exact_ambient_sieve() -> dict:
    universe=sorted({(t+k)/1024 for t in PARENT_TARGETS for k in range(1024)})
    assert len(universe)==2048
    by1=[x for x in universe if in_seams(x)]
    by2=[x for x in by1 if in_seams(8*x)]
    by3=[x for x in by2 if in_seams(64*x)]
    assert (len(by1),len(by2),len(by3))==(80,32,32)
    assert all(MOD1(1024*x) in PARENT_TARGETS for x in universe)
    assert all(x in by2 for x,_ in KNOWN_OUTER.values())
    assert len([x for x in by2 if x < Q(1,2)])==16
    assert len([x for x in by2 if x > Q(1,2)])==16
    return {'universe':universe,'first':by1,'full':by2,'third':by3}


def complete_internal_32()->list[Q]:
    parents=(Q(2,7),Q(5,7),Q(3,14),Q(11,14))
    ans=sorted({(a+k)/8 for a in parents for k in range(8)})
    assert len(ans)==32
    assert len({MOD1(8*q) for q in ans})==4
    assert all(MOD1(8*q) in parents for q in ans)
    return ans


def rank_correspondence(amb:list[Q],internal:list[Q])->dict[Q,Q]:
    ia=amb.index(P_L)
    iq=internal.index(Q(5,7))
    shift=(iq-ia)%32
    assert shift==16
    table={a:internal[(i+shift)%32] for i,a in enumerate(amb)}
    assert len(table)==32
    for a,q in KNOWN_OUTER.values(): assert table[a]==q
    # Nonvacuous: three G=f^3 returns transport every selected ray to one
    # of the FOUR source-labelled p/-p rays, which are also in this table.
    assert all(MOD1(512*a) in table and
               MOD1(8*table[a]) == table[MOD1(512*a)] for a in amb)
    # The one-G return identity also holds whenever its ambient image
    # happens itself to belong to the selected depth-ten fiber.
    for a in amb:
        if MOD1(8*a) in table:
            assert MOD1(2*table[a]) == table[MOD1(8*a)]
    return table


def phase_shifted_tuning(q:Q)->Q:
    """An independent exact substitution check; NOT used to prove landing.

    sigma(0)=011, sigma(1)=100 followed by discarding first two bits.
    All our q have eventually periodic binary expansions, hence rational.
    """
    seen:dict[Q,int]={}
    digits=[]
    r=q
    while r not in seen:
        seen[r]=len(digits)
        r*=2
        b=int(r)
        r-=b
        digits.append(b)
        assert len(digits)<64
    start=seen[r]
    pre=digits[:start]
    period=digits[start:]
    def word(seq):
        return ''.join('011' if b==0 else '100' for b in seq)
    pre_s=word(pre); cyc_s=word(period)
    result=Q(int(pre_s,2),2**len(pre_s)) if pre_s else Q(0)
    result+=Q(int(cyc_s,2),2**len(pre_s)*(2**len(cyc_s)-1))
    return MOD1(4*result)


def slit_sector(x:Q)->int:
    gap=Q(25,112) # one of the two actual internal critical-value rays /2
    return 0 if gap < x < gap+Q(1,2) else 1


def inverse_ray_pairs(pair:tuple[Q,...])->list[tuple[Q,...]]:
    """Quadratic inverse using the actual inner critical-value slit.

    At the unique critical value the two target rays' 4 lifts co-land.
    """
    tau=Q(25,56)
    if frozenset(pair)==frozenset((tau,1-tau)):
        return [tuple(sorted({z for x in pair for z in (x/2,(x+1)/2)}))]
    assert len(pair)==2, pair
    out=[]
    for sector in (0,1):
        lifts=[]
        for x in pair:
            choices=(x/2,(x+1)/2)
            admissible=[z for z in choices if slit_sector(z)==sector]
            assert len(admissible)==1,(pair,choices,sector)
            lifts.append(admissible[0])
        out.append(tuple(sorted(lifts)))
    return out


def complete_precritical_pairs(rank:dict[Q,Q])->list[dict]:
    inverse={value:key for key,value in rank.items()}
    assert len(inverse)==32
    out=[]
    for branch,pair in [('p',(Q(2,7),Q(5,7))),('-p',(Q(3,14),Q(11,14)))]:
        frontier=[pair]
        for level in range(3):
            frontier=[new for old in frontier for new in inverse_ray_pairs(old)]
            expected = 7 if (branch=='-p' and level==2) else 2**(level+1)
            assert len(frontier)==expected, (branch,level,len(frontier),expected)
        if branch=='p':assert len(frontier)==8
        else:assert len(frontier)==7
        for idx,p in enumerate(frontier):
            physical=tuple(sorted(inverse[q] for q in p))
            is_fine=frozenset(p).issubset({v for _,v in KNOWN_OUTER.values()})
            record={'branch':branch,'inverse_path_index':idx,
                    'inner_G_angle_pair_or_quartet':list(map(str,sorted(p))),
                    'ambient_f_angle_pair_or_quartet':list(map(str,physical)),
                    'ambient_523264_numerators':[int(x*523264) for x in physical],
                    'fine_K9_member':is_fine,'local_degree':len(p)//2}
            out.append(record)
    assert len(out)==15
    assert sum(len(p['ambient_f_angle_pair_or_quartet']) for p in out)==32
    assert Counter(p['local_degree'] for p in out)==Counter({1:14,2:1})
    assert sum(not p['fine_K9_member'] for p in out)==12
    assert sum(p['fine_K9_member'] for p in out)==3
    assert all(len(p['ambient_f_angle_pair_or_quartet'])==2 for p in out if not p['fine_K9_member'])
    flat={x for p in out for x in p['ambient_f_angle_pair_or_quartet']}
    assert len(flat)==32
    assert sorted(map(str,rank.keys()))==sorted(flat)
    return out


def alpha_depth3_chords()->list[tuple[Q,Q]]:
    cur=[(Q(1,3),Q(2,3))]
    for _ in range(3):
        cur=[child for p in cur for child in inverse_ray_pairs(p)]
    assert len(cur)==8 and all(len(p)==2 for p in cur)
    assert {frozenset(p) for p in cur}=={
        frozenset(map(Q,x)) for x in
        ((Q(1,3),Q(2,3)),(Q(1,6),Q(5,6)),(Q(5,12),Q(7,12)),
         (Q(1,12),Q(11,12)),(Q(7,24),Q(17,24)),
         (Q(5,24),Q(19,24)),(Q(11,24),Q(13,24)),(Q(1,24),Q(23,24)))}
    return cur


def face_signature(q:Q,chords:list[tuple[Q,Q]])->str:
    return ''.join('1' if min(p)<q<max(p) else '0' for p in chords)


def classify_original_G_faces(pairs:list[dict], rank:dict[Q,Q])->dict:
    chords=alpha_depth3_chords()
    faces=defaultdict(list)
    fine_signature=None
    for p in pairs:
        inner=[Q(x) for x in p['inner_G_angle_pair_or_quartet']]
        signatures={face_signature(q,chords) for q in inner}
        assert len(signatures)==1, (p,signatures)
        sig=signatures.pop()
        if p['fine_K9_member']:
            if fine_signature is None:fine_signature=sig
            assert sig==fine_signature
        else:assert sig!=fine_signature
        p['G_original_depth3_alpha_face_signature']=sig
        p['G_top_critical_Y3_face']=all(in_seams(q,G_Y3_SEAMS) for q in inner)
        p['G_first_child_Y6_face']=all(in_seams(q,G_Y6_SEAMS) for q in inner)
        assert p['G_top_critical_Y3_face']==p['fine_K9_member']
        assert p['G_first_child_Y6_face']==p['fine_K9_member']
        faces[sig].append(p)
    assert len(faces)==5
    coarse_counts=sorted(len(v) for key,v in faces.items() if key!=fine_signature)
    assert coarse_counts==[2,2,4,4]
    assert len(faces[fine_signature])==3
    return {'alpha_depth3_chords':[list(map(str,sorted(c))) for c in chords],
            'critical_face_signature':fine_signature,
            'original_G_depth3_faces':[
                 {'signature':key,'physical_point_count':len(v),
                  'fine_K9':key==fine_signature,
                  'ray_count':sum(len(p['ambient_f_angle_pair_or_quartet']) for p in v),
                  'pair_ids':[p['branch']+str(p['inverse_path_index']) for p in v]}
                 for key,v in sorted(faces.items())],
            'coarse_only_depth3_face_sizes':[2,2,4,4],
            'coarse_only_in_G_critical_top_Y3':0,
            'coarse_only_in_G_first_child_Y6':0,
            'fine_angles_in_G_first_child_Y6':8}


def compute()->dict:
    raw=exact_ambient_sieve()
    inner=complete_internal_32()
    rank=rank_correspondence(raw['full'],inner)
    tuned={q:phase_shifted_tuning(q) for q in inner}
    assert len(set(tuned.values()))==32
    assert all(tuned[q]==a for a,q in rank.items())
    pairs=complete_precritical_pairs(rank)
    faces=classify_original_G_faces(pairs,rank)
    return {'schema_version':1,
            'scope':'ACTUAL 3/9 tip, full 24 coarse-only ambient ray labels and original G alpha-depth3 puzzle faces; not KL O/xi/eta sheet functor',
            'exact_ambient_census':{'all_depth10_inverse_angles':2048,
                 'inside_source_F_Y6_critical_seams':len(raw['first']),
                 'inside_seams_after_two_G_checkpoints':len(raw['full']),
                 'inside_after_three_G_checkpoints':len(raw['third']),
                 'actual_source_F_Y6_seams':[list(map(str,s)) for s in F_Y6_SEAMS],
                 'complete_K3_ambient_angles':list(map(str,raw['full'])),
                 'complete_K3_ambient_523264_numerators':[int(523264*x) for x in raw['full']],
                 'fine_K9_ambient_angles':list(map(str,sorted(a for a,_ in KNOWN_OUTER.values()))),
                 'coarse_only_24_ambient_angles':list(map(str,sorted(set(raw['full'])-{a for a,_ in KNOWN_OUTER.values()})))},
            'Levin_cyclic_ranking':{'anchor_ambient':str(P_L),
                 'anchor_internal_G':str(Q(5,7)),
                 'shift_for_32_sorted_lists':16,
                 'coarse_internal_32':list(map(str,inner)),
                 'sorted_ambient_internal_pairs':[[str(a),str(rank[a])] for a in raw['full']],
                 'independent_phase_shifted_airplane_substitution_all_32_matches':True,
                 'substitution':{'0':'011','1':'100','discard_first_bits':2,
                                 'proof_use':'only an independent exact check, not a landing theorem'}},
            'complete_15_landing_points':pairs,
            'source_G_alpha_depth3_faces':faces,
            'source_inputs':['actual ambient f alpha-depth6 Y6 critical face sectors (November 6 atlas)',
                             'g3:f^3|Y6 central quadratic-like representative with filled K3',
                             'Levin real Misiurewicz p1/p2 and monotone angle semiconjugacy',
                             'G inner critical-value rays 25/56 and 31/56 from certified 8-ray ladder',
                             'analytic simple-branch ray inverse pairing, including critical fold'],
            'not_proved':['analytic source alpha-puzzle theorems and Levin map are imported',
                          'no KL canonical localization O/xi/eta cross-scale sheet functor',
                          'H1-H4 UPTCR MLC unchanged']}

def main():
    p=argparse.ArgumentParser()
    mode=p.add_mutually_exclusive_group()
    mode.add_argument('--write-manifest',action='store_true')
    mode.add_argument('--check-manifest',action='store_true')
    args=p.parse_args()
    text=json.dumps(compute(),indent=2,sort_keys=True)+'\n'
    if args.write_manifest:
        RESULT.parent.mkdir(parents=True,exist_ok=True)
        RESULT.write_text(text,encoding='utf-8')
        print('WROTE',RESULT)
    elif args.check_manifest:
        assert RESULT.read_text(encoding='utf-8')==text, 'manifest mismatch'
        print('PASS: full 32 ambient labels, 15 true landing classes, 12 coarse-only points, 5 genuine G alpha puzzle faces, independent tuning control')
    else:print(text,end='')

if __name__=='__main__':main()
