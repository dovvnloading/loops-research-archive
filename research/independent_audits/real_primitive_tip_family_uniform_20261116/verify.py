#!/usr/bin/env python3
"""Independent interval audit of the near--2 real primitive tip branch, p=3..8.

No imports from native_wave_transfer, manifests, floating point or third-party code.
The exact seed DECIMALS are only root locators: every reported conclusion is
rechecked with outward fixed-point intervals and strict sign predicates.
The verified finite marking is conditional on the cited slit/prime-end model.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RESULT = HERE / "results.json"
PREC = 384
S = 1 << PREC
SEEDS = {
    3: "-1.78651054454432475738526067347",
    4: "-1.94255417149476190531972855955",
    5: "-1.98552816970534881040825573056",
    6: "-1.99638251171841202795004968882",
    7: "-1.99909607830917598002359967041",
    8: "-1.99977407339705875086923341332",
}
EXPECTED_BLOCKS = [[18, 19, 0, 1, 2], [3, 4], [5], [6], [7, 8, 9],
                   [10], [11, 12, 13], [14], [15], [16, 17]]
EXPECTED_MATRIX = [[0, 0, 1], [1, 0, 1], [1, 1, 0]]


def demand(ok: bool, reason: str) -> None:
    if not ok:
        raise AssertionError(reason)


@dataclass(frozen=True)
class I:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        demand(self.lo <= self.hi, "inverted interval")

    @staticmethod
    def point(q: F | int) -> I:
        x = F(q) * S
        return I(x.numerator // x.denominator, -((-x.numerator) // x.denominator))

    @staticmethod
    def hull(lo: F, hi: F) -> I:
        demand(lo <= hi, "inverted rational hull")
        return I(I.point(lo).lo, I.point(hi).hi)

    def __add__(self, b: I) -> I:
        return I(self.lo + b.lo, self.hi + b.hi)

    def __neg__(self) -> I:
        return I(-self.hi, -self.lo)

    def __sub__(self, b: I) -> I:
        return self + -b

    def __mul__(self, b: I) -> I:
        products = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        a, z = min(products), max(products)
        return I(a // S, -((-z) // S))

    def square(self) -> I:
        values = (self.lo*self.lo, self.hi*self.hi)
        a = 0 if self.lo <= 0 <= self.hi else min(values)
        z = max(values)
        return I(a // S, -((-z) // S))

    def lt(self, b: I) -> bool:
        return self.hi < b.lo

    def contains(self, b: I) -> bool:
        return self.lo <= b.lo and b.hi <= self.hi

    def meets(self, b: I) -> bool:
        return self.lo <= b.hi and b.lo <= self.hi

    def mid(self) -> F:
        return F(self.lo + self.hi, 2*S)

    def abs_bound(self) -> F:
        return F(max(abs(self.lo), abs(self.hi)), S)

    def abs_lower(self) -> F:
        if self.lo > 0:
            return F(self.lo, S)
        if self.hi < 0:
            return F(-self.hi, S)
        return F(0)


def evaluate(c: I, n: int, derivative: bool = False) -> tuple[list[I], list[I]]:
    v, d = [I.point(0)], [I.point(0)]
    for _ in range(n):
        if derivative:
            d.append((I.point(2) * v[-1] * d[-1]) + I.point(1))
        v.append(v[-1].square() + c)
    return v, d


def polynomial(c: F, p: int) -> I:
    orbit, _ = evaluate(I.point(c), 6*p)
    return orbit[6*p] + orbit[3*p]


def isolate_parameter(p: int) -> tuple[F, F, I, list[I]]:
    # Seed is NOT an asserted root: sign, derivative and uniqueness are
    # checked on its full width with exact outward interval arithmetic.
    seed = F(SEEDS[p])
    a, b = seed - F(1, 10**28), seed + F(1, 10**28)
    full, der = evaluate(I.hull(a, b), 6*p, derivative=True)
    demand((der[6*p] + der[3*p]).hi < 0, f"p={p}: derivative is not strictly negative")
    demand(polynomial(a, p).lo > 0 and polynomial(b, p).hi < 0,
           f"p={p}: root seed fails exact bracketing")
    for _ in range(156):
        mid = (a+b)/2
        val = polynomial(mid, p)
        demand(val.lo > 0 or val.hi < 0, f"p={p}: interval sign not separated")
        if val.lo > 0:
            a = mid
        else:
            b = mid
    c = I.hull(a, b)
    x, _ = evaluate(c, 6*p)
    demand((x[6*p]+x[3*p]).meets(I.point(0)), "root identity not enclosed")
    return a, b, c, x


def iterate(z: I, c: I, p: int) -> I:
    for _ in range(p):
        z = z.square() + c
    return z


def isolate_alpha(c: I, p: int, low: I, high: I) -> I:
    a, b = F(low.hi, S), F(high.lo, S)
    demand(a < b, "alpha search interval inverted")
    demand(I.point(a).lt(iterate(I.point(a), c, p)), "alpha lower fixed sign")
    demand(iterate(I.point(b), c, p).lt(I.point(b)), "alpha upper fixed sign")
    for _ in range(165):
        m = (a+b)/2
        d = iterate(I.point(m), c, p) - I.point(m)
        demand(d.lo > 0 or d.hi < 0, "alpha sign ambiguous")
        if d.lo > 0:
            a = m
        else:
            b = m
    return I.hull(a, b)


def index_of(y: I, side: int, cuts: list[I]) -> int:
    n = len(cuts)
    if y.lt(cuts[0]):
        return 0
    if cuts[-1].lt(y):
        return n
    for j in range(1, n):
        if cuts[j-1].lt(y) and y.lt(cuts[j]):
            return j if side == 1 else 2*n-j
    raise AssertionError("point touches marking cut or unknown cell")


def sample(s: int, cuts: list[I], left: I, right: I) -> tuple[F, int]:
    n = len(cuts)
    if s == 0:
        a,b,side = left,cuts[0],1
    elif s == n:
        a,b,side = cuts[-1],right,1
    else:
        j,side = (s,1) if s < n else (2*n-s,-1)
        a,b=cuts[j-1],cuts[j]
    demand(a.lt(b), "empty atom")
    return (2*a.mid()+b.mid())/3,side


def blocks_of(labels: list[int]) -> list[list[int]]:
    out = []
    for j in range(10):
        starts = [s for s in range(20) if labels[s] == j and labels[(s-1)%20] != j]
        demand(len(starts) == 1, "disconnected immersion block")
        s = starts[0]
        chain = []
        while labels[s] == j:
            demand(len(chain) < 20, "unbounded block")
            chain.append(s)
            s = (s+1)%20
        out.append(chain)
    demand(sorted(sum(out, [])) == list(range(20)), "blocks do not partition")
    return out


def arc(a: int,b: int,n: int) -> list[int]:
    f, rev = (b-a)%n, (a-b)%n
    demand(f != rev, "ambiguous antipodal short arc")
    start,length=(a,f) if f < rev else (b,rev)
    return [(start+j)%n for j in range(length+1)]


def disk_image(center: F, radius: F, a: F, error: F, n: int) -> tuple[F,F]:
    for _ in range(n):
        radius=2*abs(center)*radius+radius*radius+error
        center=center*center+a
    return center,radius


def rouche(p: int, c: I, target: F) -> F:
    # Certified expansion f^p(z)=d+A z^2+E, for |z|=target.
    # Tail propagation encloses all powers >=4 by the maximum principle.
    d,A=I.point(0),I.point(0)
    tail=F(0)
    for k in range(1,p+1):
        tail=2*d.abs_bound()*tail+(A.abs_bound()*target*target+tail)**2
        A=I.point(1) if k==1 else I.point(2)*d*A
        d=d.square()+c
    margin=A.abs_lower()*target*target-d.abs_bound()-tail-target
    demand(d.abs_bound()<target and margin>0, f"p={p}: no strict Rouché margin")
    return F((margin.numerator << 64) // margin.denominator, 1 << 64)


def old_edge(y: I, edge: list[tuple[I,I]]) -> int | None:
    for k,(a,b) in enumerate(edge):
        if a.lt(y) and y.lt(b):
            return k
    return None


def invert_signed_source_cuts(p: int, c: I, x: list[I], alpha: I) -> tuple[list[I],list[I]]:
    # G is strictly monotone on each half, so these ten distinct exact
    # orbit-labelled preimages exhaust the source cuts (not a copied table).
    targets=[x[5*p],x[3*p],x[6*p],alpha,x[4*p]]
    source=[-x[4*p], x[2*p], x[5*p], -alpha, x[3*p],x[6*p],
            alpha,-x[5*p],-x[2*p],x[4*p]]
    demand(all(a.lt(b) for a,b in zip(source,source[1:])),"source cut order")
    demand(all(a.lt(b) for a,b in zip(targets,targets[1:])),"target cut order")
    # All individual preimage labels are checked by images (the evenness
    # of f^p gives two roots from each absolute location).
    expected=[targets[i] for i in (0,1,2,3,4,4,3,2,1,0)]
    for s,t in zip(source,expected):
        demand(iterate(s,c,p).meets(t), "named inverse cut polynomial check")
    return targets,source


def native(p: int) -> dict:
    a,b,c,x=isolate_parameter(p)
    zero=I.point(0)
    demand(x[1].hi<0 and all(x[j].lo>0 for j in range(2,p)), "outer primitive sign prefix")
    demand(x[p].lo>0, "physical return critical value not positive")
    # f^p has its single real critical turn on [-x_p,x_p].
    span=I(0,x[p].hi)
    for j in range(1,p):
        span=span.square()+c
        demand(span.hi<0 if j==1 else span.lo>0, "real first-return monotonicity")
    alpha=isolate_alpha(c,p,x[6*p],x[4*p])
    ordered=[x[2*p],x[5*p],x[3*p],zero,x[6*p],alpha,x[4*p],x[p]]
    demand(all(u.lt(v) for u,v in zip(ordered,ordered[1:])), "inner three-phase order")
    demand((-x[p]).lt(x[2*p]), "one attachment has positive length")
    target, source=invert_signed_source_cuts(p,c,x,alpha)
    # Inner Chebyshev map H=f^(3p): 0 -> -t -> t -> t, t>0.
    demand(x[3*p].hi<0 and x[6*p].lo>0 and
           (x[3*p]+x[6*p]).meets(zero) and
           iterate(x[6*p],c,3*p).meets(x[6*p]), "inner Chebyshev identity")
    # Full real phase intervals through f^j, with exact square enclosures.
    K=I(x[3*p].lo,x[6*p].hi)
    real_phases=[]
    for j in range(p):
        real_phases.append(K)
        K=K.square()+c
    for i in range(p):
        for j in range(i+1,p):
            demand(real_phases[i].lt(real_phases[j]) or real_phases[j].lt(real_phases[i]),
                   "nonprimitive/disjoint real phases fail")
    target_radius=F(1,4) if p==3 else F(1,2**p)
    domain_margin="imported_p3_degree_two"
    if p>=4:
        domain_margin=rouche(p,c,target_radius)
    demand(x[p].lt(I.point(target_radius)), "return critical value outside target")
    covering=[]; pulled=[]; attached=[]
    for s in range(20):
        real,side=sample(s,source,-x[p],x[p])
        y=I.point(real)
        mapped=side if real<0 else -side
        covering.append(index_of(iterate(y,c,p),mapped,target))
        isattached=y.lt(x[2*p])
        pulled.append(0 if isattached else index_of(y,side,target))
        if isattached:attached.append(s)
    bks=blocks_of(pulled)
    demand(bks==EXPECTED_BLOCKS, "immersion cyclic block drift")
    demand(covering==[s%10 for s in range(20)], "cover is not two-to-one")
    demand([s for s in bks[0] if s in attached]==[19,0,1] and len(attached)==3,
           "attachment side census drift")
    demand(all(z[0] not in attached and z[-1] not in attached for z in bks),
           "end-properness failed")
    # One physical edge per real segment; no doubling across slit sides.
    edges=[(x[5*p],x[3*p]),(x[6*p],alpha),(alpha,x[4*p])]
    endpoints=[(0,1),(2,3),(3,4)]
    image_label={0:2, 1:4, 2:4, 3:3,4:0}
    matrix=[[0]*3 for _ in range(3)]
    for col,(i,j) in enumerate(endpoints):
        demand(iterate(target[i],c,p).meets(target[image_label[i]]) and
               iterate(target[j],c,p).meets(target[image_label[j]]),
               "old edge endpoint identity")
        lo,hi=sorted((image_label[i],image_label[j]))
        for row,(u,v) in enumerate(endpoints):
            if lo<=u and v<=hi:
                matrix[row][col]+=1
    demand(matrix==EXPECTED_MATRIX, "old real edge matrix mismatch")
    # Exact left phi eigenvector: phi^2=phi+1, (phi,1,phi).
    weights=[(0,1),(1,0),(0,1)]
    for j in range(3):
        lhs=(sum(weights[k][0]*matrix[k][j] for k in range(3)),
             sum(weights[k][1]*matrix[k][j] for k in range(3)))
        aa,bb=weights[j]
        demand(lhs==(bb,aa+bb), "Perron eigenvector arithmetic")
    target_zero=[]
    for i in range(10):
        y,_=sample(i,target,x[2*p],x[p])
        if old_edge(I.point(y),edges) is None:target_zero.append(i)
    source_zero=[]
    for i in range(20):
        y,_=sample(i,source,-x[p],x[p])
        if old_edge(I.point(y),edges) is None:source_zero.append(i)
    pushed_zero=[i for i,t in enumerate(covering) if t in target_zero]
    demand(target_zero==[0,2,5,8] and source_zero==[0,1,2,5,10,15,18,19]
           and pushed_zero==[0,2,5,8,10,12,15,18],"zero-old-edge census")
    # A deliberately SELECTED annulus, NOT a dynamically canonical width.
    xp=x[p].mid()
    center=-F(3,4)*xp
    r0=xp/16
    r1=F(p-1,8*p)*xp
    ratio=r1/r0
    demand(ratio==F(2*(p-1),p), "ratio arithmetic")
    q=center+r1; crossing=center-r1; avoiding=-F(17,16)*xp
    qrange=I.hull(center+r0,center+r1)
    wrange=I.hull(center-r1,center-r0)
    demand(target[0].lt(qrange) and qrange.lt(-alpha), "wave right gate")
    demand((-x[p]).lt(wrange) and wrange.lt(x[2*p]), "wave attachment gate")
    demand(source[0].lt(wrange) and wrange.lt(source[1]), "wave source gate")
    demand(I.point(avoiding).lt(-x[p]), "avoiding path crosses source tip")
    demand(avoiding < q and abs(avoiding)<target_radius,
           "avoiding circle not in target disk")
    # A stronger primitive check: whole complex images f^j(D(0,R_p)),
    # not just pairwise-disjoint real phase intervals.
    c0=(a+b)/2; cr=(b-a)/2
    phase_disks=[(F(0),target_radius)]
    d,r=phase_disks[0]
    for j in range(1,p):
        d,r=disk_image(d,r,c0,cr,1)
        phase_disks.append((d,r))
    for i in range(p):
        for j in range(i+1,p):
            demand(abs(phase_disks[i][0]-phase_disks[j][0]) >
                   phase_disks[i][1]+phase_disks[j][1],
                   f"p={p}: complex primitive phase disks overlap")
    # Independent full complex DISK envelopes: no boundary-only sampling.
    for name,w in (("wave",crossing),("avoiding",avoiding)):
        ctr=(q+w)/2;radius=(q-w)/2
        demand((-x[p]).lt(I.point(ctr)) and I.point(ctr).lt(x[p]),
               "circle center not attached to central component")
        demand(abs(ctr)+radius < target_radius, "circle not within target U")
        dc,dr=disk_image(ctr,radius,c0,cr,p)
        demand(abs(dc)+dr<target_radius, f"p={p}: {name} full disk bound")
    qs=(index_of(I.point(q),1,source),index_of(I.point(q),-1,source))
    crossing_pairs=[(qs[0],index_of(I.point(crossing),1,source)),
                    (index_of(I.point(crossing),-1,source),qs[1])]
    avoiding_pairs=[qs]
    for pair in crossing_pairs+avoiding_pairs:
        u,v=pair
        demand(len(arc(u,v,20))>2 and pulled[u]!=pulled[v],
               "marked source proper restriction fails")
        demand(len(arc(covering[u],covering[v],10))>2,
               "short covering pushforward")
    demand(crossing_pairs==[(3,1),(19,17)] and avoiding_pairs==[(3,17)],
           "cross/avoid restrictions mismatch")
    # Must not conflate cover and immersion in pushforward.
    cpush=[(covering[u],covering[v]) for u,v in crossing_pairs]
    apush=[(covering[u],covering[v]) for u,v in avoiding_pairs]
    demand(cpush==[(3,1),(9,7)] and apush==[(3,7)],"cover path endpoints")
    base=arc(index_of(I.point(q),1,target),index_of(I.point(q),-1,target),10)
    child_bases=[arc(u,v,10) for u,v in cpush]
    demand(base==[9,0,1] and child_bases==[[1,2,3],[7,8,9]],"crest gate change")
    demand(base[1] in target_zero and all(t[1] in target_zero for t in child_bases),
           "positive old-edge crest")
    # Harmonic identity concerns exact *coefficients* of log(r1/r0)/pi.
    parent_coeff,child_coeff=F(1,2),F(1)
    demand(F(1,parent_coeff)==F(1,child_coeff)+F(1,child_coeff),
           "harmonic coefficient identity")
    # Cross-check root identity with the existing independent source brackets.
    if p==3:
        prior=json.loads((ROOT/"results/tip_root_interval_geometry.json").read_text())
        old=prior["parameter_bracket"]
    elif p==4:
        prior=json.loads((ROOT/"research/native_wave_transfer/physical_examples/primitive4_tip12_parameter.json").read_text())
        old=prior["parameter_bracket"]
    else:
        old=None
    if old is not None:
        L=old["lower_numerator"];U=old["upper_numerator"]
        old_den=2**old["denominator_power_of_two"]
        demand(F(L,old_den)<a and b<F(U,old_den),
               "root branch differs from pre-existing source certificate")
    # Frozen results intentionally keep only per-period witnesses; the
    # common tables below are reconstructed and asserted for EVERY period.
    power = 192
    scale = 1 << power
    lower = (a.numerator * scale) // a.denominator
    upper = -((-b.numerator * scale) // b.denominator)
    demand(upper-lower == 1, "reported dyadic bracket not adjacent")
    return {
        "p":p,
        "parameter_root_bracket":{"denominator_power_of_two":power,
                                  "lower_numerator":lower,
                                  "upper_numerator":upper,
                                  "unique_in_seed_window":True},
        "target_radius":str(target_radius),
        "central_degree_two":{"method":"prior_source_p3" if p==3 else "complex_Rouche",
                              "strict_margin_lower":None if p==3 else str(domain_margin)},
        "real_and_complex_primitive_phase_balls_disjoint":True,
        "selected_wave_ratio":str(ratio),
        "interval_checks": "PASS: orbit, source/target cuts, both actions, paths, edges, crests, disks",
    }


def run() -> dict:
    return {
        "schema":"real-primitive-tip-family-interval-audit/v1",
        "scope":"p=3..8 only; prime ends, complete Julia tree and extremal widths are analytic inputs",
        "arithmetic":"integer outward fixed-point intervals, 2^-384; seed signs + strictly negative derivative",
        "common_discrete_output_checked_each_period":{
            "target_cuts":["x5p","x3p","x6p","alpha","x4p"],
            "source_cuts":["-x4p","x2p","x5p","-alpha","x3p","x6p","alpha","-x5p","-x2p","x4p"],
            "source_atoms":20,"target_atoms":10,"outer_component_atom":1,
            "covering_f_star":[i%10 for i in range(20)],
            "immersion_iota_pullback_blocks":EXPECTED_BLOCKS,
            "attached_source_sides":[19,0,1],
            "proper_crossing_pairs":[[3,1],[19,17]],
            "proper_avoiding_pair":[3,17],
            "cover_pushed_crossing_pairs":[[3,1],[9,7]],
            "cover_pushed_avoiding_pair":[3,7],
            "old_edge_matrix_output_rows_input_cols":EXPECTED_MATRIX,
            "perron_root":"(1+sqrt(5))/2",
            "target_zero_edge_atoms":[0,2,5,8],
            "parent_crest":0,"child_crests":[2,8],
            "harmonic_width_coefficients":{"parent":"1/2","each_child":"1"},
        },
        "selected_wave_family":{"center_over_xp":"-3/4",
                                "r0_over_xp":"1/16","r1_over_xp":"(p-1)/(8p)",
                                "ratio":"2(p-1)/p (chosen, not canonical)",
                                "width_parent":"log(2-2/p)/(2*pi)",
                                "width_each_child":"log(2-2/p)/pi",
                                "limit":"log(2)/(2*pi)"},
        "results":[native(p) for p in range(3,9)],
        "uniform_theorem_status":"conditional finite combinatorial theorem; physical all-p realization open",
    }


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true",help="write canonical certificate after review")
    args=parser.parse_args()
    data=(json.dumps(run(),sort_keys=True,ensure_ascii=True,indent=2)+"\n").encode()
    if args.write:
        RESULT.write_bytes(data)
        print(f"WROTE {RESULT}")
    else:
        demand(RESULT.read_bytes()==data,"result JSON drift")
        print("PASS p=3..8: independent interval roots, geometry, 20/10, f*/iota*, 2/1, edges, crests and selected symbolic harmonic equality")


if __name__=="__main__":
    main()
