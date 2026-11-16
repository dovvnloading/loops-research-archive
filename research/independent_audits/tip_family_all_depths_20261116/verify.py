#!/usr/bin/env python3
"""One depth-three real tip: strict rational, outward 2**-512 arithmetic.

This checks a *single* (3,3,3) chart, not an arbitrary-depth theorem.
The prime-end, KKL, tuning, and extremal-width theorems are external.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from math import isqrt

S = 1 << 512
SEED = ('-1.7864402785935947468504588226965670222586957449493088602791560382493896109336918126725022579412611772294370905849655876540931823207741086406')
CHART = Q(1, 10**80)
PERIODS = (3, 9, 27)
RADII = (Q(1, 4), Q(1, 40), Q(1, 250))
ALPHA = Q('0.96330184473265205057708169965409871077592668579')
ALPHA_RADIUS = Q(1, 10**25)
REFERENCE_DEPTH2 = ('-1.78644152790551131044650403351222319790845429767665075050684504932925497511533947022164768894027532108442')
REFERENCE_DEPTH1 = ('-1.786510544544324757385260673471213673058457671889172800031923968334629798587697269507048968639156733')
BLOCKS = ((18, 19, 0, 1, 2), (3, 4), (5,), (6,), (7, 8, 9),
          (10,), (11, 12, 13), (14,), (15,), (16, 17))


def check(ok: bool, reason: str) -> None:
    if not ok:
        raise AssertionError(reason)


def floor(q: Q) -> int:
    return q.numerator // q.denominator


def ceil(q: Q) -> int:
    return -floor(-q)


def upper_product(a: int, b: int) -> int:
    check(a >= 0 and b >= 0, 'upper_product needs nonnegative inputs')
    return ceil(Q(a*b, S))


def scaled(z: int) -> Q:
    return Q(z, S)


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        check(self.lo <= self.hi, 'inverted interval')

    @staticmethod
    def point(q: Q | int | str) -> 'Interval':
        a = Q(q) * S
        return Interval(floor(a), ceil(a))

    @staticmethod
    def hull(lo: Q, hi: Q) -> 'Interval':
        check(lo <= hi, 'inverted hull')
        return Interval(floor(lo*S), ceil(hi*S))

    def __add__(self, other: 'Interval') -> 'Interval':
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> 'Interval':
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: 'Interval') -> 'Interval':
        return self + -other

    def __mul__(self, other: 'Interval') -> 'Interval':
        products = (self.lo*other.lo, self.lo*other.hi,
                    self.hi*other.lo, self.hi*other.hi)
        return Interval(min(products)//S, ceil(Q(max(products), S)))

    def square(self) -> 'Interval':
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        return Interval(low//S, ceil(Q(max(self.lo**2, self.hi**2), S)))

    def __truediv__(self, other: 'Interval') -> 'Interval':
        check(other.lo > 0 or other.hi < 0, 'divide by zero interval')
        inverse=Interval.hull(1/scaled(other.hi),1/scaled(other.lo))
        return self*inverse

    def abshi(self) -> int:
        return max(abs(self.lo), abs(self.hi))

    def abslo(self) -> int:
        if self.lo > 0:
            return self.lo
        if self.hi < 0:
            return -self.hi
        return 0

    def lt(self, b: 'Interval') -> bool:
        return self.hi < b.lo


def iterate(c: Interval, n: int) -> tuple[list[Interval], list[Interval], list[Interval]]:
    x, d, a = [Interval.point(0)], [Interval.point(0)], [Interval.point(0)]
    one, two = Interval.point(1), Interval.point(2)
    for j in range(n):
        d.append(two*x[j]*d[j] + one)
        a.append(one if j == 0 else two*x[j]*a[j])
        x.append(x[j].square() + c)
    return x, d, a


def errors(x: list[Interval], a: list[Interval], r: Q, n: int) -> list[int]:
    """Bound every holomorphic term beyond the quadratic, on the entire disk."""
    r2 = Interval.point(r*r).hi
    t = [0, 0]
    for j in range(1, n):
        v = upper_product(a[j].abshi(), r2) + t[-1]
        t.append(upper_product(2*x[j].abshi(), t[-1]) + upper_product(v, v))
    return t[:n+1]


def gap(x: list[Interval], a: list[Interval], n: int, r: Q) -> Q:
    t = errors(x, a, r, n)
    return scaled(a[n].abslo())*r*r - scaled(x[n].abshi()) - scaled(t[n]) - r


def upper_disk_image(x: list[Interval], start: int, length: int, delta: int) -> int:
    for j in range(start, start+length):
        delta = upper_product(2*x[j].abshi(), delta) + upper_product(delta, delta)
    return delta


def disjoint_phases(x: list[Interval], a: list[Interval], indices: list[int], r: Q) -> None:
    t = errors(x, a, r, max(indices) + 1)
    r2 = Interval.point(r*r).hi
    deviations = [Interval.point(r).hi if j == 0 else
                  upper_product(a[j].abshi(), r2) + t[j] for j in indices]
    for pos, i in enumerate(indices):
        for other in range(pos+1, len(indices)):
            j = indices[other]
            check((x[i]-x[j]).abslo() > deviations[pos]+deviations[other],
                  'overlapping phase disks')


def check_marked_tables(blocks: tuple[tuple[int, ...], ...] = BLOCKS) -> None:
    check(blocks == BLOCKS, 'immersion target partition changed')
    check(len(blocks) == 10 and blocks[0] == (18, 19, 0, 1, 2), 'attachment wrong')
    check(sorted(v for b in blocks for v in b) == list(range(20)), 'immersion partition wrong')
    cover = tuple(j % 10 for j in range(20))
    immerse = {j: i for i, b in enumerate(blocks) for j in b}
    check(all(cover.count(i) == 2 for i in range(10)), 'cover degree wrong')
    check(any(cover[j] != immerse[j] for j in range(20)), 'cover mistaken for immersion')
    pairs = ((3, 1), (19, 17), (3, 17))
    def span(u: int, v: int, N: int) -> int:
        return 1 + min((u-v) % N, (v-u) % N)
    check(tuple(span(u,v,20) for u,v in pairs) == (3, 3, 7), 'source spans wrong')
    check(tuple(span(cover[u],cover[v],10) for u,v in pairs) == (3, 3, 5),
          'cover spans wrong')
    check(all(immerse[u] != immerse[v] for u,v in pairs), 'proper immersion filter wrong')
    image_cuts = (2, 4, 4, 3, 0)
    edges = ((0,1), (2,3), (3,4))
    matrix = tuple(tuple(int(min(image_cuts[edges[j][0]],image_cuts[edges[j][1]]) <= s
                             and t <= max(image_cuts[edges[j][0]],image_cuts[edges[j][1]]))
                         for j in range(3)) for s,t in edges)
    check(matrix == ((0,0,1),(1,0,1),(1,1,0)), 'wrong edge matrix')


def real_connector(x: list[Interval], c: Interval, p: int, r: Q, count: int) -> None:
    """Real interval between 0 and all return centres maps into the central component."""
    M = max(x[j*p].abshi() for j in range(1, count+1))
    check(scaled(M) < r, 'outer real phase centre outside target')
    u = Interval(-M, M)
    for j in range(1, p):
        u = u.square() + c
        check((x[j].hi < 0 and u.hi < 0) or (x[j].lo > 0 and u.lo > 0),
              'real connector wrong branch')
    u = u.square() + c
    check(scaled(u.abshi()) < r, 'real connector return outside parent target')


def fixed_residual(c: Interval, a: Interval, u: Q, n: int) -> Interval:
    # z = -u/a_n; reciprocal is outward rounded and zero excluded.
    check(a.lo > 0 or a.hi < 0, 'vanishing quadratic coefficient')
    inv = Interval.hull(1/scaled(a.hi), 1/scaled(a.lo))
    z = -Interval.point(u)*inv
    for _ in range(n):
        z = z.square() + c
    return -(a*z) - Interval.point(u)



# Certified plane-slit upper-envelope arithmetic, adapted independently from
# the archived depth-two verifier (same outward rational Taylor/AGM method).
def qclip(z: Q, denominator: int=10**14, upward: bool=False) -> Q:
    return Q(ceil(z*denominator) if upward else floor(z*denominator), denominator)


def factorial(n: int) -> int:
    out=1
    for j in range(2,n+1):
        out*=j
    return out


def cos_bounds(t: Q, N: int=17) -> tuple[Q,Q]:
    check(0<=t<=2,'cos input outside controlled interval')
    term=Q(1)
    value=Q(1)
    for j in range(1,N+1):
        term=-term*t*t/Q((2*j-1)*(2*j))
        value+=term
    tail=t**(2*N+2)/factorial(2*N+2)
    return value-tail,value+tail


def acos_bounds(t: Interval) -> tuple[Q,Q]:
    check(0 < t.lo <= t.hi < S,'acos argument must lie in (0,1)')
    v_lo=qclip(scaled(t.lo))
    v_hi=qclip(scaled(t.hi),upward=True)
    lo,hi=Q(0),Q(2)
    for _ in range(36):
        mid=(lo+hi)/2
        below,above=cos_bounds(mid)
        if below>v_hi:
            lo=mid
        elif above<v_lo:
            hi=mid
        else:
            raise AssertionError('cos inversion interval unresolved')
    check(cos_bounds(lo)[0]>v_hi and cos_bounds(hi)[1]<v_lo,'acos enclosure not strict')
    return lo,hi


def sqrt_bounds(t: Q) -> tuple[Q,Q]:
    check(t>=0,'negative sqrt')
    N=10**26
    k=isqrt((t.numerator*N*N)//t.denominator)
    return Q(k,N),Q(k+1,N)


def agm_interval(t: Q) -> tuple[Q,Q]:
    check(0<t<=1,'invalid AGM argument')
    alo=ahi=Q(1)
    blo=bhi=t
    for _ in range(10):
        nl=(alo+blo)/2
        nh=(ahi+bhi)/2
        mlo=sqrt_bounds(alo*blo)[0]
        mhi=sqrt_bounds(ahi*bhi)[1]
        alo,ahi,blo,bhi=nl,nh,mlo,mhi
    check(blo<=ahi,'AGM inverse enclosure')
    return blo,ahi


def plane_sandwich_upper(y: list[Interval]) -> tuple[Q,Q]:
    """Full lifted-plane-slit upper width via Joukowski/AGM, theorem input."""
    mid=(y[2]+y[1])*Interval.point(Q(1,2))
    rad=(y[1]-y[2])*Interval.point(Q(1,2))
    a=acos_bounds((mid-y[5])/rad)
    b=acos_bounds((mid-y[3])/rad)
    check(0<a[0]<a[1]<b[0]<b[1]<2,'wrong prime-end cut angle order')
    klo=(b[0]-a[1])/(b[0]+a[1])
    khi=(b[1]-a[0])/(b[1]+a[0])
    check(0<klo<khi<1,'invalid elliptic ratio')
    slo=sqrt_bounds(1-khi*khi)[0]
    shi=sqrt_bounds(1-klo*klo)[1]
    top_lo,top_hi=agm_interval(klo)[0],agm_interval(khi)[1]
    bottom_lo,bottom_hi=agm_interval(slo)[0],agm_interval(shi)[1]
    return top_lo/bottom_hi,top_hi/bottom_lo


def verify(seed: str = SEED, chart: Q = CHART, blocks=BLOCKS) -> dict[str, Q]:
    check_marked_tables(blocks)
    s = Q(seed)
    c = Interval.hull(s-chart, s+chart)
    n = PERIODS[-1]
    x, dx, a = iterate(c, 6*n)
    deriv = dx[3*n] + dx[6*n]
    check(deriv.lo > 0 or deriv.hi < 0, 'nonmonotone root chart')
    l, _, _ = iterate(Interval.point(s-chart), 6*n)
    u, _, _ = iterate(Interval.point(s+chart), 6*n)
    lp, up = l[3*n]+l[6*n], u[3*n]+u[6*n]
    check((lp.hi < 0 and up.lo > 0) or (lp.lo > 0 and up.hi < 0),
          'no isolated depth-three tip')
    check(x[1].hi < 0 and all(x[j].lo > 0 for j in range(2, 4)),
          'outer primitive real prefix')
    check(a[3].hi < 0 and a[9].lo > 0 and a[27].hi < 0,
          'quadratic orientation / branch')
    check((a[27]*x[81]).lo > 0 and (a[27]*x[162]).hi < 0,
          'wrong last-tip preperiodic branch')
    # Signed kneading at the outer and middle returns, checked against the
    # two already audited *distinct* lower-level parameters (not against c itself).
    for p, base, steps in ((3, REFERENCE_DEPTH2, 54), (9, REFERENCE_DEPTH1, 18)):
        q = Q(base)
        reference, _, _ = iterate(Interval.hull(q-Q(1,10**75),q+Q(1,10**75)),steps)
        for j in range(1, steps+1):
            actual = a[p]*x[j*p]
            wanted = reference[j]
            check((actual.lo > 0 and wanted.lo > 0) or
                  (actual.hi < 0 and wanted.hi < 0),
                  'tuning kneading mismatch')
    for p, r in zip(PERIODS, RADII):
        check(scaled(x[p].abshi()) < r, 'return critical value outside target')
        check(gap(x,a,p,r) > 0, 'Rouche disk fails')
    # Two primitive multi-phase nests; both their complex disk images and
    # the real centre connectors must lie in the preceding central component.
    disjoint_phases(x, a, [0,1,2], RADII[0])
    disjoint_phases(x, a, [0,3,6], RADII[1])
    disjoint_phases(x, a, [0,9,18], RADII[2])
    for parent, child, return_period, repeats in ((0,1,3,3),(1,2,9,3)):
        R, r = RADII[parent], RADII[child]
        t = errors(x,a,r,return_period*(repeats-1))
        r2 = Interval.point(r*r).hi
        for j in range(repeats):
            i = j*return_period
            delta = Interval.point(r).hi if i == 0 else upper_product(a[i].abshi(),r2)+t[i]
            after = upper_disk_image(x, i, return_period, delta)
            check(scaled(x[i+return_period].abshi()+after)<R,
                  'complex child phase disk escapes parent target')
        real_connector(x,c,return_period,R,6*repeats)
    # Last-level real marked cuts and actual dividing fixed point.
    y = [Interval.point(0)] + [-(a[n]*x[j*n]) for j in range(1,7)]
    alpha = Interval.hull(ALPHA-ALPHA_RADIUS,ALPHA+ALPHA_RADIUS)
    check(fixed_residual(c,a[n],ALPHA-ALPHA_RADIUS,n).lo>0
          and fixed_residual(c,a[n],ALPHA+ALPHA_RADIUS,n).hi<0,
          'no marked fixed-point bracket')
    zero = Interval.point(0)
    o1 = [y[2],y[5],y[3],zero,y[6],alpha,y[4],y[1]]
    o2 = [-y[1],-y[4],y[2],y[5],-alpha,y[3],y[6],alpha,
          -y[5],-y[2],y[4],y[1]]
    check(all(u.lt(v) for u,v in zip(o1,o1[1:])), 'O1 cut order wrong')
    check(all(u.lt(v) for u,v in zip(o2,o2[1:])), 'O2 cut order wrong')
    # Degree-two final three-return with *independent* radius and margin.
    A = a[n]
    nearest = floor(Q(A.abslo()+A.abshi(),2*S)+Q(1,2))
    check(nearest > 0 and scaled(A.abslo()) > nearest - Q(1,2)
          and scaled(A.abshi()) < nearest + Q(1,2), 'invalid A rounding')
    r4 = Q(3, 10*nearest)
    g4 = gap(x,a,3*n,r4)
    check(scaled(A.abslo())*g4 > Q(1,8), 'third-return normalized Rouche gap fails')
    check(r4 < RADII[2] and scaled(x[3*n].abshi()) < r4,
          'third-return disk not embedded')
    disjoint_phases(x,a,[0,n,2*n],r4)
    t4=errors(x,a,r4,3*n)
    r4sq=Interval.point(r4*r4).hi
    for j in (1,2,3):
        dev=upper_product(a[j*n].abshi(),r4sq)+t4[j*n]
        check(scaled(x[j*n].abshi()+dev) < RADII[2],
              'third-return phase disk escapes innermost target')
    # The real fixed-point connector for the innermost central source.
    real_connector(x,c,n,RADII[2],6)
    # Full closed round gate: not a sampled-circle test.
    half = Interval.point(Q(1,2))
    center=(y[2]+y[5])*half
    inner=(y[5]-y[2])*half
    gplus=-alpha-center
    gminus=y[4]+center
    check(gplus.lt(gminus) and inner.lt(gplus), 'round gate missing')
    inv = Interval.hull(1/scaled(A.hi), 1/scaled(A.lo))
    zcenter=-center*inv
    dr=ceil(scaled(gplus.abshi())/scaled(A.abslo())*S)
    dev=dr
    z=zcenter
    for _ in range(n):
        dev=upper_product(2*z.abshi(),dev)+upper_product(dev,dev)
        z=z.square()+c
    check(scaled(z.abshi()+dev) < RADII[2], 'closed gate not in central return domain')
    check(zcenter.abshi() < x[n].abslo(), 'gate centre not in real central connector')
    # A rigorous *rational* lower bound of log(gplus/inner)/(2*pi).
    # log(u)=2 sum_{j>=0} v^(2j+1)/(2j+1), v=(u-1)/(u+1)>0.
    ratio=scaled(gplus.lo)/scaled(inner.hi)
    v=(ratio-1)/(ratio+1)
    check(v>0,'log ratio not >1')
    log_lower=2*sum((v**(2*j+1))/(2*j+1) for j in range(16))
    pi_upper=Q(22,7)  # classical Archimedean strict upper bound
    width_lower=log_lower/(2*pi_upper)
    check(width_lower>Q(1,4), 'third-level certified radial witness too narrow')
    plane_lo,plane_hi=plane_sandwich_upper(y)
    check(plane_hi<Q(31,40),'third-level plane-slit upper exceeds 0.775')
    check(width_lower<plane_lo,'upper/lower width envelopes inconsistent')
    return {'root_chart':chart, 'rouche1':gap(x,a,3,RADII[0]),
            'rouche2':gap(x,a,9,RADII[1]),
            'rouche3':gap(x,a,27,RADII[2]),
            'normalized_third':scaled(A.abslo())*g4,
            'radial_width_lower':width_lower,
            'plane_width_upper':plane_hi,
            'A27_lower':scaled(A.abslo())}


def main() -> None:
    r=verify()
    for k,v in r.items():
        direction = '<' if k == 'plane_width_upper' else '>'
        print(f'{k}: {direction} {float(v):.12g}  (strict rational bound)')
    print('PASS (3,3,3): unique root in rational chart, three degree-two returns,')
    print('separate terminal three-return, real KKL cuts and complete radial gate.')
    print('No assertion about arbitrary depths, uniform moduli or optimal width.')


if __name__=='__main__':
    main()

# End of independent depth-three interval certificate.
