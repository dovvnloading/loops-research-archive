#!/usr/bin/env python3
"""Depth-two real tip certificates. Python 3.12, integer/fraction arithmetic only.

Theorem imports (straightening, tuning, KKL, extremal length) are NOT
computer-proved here; NOTE.md records their use and the remaining gaps.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from math import isqrt

BITS = 512
S = 1 << BITS
SEEDS = {
    (3, 3): '-1.78644152790551131044650403351222319790845429767665075050684504932925497511533947022164768894027532108442',
    (3, 4): '-1.78921105996871074726352652434602925645322357166487958843433254518733523157732087568331186792219708235097',
    (3, 5): '-1.79002516526106961615589624562545550664406186804532170612169331046702406397585508642585225137915896316307',
    (4, 3): '-1.94255039418497097061094275976828922944296786565857110974326010023050893645448363905890806607143502513821',
    (4, 4): '-1.94270420172521125062973117920756695925838285258728871526698613843375296821569907267817489117062296343467',
    (4, 5): '-1.9427472085617538053719275020970711922038401186056671081983604075065269598212526502684810440365517288136',
    (5, 3): '-1.98552794754653622605105467669380990995582600193407438549368271706463257562377405800895436855792691545633',
    (5, 4): '-1.98553702124031319738507589429313609828856296362264016206121635703162689516940800126806124931985876243848',
    (5, 5): '-1.98553952938943928931884230147642390754961746722764387075165413761886580756463125103180646886503637390431',
}
REFERENCE_TIPS = {
    3: '-1.786510544544324757385260673471213673058457671889172800031923968334629798587697269507048968639156733',
    4: '-1.942554171494761905319728559547351970316877794253756256973061644721007908220533846556129430732097156',
    5: '-1.985528169705348810408255730556821748277263841949252553593917274749073066379677891609603820336856318',
}
ALPHAS = {
    (3, 3): '0.96310854612', (3, 4): '0.936827164304', (3, 5): '0.930580227423',
    (4, 3): '0.965408869553', (4, 4): '0.937102846742', (4, 5): '0.930544490132',
    (5, 3): '0.965885298013', (5, 4): '0.937148192205', (5, 5): '0.930532277472',
}
BLOCKS = ((18, 19, 0, 1, 2), (3, 4), (5,), (6,), (7, 8, 9),
          (10,), (11, 12, 13), (14,), (15,), (16, 17))
MATRIX = ((0, 0, 1), (1, 0, 1), (1, 1, 0))


def require(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)


def floor(q: Q) -> int:
    return q.numerator // q.denominator


def ceil(q: Q) -> int:
    return -floor(-q)


def frac(v: int) -> Q:
    return Q(v, S)


def upmul(a: int, b: int) -> int:
    """Nonnegative fixed-point multiplication, rounding UP."""
    require(a >= 0 and b >= 0, 'negative upper bound')
    return (a*b + S-1)//S


@dataclass(frozen=True)
class I:
    lo: int
    hi: int

    def __post_init__(self):
        require(self.lo <= self.hi, 'interval inverted')

    @classmethod
    def point(cls, q: Q | int | str) -> 'I':
        n = Q(q)*S
        return cls(floor(n), ceil(n))

    @classmethod
    def hull(cls, a: Q, b: Q) -> 'I':
        require(a <= b, 'hull order')
        return cls(floor(a*S), ceil(b*S))

    def __add__(self, b: 'I') -> 'I':
        return I(self.lo+b.lo, self.hi+b.hi)

    def __neg__(self) -> 'I':
        return I(-self.hi, -self.lo)

    def __sub__(self, b: 'I') -> 'I':
        return self + (-b)

    def __mul__(self, b: 'I') -> 'I':
        t = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        return I(min(t)//S, -((-max(t))//S))

    def square(self) -> 'I':
        mn = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        mx = max(self.lo**2, self.hi**2)
        return I(mn//S, (mx+S-1)//S)

    def reciprocal(self) -> 'I':
        require(self.lo > 0 or self.hi < 0, 'division by interval containing zero')
        return I.hull(1/frac(self.hi), 1/frac(self.lo))

    def __truediv__(self, b: 'I') -> 'I':
        return self*b.reciprocal()

    def abshi(self) -> int:
        return max(abs(self.lo), abs(self.hi))

    def abslo(self) -> int:
        return self.lo if self.lo > 0 else (-self.hi if self.hi < 0 else 0)

    def lt(self, other: 'I') -> bool:
        return self.hi < other.lo

    def mid(self) -> Q:
        return Q(self.lo+self.hi, 2*S)


def orbit(c: I, n: int) -> tuple[list[I], list[I], list[I]]:
    """Exact polynomial orbit, parameter derivative and quadratic coefficient."""
    x, dx, a = [I.point(0)], [I.point(0)], [I.point(0)]
    two, one = I.point(2), I.point(1)
    for j in range(n):
        dx.append(two*x[j]*dx[j]+one)
        x.append(x[j].square()+c)
        a.append(one if j == 0 else two*x[j]*a[j])
    return x, dx, a


def rem_bound(x: list[I], a: list[I], radius: Q, n: int) -> list[int]:
    """Full holomorphic error of f^j(z)=x_j+a_j z^2+E_j on |z|<=r.

    Exact induction: T_(j+1)=2|x_j|T_j+(|a_j|r^2+T_j)^2.
    All operations are upper-rounded, including r^2.
    """
    rr = I.point(radius*radius).hi
    T = [0, 0]
    for j in range(1, n):
        t = upmul(a[j].abshi(), rr) + T[-1]
        T.append(upmul(2*x[j].abshi(), T[-1]) + upmul(t, t))
    return T[:n+1]


def rouche_gap(x: list[I], a: list[I], n: int, radius: Q) -> Q:
    T = rem_bound(x, a, radius, n)
    return frac(a[n].abslo())*radius*radius - frac(x[n].abshi()) - frac(T[n]) - radius


def upper_disk_image(x: list[I], start: int, length: int, delta: int) -> int:
    """Upper radius image of disk centred at x_start under f^length."""
    D = delta
    for j in range(start, start+length):
        D = upmul(2*x[j].abshi(), D) + upmul(D, D)
    return D


def real_order(y: list[I], alpha: I) -> None:
    z=I.point(0)
    o1=[y[2],y[5],y[3],z,y[6],alpha,y[4],y[1]]
    require(all(a.lt(b) for a,b in zip(o1,o1[1:])), 'second-level O1')
    o2=[-y[1],-y[4],y[2],y[5],-alpha,y[3],y[6],alpha,-y[5],-y[2],y[4],y[1]]
    require(all(a.lt(b) for a,b in zip(o2,o2[1:])), 'second-level O2')


def proper_atom_tables(blocks=BLOCKS) -> None:
    flattened = [s for block in blocks for s in block]
    require(len(flattened)==20 and sorted(flattened)==list(range(20)), 'immersion not a partition')
    require(blocks[0]==(18,19,0,1,2), 'attachment block')
    require(len(blocks)==10 and blocks[4]==(7,8,9), 'immersion block changes')
    # The covering is f_*(S_s)=I_(s mod 10), NOT the immersion blocks.
    cover=tuple(s % 10 for s in range(20))
    require(all(cover.count(i)==2 for i in range(10)), 'degree-two covering')
    require(cover != tuple(i for i,b in enumerate(blocks) for s in b), 'identified cover and immersion')
    endpoints=((3,1),(19,17),(3,17))
    def shortspan(i,j,N):
        d=(j-i)%N
        return 1+min(d,N-d)
    require(tuple(shortspan(a,b,20) for a,b in endpoints)==(3,3,7), 'source path filters')
    require(tuple(shortspan(cover[a],cover[b],10) for a,b in endpoints)==(3,3,5), 'cover path filters')
    # Different pulled-back blocks at both ends: all three paths survive A.3.2.
    locate={v:i for i,b in enumerate(blocks) for v in b}
    require(all(locate[a]!=locate[b] for a,b in endpoints),'immersion collapsed proper child')
    old_edges=((0,1),(2,3),(3,4))  # cut-index endpoints of E0,E1,E2
    image_cuts=(2,4,4,3,0)       # images of cuts a,b,d,e,h
    computed=[[0]*3 for _ in range(3)]
    for j,(u,v) in enumerate(old_edges):
        left,right=sorted((image_cuts[u],image_cuts[v]))
        for i,(s,t) in enumerate(old_edges):
            computed[i][j]=int(left<=s and t<=right)
    require(tuple(tuple(row) for row in computed)==MATRIX, 'wrong edge occurrence matrix')
    # Crest I0 and intermediates I2,I8 have no old edges; I1 and I9 are
    # opposite accesses to one old edge E0, not separate physical edges.
    crest_carrier={0:None,1:0,2:None,8:None,9:0}
    require(crest_carrier[1]==crest_carrier[9] and all(crest_carrier[i] is None for i in (0,2,8)), 'crest sides')


def qclip(z: Q, denominator: int=10**14, upwards=False) -> Q:
    return Q(ceil(z*denominator) if upwards else floor(z*denominator),denominator)


def atan_inv_bounds(q: int, count=64) -> tuple[Q,Q]:
    t=Q(1,q)
    v=sum(((-1)**j)*t**(2*j+1)/Q(2*j+1) for j in range(count))
    tail=t**(2*count+1)/Q(2*count+1)
    return (v,v+tail) if count%2==0 else (v-tail,v)


def pi_bounds() -> tuple[Q,Q]:
    a,b=atan_inv_bounds(5),atan_inv_bounds(239)
    low=16*a[0]-4*b[1]
    high=16*a[1]-4*b[0]
    require(Q('3.1415926535897932384626') <low<high<Q('3.1415926535897932384627'), 'pi bound')
    return low,high


def log_bounds(t: Q) -> tuple[Q,Q]:
    """Rigorous positive log on a rational argument via atanh and a tail."""
    require(t>=1, 'log positive ratio required')
    z=(t-1)/(t+1)
    lo=qclip(z); hi=qclip(z,upwards=True)
    require(hi <1, 'atanh convergence')
    N=100
    # Atanh positive series; both truncated expressions bound below their logs.
    def subtotal(v):
        term=v; total=Q(0)
        for j in range(N):
            total+=term/Q(2*j+1)
            term*=v*v
        return 2*total
    low=subtotal(lo)
    upper=subtotal(hi)+2*hi**(2*N+1)/(Q(2*N+1)*(1-hi*hi))
    return low,upper


def cos_bounds(t: Q, N=17) -> tuple[Q,Q]:
    """Taylor remainder, all tested t in [0,2], no floating point."""
    require(0<=t<=2, 'cos chart out of range')
    acc=Q(1);term=Q(1)
    for k in range(1,N+1):
        term= -term*t*t/Q((2*k-1)*(2*k))
        acc+=term
    tail=t**(2*N+2)/Q(_factorial(2*N+2))
    return acc-tail,acc+tail


def _factorial(n):
    z=1
    for j in range(2,n+1):z*=j
    return z


def acos_bounds(t: I) -> tuple[Q,Q]:
    """Invert strictly decreasing cosine on (0,pi/2), outward."""
    require(0<t.lo<=t.hi<S, 'acos parameter outside (0,1)')
    xlo=qclip(frac(t.lo));xhi=qclip(frac(t.hi),upwards=True)
    lo,hi=Q(0),Q(2)
    for _ in range(36):
        mid=(lo+hi)/2
        cl,ch=cos_bounds(mid)
        if cl>xhi:
            lo=mid
        elif ch<xlo:
            hi=mid
        else:
            # A Taylor overlap is extremely narrow; 17 terms suffice for our chart.
            raise AssertionError('cosine Taylor precision insufficient')
    require(cos_bounds(lo)[0]>xhi and cos_bounds(hi)[1]<xlo, 'acos not outward')
    return lo,hi


def sqrt_bounds(t: Q) -> tuple[Q,Q]:
    require(t>=0,'negative square root')
    N=10**26
    k=isqrt((t.numerator*N*N)//t.denominator)
    return Q(k,N),Q(k+1,N)


def agm_interval(t: Q) -> tuple[Q,Q]:
    require(0<t<=1,'agm input')
    a_lo=a_hi=Q(1)
    b_lo=b_hi=t
    for _ in range(10):
        anew_lo=(a_lo+b_lo)/2
        anew_hi=(a_hi+b_hi)/2
        bnew_lo=sqrt_bounds(a_lo*b_lo)[0]
        bnew_hi=sqrt_bounds(a_hi*b_hi)[1]
        a_lo,a_hi,b_lo,b_hi=anew_lo,anew_hi,bnew_lo,bnew_hi
    require(b_lo<=a_hi,'agm outer enclosure')
    return b_lo,a_hi


def qplane_bounds(y: list[I]) -> tuple[Q,Q]:
    """Joukowski plane-slit lifted upper envelope K(k)/K(k')."""
    half=I.point(Q(1,2))
    m=(y[2]+y[1])*half
    r=(y[1]-y[2])*half
    a=acos_bounds((m-y[5])/r)
    b=acos_bounds((m-y[3])/r)
    require(0<a[0]<a[1]<b[0]<b[1]<2,'prime-end cuts/angles')
    k_lo=(b[0]-a[1])/(b[0]+a[1])
    k_hi=(b[1]-a[0])/(b[1]+a[0])
    require(0<k_lo<k_hi<1,'elliptic ratio')
    # AGM formula K(k)=pi/(2 AGM(1,sqrt(1-k^2))).
    slo=sqrt_bounds(1-k_hi*k_hi)[0]
    shi=sqrt_bounds(1-k_lo*k_lo)[1]
    numerator_low=agm_interval(k_lo)[0]
    numerator_high=agm_interval(k_hi)[1]
    denominator_low=agm_interval(slo)[0]
    denominator_high=agm_interval(shi)[1]
    return numerator_low/denominator_high, numerator_high/denominator_low


def five_digits(b: tuple[Q,Q]) -> tuple[int,int]:
    lo,hi=floor(b[0]*100000),ceil(b[1]*100000)
    require(0<hi-lo<=2,'width chart too broad')
    return lo,hi


def verify_case(p1: int,p2: int,seed: str | None=None, upper_blocks=BLOCKS):
    require(p1 in (3,4,5) and p2 in (3,4,5),'unsupported grid')
    proper_atom_tables(upper_blocks)
    n=p1*p2
    s=Q(seed if seed is not None else SEEDS[p1,p2]);h=Q(1,10**80)
    c=I.hull(s-h,s+h)
    x,dx,a=orbit(c,6*n)
    D=dx[3*n]+dx[6*n]
    require(D.lo>0 or D.hi<0, 'zero derivative: nonunique chart')
    left=I.point(s-h);right=I.point(s+h)
    xl,_,_=orbit(left,6*n);xr,_,_=orbit(right,6*n)
    pl=xl[3*n]+xl[6*n];pr=xr[3*n]+xr[6*n]
    require((pl.hi<0 and pr.lo>0) or (pl.lo>0 and pr.hi<0),'no isolated tip root')
    require(a[p1].hi<0 and a[n].lo>0,'quadratic orientations not primitive')
    require(x[1].hi<0 and all(x[j].lo>0 for j in range(2,p1+1)),
            'wrong outer primitive phase window')
    # First level chart: normalized G=f^p1 has the real Chebyshev prefix
    # - + ... + (and its critical value is not prescribed to equal c_p1).
    A1=a[p1]; tau1=A1*x[p1]
    require(I.point(-Q(5,2)).lt(tau1) and tau1.lt(I.point(-Q(7,4))), 'outer near -2 chart')
    require(all((A1*x[j*p1]).lo>0 for j in range(2,p2+1)), 'inner first-return prefix')
    # Exact infinite kneading identity: the two finite signs lists through
    # 6*p2 agree and become 3*p2-periodic thereafter by P=0.
    rseed=Q(REFERENCE_TIPS[p2]);rh=Q(1,10**75)
    reference,_,_=orbit(I.hull(rseed-rh,rseed+rh),6*p2)
    for j in range(1,6*p2+1):
        u=A1*x[j*p1];v=reference[j]
        require((u.lo>0 and v.lo>0) or (u.hi<0 and v.hi<0),
                'tuning kneading mismatch')
    y=[I.point(0)]+[-a[n]*x[j*n] for j in range(1,7)]
    # Reject the spurious period-three centre P=0: positive x3, negative x6
    # in the *quadratic-normalized* H=A_n f^n coordinates.
    require((a[n]*x[3*n]).lo>0 and (a[n]*x[6*n]).hi<0, 'wrong tip branch / period-three centre')
    radius1=Q(1,4) if p1==3 else Q(1,2**p1)
    radius2=Q(1,10*4**(p1-3)*(4 if p2==3 else 2**p2))
    gap1=rouche_gap(x,a,p1,radius1)
    gap2=rouche_gap(x,a,n,radius2)
    require(gap1>Q(1,1000) and gap2>Q(1,10000),'quadratic-like Rouché margin')
    require(frac(x[p1].abshi())<radius1 and frac(x[n].abshi())<radius2,'critical values outside')
    # Keep f^p1_* and all phase disks within its CENTRAL quadratic-like
    # preimage component, not merely in the target U1.
    t2=rem_bound(x,a,radius2,n)
    t1=rem_bound(x,a,radius1,p1)
    # Little Julia set phases must be primitive: whole complex phase disks
    # are strictly disjoint, a stronger test than comparing their centres.
    def phase_disjoint(indices, rad, T):
        rr=I.point(rad*rad).hi
        deviations=[I.point(rad).hi if j==0 else
                    upmul(a[j].abshi(),rr)+T[j] for j in indices]
        for i,j in enumerate(indices):
            for k in range(i+1,len(indices)):
                require((x[j]-x[indices[k]]).abslo()>deviations[i]+deviations[k],
                        'phase disks intersect: no certified primitivity')
    phase_disjoint(list(range(p1)),radius1,t1)
    phase_disjoint([j*p1 for j in range(p2)],radius2,t2)
    M=max(x[j*p1].abshi() for j in range(1,6*p2+1))
    require(frac(M)<radius1,'postcritical G1 orbit escapes U1')
    for j in range(p2):
        index=j*p1
        delta=(I.point(radius2).hi if j==0 else
               upmul(a[index].abshi(),I.point(radius2*radius2).hi)+t2[index])
        after=upper_disk_image(x,index,p1,delta)
        require(frac(x[index+p1].abshi()+after)<radius1,
                'phase disk not mapped into outer U1')
    # The real centre x_(j p1) lies in V1: G1 is monotone on each side
    # of zero throughout the interval connecting 0 to those centres.
    z=I(-M,M)
    for k in range(1,p1):
        z=z.square()+c
        require(z.hi<0 if k==1 else z.lo>0, 'earlier critical branch on real connector')
    require(all(frac(x[j*p1].abshi())<radius1 for j in range(1,6*p2+1)),
            'real orbit connectors outside U1')
    # For second-level KKL normalization u=-A_n z the leading coefficient
    # is -1 and the critical value is POSITIVE, restoring the source order.
    al=Q(ALPHAS[p1,p2]);rad=Q(1,10**10)
    alpha=I.hull(al-rad,al+rad)
    def fixed_residual(u: Q):
        start= -I.point(u)/a[n]
        z=start
        for _ in range(n):z=z.square()+c
        return -a[n]*z-I.point(u)
    require(fixed_residual(al-rad).lo>0 and fixed_residual(al+rad).hi<0,'fixed point bracket')
    real_order(y,alpha)
    # Real local critical orbit stays off 0 until return, hence H is
    # strictly decreasing on the positive half of [-y1,y1].
    zn=I(-x[n].abshi(),x[n].abshi())
    for j in range(1,n):
        zn=zn.square()+c
        require(x[j].lo>0 or x[j].hi<0, 'ambiguous precritical orbit sign')
        require(zn.lo>0 if x[j].lo>0 else zn.hi<0,'second real monotone branch')
    require(frac(max(y[1].abshi(),y[2].abshi())) < frac(a[n].abslo())*radius2,
            'second-level tree outside U2')
    # Extra KKL prerequisite: a proper degree-two third return of H,
    # using *all* higher Taylor terms up to 3n (not a cubic truncation).
    integer_A=floor(a[n].mid()+Q(1,2))
    r3=Q(3,10*integer_A)
    gap3=rouche_gap(x,a,3*n,r3)
    require(frac(a[n].abslo())*gap3 > Q(1,8), 'third-return Rouché/KKL gap')
    require(r3<radius2 and frac(x[3*n].abshi())<r3, 'third-return embedding')
    # Whole complex images of the third-return disk at times n and 2n
    # remain in U2. Their real orbit centres lie in the central V2, so
    # the connected complex images lie in V2, not merely in U2.
    tt=rem_bound(x,a,r3,3*n)
    rr3=I.point(r3*r3).hi
    phase_disjoint([0,n,2*n],r3,tt)
    for j in (1,2,3):
        dev=upmul(a[j*n].abshi(),rr3)+tt[j*n]
        require(frac(x[j*n].abshi()+dev)<radius2,
                'three-return intermediate disk escapes U2')
    require(frac(x[2*n].abshi())<frac(x[n].abslo()),
            'three-return phase center outside central V2 connector')
    # Lower A.1 Wave: the COMPLETE radial gate disk maps inside U2.
    half=I.point(Q(1,2))
    m=(y[2]+y[5])*half
    r0=(y[5]-y[2])*half
    rplus=-alpha-m
    rminus=y[4]+m
    require(rplus.hi<rminus.lo and r0.lt(rplus),'nonempty active radial gate')
    gate=rplus
    zcenter= -m/a[n]
    deltar=ceil(frac(gate.hi)/frac(a[n].lo)*S)
    z=zcenter;delta=deltar
    for _ in range(n):
        delta=upmul(2*z.abshi(),delta)+upmul(delta,delta)
        z=z.square()+c
    require(frac(z.abshi()+delta)<radius2,'whole gate disk escapes second U2')
    require(frac(zcenter.abshi())<frac(x[n].abslo()),'gate centre not in central V2')
    ratio_lo=frac(gate.lo)/frac(r0.hi)
    ratio_hi=frac(gate.hi)/frac(r0.lo)
    pi_lo,pi_hi=pi_bounds()
    Llo,Lhi=log_bounds(ratio_lo)[0],log_bounds(ratio_hi)[1]
    radial=(Llo/(2*pi_hi),Lhi/(2*pi_lo))
    qplane=qplane_bounds(y)
    require(radial[0]>Q(1,4),'radial witness degenerates')
    require(qplane[1]<Q(31,40),'plane-slit upper too broad')
    require(radial[1]<qplane[0],'inconsistent sandwich')
    return {
      'pair':(p1,p2), 'seed':s, 'root_chart_radius':h,
      'rouche1':gap1, 'rouche2':gap2, 'rouche3_normalized_lower':frac(a[n].abslo())*gap3,
      'radial':radial,'qplane':qplane,
      'radial5':five_digits(radial),'qplane5':five_digits(qplane),
      'outer_chart_tau1':(frac(tau1.lo),frac(tau1.hi)),
    }


def main():
    proper_atom_tables()
    print('p1 p2 | Rouché1 >, Rouché2 >, Rouché3*(A_n) > | W_rad and Q_plane (strict /100000)')
    for p1 in (3,4,5):
        for p2 in (3,4,5):
            rec=verify_case(p1,p2)
            a,b=rec['radial5'],rec['qplane5']
            gaps=tuple(floor(rec[key]*10**6) for key in
                       ('rouche1','rouche2','rouche3_normalized_lower'))
            print(f'{p1}  {p2}  | >{gaps[0]}, >{gaps[1]}, >{gaps[2]} / 10^6'
                  f' | ({a[0]},{a[1]}) and ({b[0]},{b[1]})')
    print('PASS: nine local uniqueness/degree-two/phase/Rouché and marked-width certificates.')


if __name__=='__main__':main()
