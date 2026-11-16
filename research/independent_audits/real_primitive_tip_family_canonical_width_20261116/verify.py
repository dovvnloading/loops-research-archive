#!/usr/bin/env python3
"""Independent exact interval audit of tip cuts, radial witnesses and upper envelopes.

IMPORTANT: This does NOT certify the supremal KKL Wave.  Exact arithmetic only:
all calculations use integer fixed-grid outward rounding, Fraction constants,
and analytic one-sided series remainders.  No mpmath, numpy, float, or imports
from another verifier.  The prior dyadic parameter packets are treated as
untrusted inputs and are re-certified by endpoint signs and full-hull derivative.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from math import isqrt, factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OLD = ROOT / 'research/independent_audits/real_primitive_tip_family_unconditional_20261116/results.json'
RESULT = HERE / 'results.json'
BITS = 512
S = 1 << BITS
MODEL_LO, MODEL_HI = Q(-1795, 1000), Q(-1785, 1000)


def need(test: bool, msg: str) -> None:
    if not test:
        raise AssertionError(msg)


def floorq(a: Q) -> int:
    return a.numerator // a.denominator


def ceilq(a: Q) -> int:
    return -floorq(-a)


@dataclass(frozen=True)
class Iv:
    lo: int
    hi: int

    def __post_init__(self):
        need(self.lo <= self.hi, 'inverted interval')

    @staticmethod
    def point(x: Q | int) -> 'Iv':
        t = Q(x) * S
        return Iv(floorq(t), ceilq(t))

    @staticmethod
    def hull(a: Q, b: Q) -> 'Iv':
        need(a <= b, 'inverted rational interval')
        return Iv(Iv.point(a).lo, Iv.point(b).hi)

    def __add__(self, other: 'Iv') -> 'Iv':
        return Iv(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> 'Iv':
        return Iv(-self.hi, -self.lo)

    def __sub__(self, other: 'Iv') -> 'Iv':
        return self + (-other)

    def __mul__(self, other: 'Iv') -> 'Iv':
        v = [i*j for i in (self.lo, self.hi) for j in (other.lo, other.hi)]
        return Iv(min(v) // S, -((-max(v)) // S))

    def square(self) -> 'Iv':
        lo = 0 if self.lo <= 0 <= self.hi else min(self.lo*self.lo, self.hi*self.hi)
        return Iv(lo // S, -((-max(self.lo*self.lo, self.hi*self.hi)) // S))

    def reciprocal(self) -> 'Iv':
        need(self.lo > 0, 'division by nonpositive interval')
        return Iv((S*S) // self.hi, -((-(S*S)) // self.lo))

    def __truediv__(self, other: 'Iv') -> 'Iv':
        return self * other.reciprocal()

    def sqrt(self) -> 'Iv':
        need(self.lo >= 0, 'square root of negative interval')
        a = isqrt(self.lo * S)
        b = isqrt(self.hi * S)
        return Iv(a, b + (b*b < self.hi*S))

    def lt(self, other: 'Iv') -> bool:
        return self.hi < other.lo

    def gt(self, other: 'Iv') -> bool:
        return self.lo > other.hi

    def positive(self) -> bool:
        return self.lo > 0

    def negative(self) -> bool:
        return self.hi < 0

    def abs_upper(self) -> Q:
        return Q(max(abs(self.lo), abs(self.hi)), S)

    def low(self) -> Q:
        return Q(self.lo, S)

    def high(self) -> Q:
        return Q(self.hi, S)

    def inside(self, a: Q, b: Q) -> bool:
        return Q(a) < self.low() and self.high() < Q(b)


ZERO, ONE, TWO = Iv.point(0), Iv.point(1), Iv.point(2)


def poly_orbit(c: Iv, n: int, derivative: bool = False) -> tuple[list[Iv], list[Iv]]:
    x, dx = [ZERO], [ZERO]
    for _ in range(n):
        if derivative:
            dx.append(TWO * x[-1] * dx[-1] + ONE)
        x.append(x[-1].square() + c)
    return x, dx


def model(t: Iv) -> tuple[list[Iv], list[Iv]]:
    return poly_orbit(t, 6, derivative=True)


def model_p(t: Iv) -> Iv:
    x, _ = model(t)
    return x[6] + x[3]


def isolate_model() -> tuple[Iv, list[Iv]]:
    a, b = MODEL_LO, MODEL_HI
    need(model_p(Iv.point(a)).negative() and model_p(Iv.point(b)).positive(), 'model root signs')
    # The whole model window is separated by subdivision: no interval hull
    # is allowed to conceal a derivative sign change.
    for j in range(64):
        l = MODEL_LO + (MODEL_HI-MODEL_LO)*Q(j, 64)
        u = MODEL_LO + (MODEL_HI-MODEL_LO)*Q(j+1, 64)
        _, d = model(Iv.hull(l, u))
        need((d[6]+d[3]).gt(Iv.point(8)), 'model P derivative <= 8')
    for _ in range(93):
        m = (a+b)/2
        v = model_p(Iv.point(m))
        need(v.positive() or v.negative(), 'model bisection ambiguous')
        if v.positive():
            b = m
        else:
            a = m
    t = Iv.hull(a, b)
    x, _ = model(t)
    need((x[6]+x[3]).lo <= 0 <= (x[6]+x[3]).hi, 'missing model tip identity')
    return t, x


def checked_packet(row: dict) -> tuple[int, Iv, list[Iv]]:
    p = row['p']
    need(type(p) is int and 3 <= p <= 12, 'unexpected period')
    pkt = row['parameter_bracket']
    need(pkt['denominator_power_of_two'] == 256, 'parameter precision drift')
    n, top = pkt['lower_numerator'], pkt['upper_numerator']
    need(type(n) is int and type(top) is int and top == n+1, 'nonadjacent dyadic bracket')
    a, b = Q(n, 2**256), Q(top, 2**256)
    xx, dx = poly_orbit(Iv.hull(a, b), 6*p, derivative=True)
    need((dx[6*p]+dx[3*p]).negative(), f'p={p}: nontransverse parameter')
    va, _ = poly_orbit(Iv.point(a), 6*p)
    vb, _ = poly_orbit(Iv.point(b), 6*p)
    need((va[6*p]+va[3*p]).positive() and (vb[6*p]+vb[3*p]).negative(),
         f'p={p}: root signs failed')
    need((xx[6*p]+xx[3*p]).lo <= 0 <= (xx[6*p]+xx[3*p]).hi, 'root identity interval')
    need(xx[1].negative() and all(xx[j].positive() for j in range(2,p+1)), 'outer itinerary')
    signs = (1,-1,-1,1,-1,1)
    for k,sign in enumerate(signs, 1):
        need(xx[k*p].positive() if sign==1 else xx[k*p].negative(), 'inner itinerary')
    cuts = [xx[2*p],xx[5*p],xx[3*p],ZERO,xx[6*p],xx[4*p],xx[p]]
    need(all(u.lt(v) for u,v in zip(cuts,cuts[1:])), 'target cut order')
    return p,Iv.hull(a,b),xx


def alpha_interval(p: int, c: Iv, x: list[Iv]) -> Iv:
    lo, hi = x[6*p].high(), x[4*p].low()
    need(lo < hi, 'fixed-point bracket empty')
    def f(z: Q) -> Iv:
        w=Iv.point(z)
        for _ in range(p):
            w=w.square()+c
        return w-Iv.point(z)
    need(f(lo).positive() and f(hi).negative(), 'fixed-point endpoint signs')
    # f^p is decreasing on (x_6p,x_4p) because f(z)<0, f^j(z)>0 for
    # 2<=j<p; confirm using whole real interval, not endpoint sampling.
    k = Iv.hull(lo,hi)
    for j in range(p):
        if j == 0:
            need(k.positive(), 'fixed branch not positive')
        elif j == 1:
            need(k.negative(), 'wrong first derivative factor')
        else:
            need(k.positive(), 'wrong later derivative factor')
        k=k.square()+c
    for _ in range(82):
        m=(lo+hi)/2
        fm=f(m)
        need(fm.positive() or fm.negative(), 'alpha bisection ambiguous')
        if fm.positive():lo=m
        else:hi=m
    return Iv.hull(lo,hi)


def atan_unit(x: Iv, terms: int = 190) -> Iv:
    """Alternating atan series, valid for 0 <= x <= 4/5; even truncation."""
    need(terms%2==0 and x.lo >= 0 and x.high() < Q(4,5), 'atan range')
    z=x.square()
    powx=x
    out=ZERO
    for n in range(terms):
        term=powx*Iv.point(Q(1,2*n+1))
        out=out+term if n%2==0 else out-term
        powx=powx*z
    # Next omitted term positive, geometric bound is conservative.
    bound=Q(4,5)**(2*terms+1)/Q(2*terms+1)
    return Iv(out.lo, out.hi + Iv.point(bound).hi)


def pi_interval() -> Iv:
    pi=Iv.point(16)*atan_unit(Iv.point(Q(1,5))) - Iv.point(4)*atan_unit(Iv.point(Q(1,239)))
    need(pi.inside(Q(314159,100000),Q(314160,100000)), 'Machin pi')
    return pi


def arccos_pos(v: Iv) -> Iv:
    """acos(v)=2 atan sqrt((1-v)/(1+v)), for 0<v<1."""
    need(v.positive() and v.lt(ONE), 'acos sign / range')
    root=((ONE-v)/(ONE+v)).sqrt()
    need(root.high() < Q(4,5), 'atan does not converge fast')
    return TWO*atan_unit(root)


def ln_unit(y: Iv, terms: int=180) -> Iv:
    """log(y) by atanh after range reduction: 1<=y<=4."""
    need(y.low() >= 1 and y.high() <= 4, 'log range reduction')
    t=(y-ONE)/(y+ONE)
    need(t.lo >= 0 and t.high() <= Q(3,5), 'log reduced argument')
    t2=t.square()
    powt=t
    z=ZERO
    for n in range(terms):
        z=z+powt*Iv.point(Q(2,2*n+1))
        powt=powt*t2
    bound=Q(2)*Q(3,5)**(2*terms+1)/(Q(2*terms+1)*(1-Q(3,5)**2))
    return Iv(z.lo,z.hi+Iv.point(bound).hi)


def log_iv(v: Iv) -> Iv:
    need(v.low()>=1, 'log of argument below one not supported')
    n=v.lo//S
    shift=max(0,n.bit_length()-1)
    # Choosing a smaller reduction factor accommodates a power-of-two crossing.
    if v.high()>2**(shift+1):
        shift=max(0,shift-1)
    need(v.high()<=4*2**shift, 'log reduction overflow')
    z=v/Iv.point(2**shift)
    return ln_unit(z)+Iv.point(shift)*ln_unit(Iv.point(2))


def sinh_iv(x: Iv, terms: int=49) -> Iv:
    need(x.lo >= 0 and x.high() < 4, 'sinh argument outside proven tail bound')
    y=ZERO
    t=x
    xsq=x.square()
    for n in range(terms):
        y=y+t
        t=t*xsq*Iv.point(Q(1,(2*n+2)*(2*n+3)))
    # Ratio of successive omitted terms <1/2 from this index onwards.
    tail=Q(2)*Q(4)**(2*terms+1)/Q(factorial(2*terms+1))
    return Iv(y.lo,y.hi+Iv.point(tail).hi)


def elliptic_factor(m: Iv) -> Iv:
    """2K(sqrt(m))/pi = sum (C(2n,n)/4^n)^2 m^n; 0<m<1."""
    need(m.positive() and m.lt(ONE), 'elliptic parameter')
    # Find a rational geometric majorant; no numerical convergence heuristic.
    cap=Q(ceilq(m.high()*1000),1000)
    need(cap<1, 'elliptic majorant not <1')
    n=60
    while cap**n/(1-cap) >= Q(1,10**18):
        n += 40
        need(n <= 5000, 'elliptic series exceeds hard cap')
    coeff=ONE
    power=ONE
    out=ZERO
    for j in range(n):
        out=out+coeff*power
        coeff=coeff*Iv.point(Q(2*j+1,2*j+2)**2)
        power=power*m
    return Iv(out.lo, out.hi+Iv.point(cap**n/(1-cap)).hi)


def upper_envelope_elliptic(k: Iv) -> Iv:
    need(k.positive() and k.lt(ONE), 'crossratio not in (0,1)')
    t=k.square()
    return elliptic_factor(t)/elliptic_factor(ONE-t)


def infinite_envelope_for_cuts(xp: Iv, x2: Iv, x5: Iv, x3: Iv) -> tuple[Iv,Iv,Iv,Iv]:
    """Upper bound from full lifted path family in C minus the real slit."""
    m=(x2+xp)/TWO
    r=(xp-x2)/TWO
    need(r.positive(), 'slit radius')
    near=(m-x5)/r
    far=(m-x3)/r
    need(near.gt(far) and far.positive() and near.lt(ONE), 'cut order in normalized slit')
    a=arccos_pos(near)  # smaller angular displacement from left slit end
    b=arccos_pos(far)
    need(a.positive() and a.lt(b), 'angular gate order')
    k=(b-a)/(b+a)
    return upper_envelope_elliptic(k),a,b,r


def bound_for_finite_disk(xp: Iv, x2: Iv, x5: Iv, x3: Iv, R: Q, pi: Iv) -> tuple[Iv,Iv,Iv]:
    """Geometric annular inner/outer comparisons for the full-lifted class.

    This is an upper *envelope* for admissible Wave families, not a certificate
    that all its paths pass KKL A.3.2 immersion restriction.
    """
    inf,a,b,r=infinite_envelope_for_cuts(xp,x2,x5,x3)
    m=(x2+xp)/TWO
    need(m.positive(), 'slit midpoint sign: abs case not covered')
    RR=Iv.point(R)
    need((RR-m).gt(r), 'no room for concentric Joukowski annulus')
    A=(RR-m)/r
    B=(RR+m)/r
    rho_low=A+(A.square()-ONE).sqrt()
    rho_high=B+(B.square()+ONE).sqrt()
    need(rho_low.gt(ONE) and rho_low.lt(rho_high), 'outer annular bounds')
    Llo=log_iv(rho_low)
    Lhi=log_iv(rho_high)
    need(Llo.positive() and Llo.lt(Lhi), 'strip heights wrong')
    def capacity(L: Iv) -> Iv:
        x=pi*(b-a)/(TWO*L)
        y=pi*(b+a)/(TWO*L)
        need(x.positive() and x.lt(y), 'sinh angle order')
        return upper_envelope_elliptic(sinh_iv(x)/sinh_iv(y))
    low=capacity(Llo)
    high=capacity(Lhi)
    need(low.lt(high) and high.high()<inf.high(), 'finite strip capacity monotonicity')
    return low, high, inf


def radial_data(p: int,c: Iv,x: list[Iv],alpha: Iv,pi: Iv) -> tuple[Iv, Iv, Iv]:
    """All circles in the exact orbit-defined gate, not its maximal-wave width."""
    xp,x2,x5,x3,x4=x[p],x[2*p],x[5*p],x[3*p],x[4*p]
    m=(x2+x5)/TWO
    rin=(x5-x2)/TWO
    rright=-alpha-m
    rleft=x4+m
    need(rin.positive() and rin.lt(rright) and rin.lt(rleft), 'radial gate empty')
    need(rright.lt(rleft) or rleft.lt(rright), 'radial active boundary not certified')
    rmax=rright if rright.lt(rleft) else rleft
    ratio=rmax/rin
    need(ratio.gt(ONE), 'radial ratio <=1')
    R=Q(1,4) if p==3 else Q(1,2**p)
    # All z in the entire largest closed gate disk: propagate a complex disk
    # centered on the real axis, with both parameter and orbit interval errors.
    d=m
    rr=Iv.point(rmax.high())
    for _ in range(p):
        rr=TWO*Iv.point(d.abs_upper())*rr+rr.square()
        d=d.square()+c
    margin=R-d.abs_upper()-rr.high()
    need(margin > R*Q(2,5), 'entire gate disk is not contained in U')
    # Real center connects to 0 inside the same component by first return order.
    need(m.negative() and (-(xp)).lt(m) and m.lt(ZERO), 'disk center not on central real branch')
    width=log_iv(ratio)/(TWO*pi)
    return ratio,width,Iv.point(margin)


def bracket_dec(x: Iv, decimals: int=7) -> list[int]:
    scale=10**decimals
    # Strict enclosing rational endpoints (with one integer unit guard).
    return [floorq(x.low()*scale)-1,ceilq(x.high()*scale)+1]


def certify_large_p(t: Iv, u: list[Iv]) -> dict:
    """Rational algebra for the O(4^-p) orbit-defined gate limit.

    Assumes the analytic ALL-P note's explicit bound |e|<=88q, |e_w|<=256q
    and all-p Rouché/real-cut theorem. The verifier checks every numeric
    inequality used in the derived constants; it does not formalize Rouche.
    """
    q=Q(1,4**13)
    e=lambda j: Q(88*(4**j-1),3)
    tau_error=(e(6)+e(3))/8
    need(tau_error == 15246, 'tau perturbation coefficient')
    _,du=model(Iv.hull(MODEL_LO,MODEL_HI))
    need(all(d.inside(-30,30) for d in du[:6]), 'model derivative bound failed')
    coeff={j:30*tau_error+e(j) for j in range(2,6)}
    a=(ONE-(ONE-Iv.point(4)*t).sqrt())/TWO
    need(a.inside(-1,Q(-4,5)), 'wrong negative fixed point')
    c_alpha=Q(5900)
    need(-Q(13,5)+256*q < -Q(5,2), 'fixed-point slope not separated')
    need(Q(88)*q < 1 and Q(140,3)*q < Q(3,5)*Q(1,2**13),
         'large-period full-gate disk margin not uniform')
    need(Q(88)*Q(2,5)+tau_error*Q(5,13)<c_alpha, 'fixed point perturbation constant')
    d=u[2]-u[5]
    right=Iv.point(2)*a+u[2]+u[5]
    left=-Iv.point(2)*u[4]-u[2]-u[5]
    need(d.inside(Q(3,20),Q(1)), 'model gate denominator bound')
    need(right.inside(Q(4,5),Q(1)) and left.inside(Q(4,5),Q(1)), 'model gate numerator bound')
    N_c=max(2*c_alpha+coeff[2]+coeff[5], 2*coeff[4]+coeff[2]+coeff[5])
    D_c=coeff[2]+coeff[5]
    need(d.low()-Q(D_c)*q>Q(13,100), 'physical denominator lower not certified')
    need(Q(4,5)-N_c*q>4*(d.high()+D_c*q), 'radial ratio >4 not certified')
    bound=(N_c+D_c)/(Q(13,100)*Q(3,20))
    need(bound<150_000_000, 'ratio perturbation coefficient drift')
    need(Q(150_000_000,24)<7_000_000, 'log/pi Lipschitz constant drift')
    return {'from_period':13, 'radius_ratio_difference_bound': '150000000*4^(-p)',
            'radial_width_difference_bound':'7000000*4^(-p)',
            'source_dependency': 'all_p NOTE.md equations (13)-(18) and strict cuts'}


def run(old: dict) -> dict:
    rows=old['periods']
    need(len(rows)==10 and [r['p'] for r in rows]==list(range(3,13)), 'finite periods changed')
    pi=pi_interval()
    t,u=isolate_model()
    a=(ONE-(ONE-Iv.point(4)*t).sqrt())/TWO
    D=u[2]-u[5]
    Nr=Iv.point(2)*a+u[2]+u[5]
    Nl=-Iv.point(2)*u[4]-u[2]-u[5]
    need(Nr.lt(Nl) and Nr.positive() and D.positive(), 'limit active radial gate')
    limit_ratio=Nr/D
    limit_radial=log_iv(limit_ratio)/(TWO*pi)
    # Geometric, no physical finite-radius cutoff: full lift class for C\[u1,u2].
    lim_full,_,_,_=infinite_envelope_for_cuts(-u[1],-u[2],-u[5],-u[3])
    need(lim_full.gt(limit_radial), 'lower witness exceeds full-family bound')
    cert=[]
    for row in rows:
        p,c,x=checked_packet(row)
        alpha=alpha_interval(p,c,x)
        ratio,radial,margin=radial_data(p,c,x,alpha,pi)
        disk_R=Q(1,4) if p==3 else Q(1,2**p)
        boundlo,boundhi,wholeinf=bound_for_finite_disk(x[p],x[2*p],x[5*p],x[3*p],disk_R,pi)
        need(radial.lt(boundhi), 'lower wave > upper full-path envelope')
        cert.append({'p':p,
                     'radial_ratio_1e-7_strict':bracket_dec(ratio),
                     'radial_wave_width_1e-7_strict':bracket_dec(radial),
                     'full_lift_path_width_upper_1e-7_strict':bracket_dec(boundhi),
                     'round_annular_full_path_lower_1e-7_strict':bracket_dec(boundlo),
                     'source_gate_disk_margin_over_R_gt_2_5':margin.low()>Q(2,5)*disk_R,
                     'NOT_a_canonical_width_certificate':True})
    return {'schema':'canonical-width-gap-audit/v1',
            'scope':'certified radial lower witnesses and full-lift extremal upper envelopes; maximal KKL Wave NOT computed',
            'arithmetic':'integer outward 2^-512; rational Taylor, hypergeometric and geometric remainders',
            'model_tau_star_1e-7_strict':bracket_dec(t),
            'model_limit_radial_ratio_1e-7_strict':bracket_dec(limit_ratio),
            'model_limit_radial_width_1e-7_strict':bracket_dec(limit_radial),
            'model_limit_full_path_upper_envelope_1e-7_strict':bracket_dec(lim_full),
            'large_p_radial_result':certify_large_p(t,u),
            'finite':cert}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='regenerate new-only results after review')
    args=parser.parse_args()
    # These old certificates are not trusted as theorems: all root inequalities
    # used below are independently recomputed from their dyadic packets.
    source=json.loads(OLD.read_text())
    data=run(source)
    rendered=json.dumps(data,sort_keys=True,indent=2,ensure_ascii=True)+'\n'
    if args.write:
        RESULT.write_text(rendered)
    else:
        need(RESULT.read_text()==rendered,'committed results drift (use --write intentionally)')
    print(rendered)


if __name__=='__main__':
    main()
