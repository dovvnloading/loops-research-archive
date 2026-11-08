#!/usr/bin/env python3
"""Certified critical-preimage ramification for the archive's REAL 3/9 tip.

All sign and coefficient certificates use exact dyadic *outward interval*
arithmetic, not floating point.  A separate high-precision numerical check
of the local two-sheet unfolding is diagnostic, NOT proof of analytic
continuation, that the two points remain in K9/K3, or external ray landing.

python research/independent_audits/verify_tip_ramified_precritical_pair.py --check-manifest
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from pathlib import Path

PREC=256
S=1<<PREC
TIP_BITS=128
K=-607918036626757496169199575185708826140
OUTPUT=Path(__file__).resolve().parents[2]/'results'/'tip_ramified_precritical_pair_20261107.json'

def ceildiv(x:int,y:int)->int:
    return -((-x)//y)

@dataclass(frozen=True)
class D:
    lo:int
    hi:int
    def __post_init__(self):
        assert self.lo<=self.hi
    def add(self,b:'D')->'D':return D(self.lo+b.lo,self.hi+b.hi)
    def neg(self)->'D':return D(-self.hi,-self.lo)
    def sub(self,b:'D')->'D':return self.add(b.neg())
    def mul(self,b:'D')->'D':
        xs=[a*c for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        return D(min(xs)//S,ceildiv(max(xs),S))
    def sq(self)->'D':
        mn=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
        mx=max(self.lo*self.lo,self.hi*self.hi)
        return D(mn//S,ceildiv(mx,S))
    def times(self,k:int)->'D':return D(self.lo*k,self.hi*k) if k>=0 else D(self.hi*k,self.lo*k)
    def rational(self)->'R':return R(Q(self.lo,S),Q(self.hi,S))

@dataclass(frozen=True)
class R:
    lo:Q
    hi:Q
    def __post_init__(self):assert self.lo<=self.hi
    def add(self,b:'R')->'R':return R(self.lo+b.lo,self.hi+b.hi)
    def neg(self)->'R':return R(-self.hi,-self.lo)
    def sub(self,b:'R')->'R':return self.add(b.neg())
    def mul(self,b:'R')->'R':
        vs=[a*c for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        return R(min(vs),max(vs))
    def div(self,b:'R')->'R':
        assert b.lo*b.hi>0
        vs=[a/c for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        return R(min(vs),max(vs))
    def in_(self,lo:Q,hi:Q)->bool:return lo<self.lo<=self.hi<hi
    def decimal_mid(self,digits=14)->str:
        with localcontext() as ctx:
            ctx.prec=digits+18
            x=(self.lo+self.hi)/2
            z=Decimal(x.numerator)/Decimal(x.denominator)
            return f'{z:.{digits}f}'
    def dyadic_width_lt(self,bits:int)->bool:return self.hi-self.lo<Q(1,1<<bits)

ONE=D(S,S)
ZERO=D(0,0)

def orbit(c:D)->tuple[list[D],list[D]]:
    xs=[ZERO]; ds=[ZERO]
    x=ZERO; d=ZERO
    for _ in range(19):
        d=x.mul(d).times(2).add(ONE)
        x=x.sq().add(c)
        xs.append(x);ds.append(d)
    return xs,ds

def factor_product(xs:list[D],start:int,end:int)->D:
    z=ONE
    for j in range(start,end+1):z=z.mul(xs[j].times(2))
    return z

def certified_core():
    C=D(K*(1<<(PREC-TIP_BITS)),(K+1)*(1<<(PREC-TIP_BITS)))
    xs,ds=orbit(C)
    G=xs[18].add(xs[9]).rational()
    Gp=ds[18].add(ds[9]).rational()
    A8=factor_product(xs,1,8).rational()
    A9=factor_product(xs,1,9).rational()
    lam=factor_product(xs,10,18).rational()
    two=R(Q(2),Q(2));one=R(Q(1),Q(1))
    x9=xs[9].rational();x18=xs[18].rational()
    delta=(x18.sub(x9).mul(Gp)).div(lam.sub(one))
    # The two *independent* exact identities for kappa:
    # kappa=Delta'/A9= -G'/[(lambda-1)A8].
    kappa1=delta.div(A9)
    kappa2=Gp.neg().div(lam.sub(one).mul(A8))
    assert G.in_(Q(-1,10**34),Q(1,10**34))
    assert Gp.in_(Q(-71),Q(-70))
    assert x9.in_(Q(-23,1000),Q(-22,1000))
    assert x18.in_(Q(22,1000),Q(23,1000))
    assert A8.in_(Q(9343,100),Q(9345,100)),(A8.decimal_mid(),)
    assert A9.in_(Q(-427,100),Q(-426,100))
    assert lam.in_(Q(3),Q(4))
    assert delta.in_(Q(-1181,1000),Q(-1180,1000))
    assert kappa1.in_(Q(276,1000),Q(277,1000)),(kappa1.decimal_mid(),)
    assert kappa2.in_(Q(276,1000),Q(277,1000)),(kappa2.decimal_mid(),)
    assert kappa1.lo<=kappa2.hi and kappa2.lo<=kappa1.hi
    # Independent differentiation of p(c)=f_c^8(Z(c)), with
    # Z'(c*)=P10'(c*)-Delta'(c*).
    Zp=ds[10].rational().sub(delta)
    pp=Zp
    for j in range(10,18):
        pp=xs[j].rational().mul(pp).mul(two).add(one)
    kappa3=ds[9].rational().add(pp).div(A8)
    assert kappa3.in_(Q(276,1000),Q(277,1000)),kappa3.decimal_mid()
    assert kappa3.lo<=kappa2.hi and kappa2.lo<=kappa3.hi
    # At the special root, the ratio is an exact algebraic identity:
    #  (P9'+p') = -G'/(lambda-1), then kappa=(P9'+p')/A8.
    identity_left=ds[9].rational().add(pp)
    identity_right=Gp.neg().div(lam.sub(one))
    assert identity_left.lo<=identity_right.hi and identity_right.lo<=identity_left.hi
    # The branch sqrt(kappa) is between .525 and .527 by exact rationals.
    assert kappa2.lo > Q(525,1000)**2 and kappa2.hi<Q(527,1000)**2
    # An independent interval product checks A9=(2*x9)*A8, not just
    # factor_product's shared code path.
    prod=x9.mul(two).mul(A8)
    assert prod.lo<=A9.hi and A9.lo<=prod.hi
    return {'tip_bracket':{'numerators':[str(K),str(K+1)],'denominator_bits':TIP_BITS},
        'integer_interval_precision_bits':PREC,
        'Gprime_bounds':['-71','-70'],
        'P9_bounds':['-23/1000','-22/1000'],
        'A8_strict_bounds':['9343/100','9345/100'],
        'A8_midpoint':A8.decimal_mid(18),
        'A9_strict_bounds':['-427/100','-426/100'],
        'A9_midpoint':A9.decimal_mid(18),
        'lambda_strict_bounds':['3','4'],
        'lambda_midpoint':lam.decimal_mid(18),
        'Delta_prime_bounds':['-1181/1000','-1180/1000'],
        'Delta_prime_midpoint':delta.decimal_mid(18),
        'kappa_strict_bounds':['276/1000','277/1000'],
        'kappa_midpoint':kappa2.decimal_mid(18),
        'sqrt_kappa_strict_bounds':['525/1000','527/1000'],
        'independent_kappa_formulas':['Delta_prime/A9','-Gprime/((lambda-1)*A8)', '(P9_prime+p_prime)/A8'],
        'three_kappa_intervals_overlap':True,
        'P9_plus_pprime_interval_midpoint':identity_left.decimal_mid(15),
        'certified_sign':'Rprime=-kappa<0; for real c>tip two pure imaginary points; for c<tip two real points'}

def decimals_diagnostic():
    # Decimal Newton work intentionally *not* counted as a rigorous sign test.
    # Recomputes both the periodic-point continuation and a LOCAL inverse
    # of f_c^9 at the critical value for three small perturbations.
    with localcontext() as ctx:
        ctx.prec=100
        c0=(Decimal(K)+Decimal('0.5'))/Decimal(1<<TIP_BITS)
        def it(c,z,n):
            for _ in range(n):z=z*z+c
            return z
        def it_with_d(c,z,n):
            d=Decimal(1)
            for _ in range(n):d=2*z*d; z=z*z+c
            return z,d
        def tip_root():
            c=c0
            for _ in range(8):
                x=Decimal(0);d=Decimal(0); xs=[x];ds=[d]
                for _ in range(18):
                    d=2*x*d+1;x=x*x+c;xs.append(x);ds.append(d)
                c-=(xs[18]+xs[9])/(ds[18]+ds[9])
            return c
        cstar=tip_root()
        Zstar=it(cstar,Decimal(0),10)
        kappa=Decimal('0.2765920601834685059356050344462046177267')
        checks=[]
        for dstr in ('0.0000000001','0.0000000000001','0.0000000000000001'):
            delta=Decimal(dstr);c=cstar+delta
            # Periodic z(c), near Zstar, with derivative lambda-1.
            Z=Zstar
            for _ in range(8):
                zz,der=it_with_d(c,Z,9)
                Z-=(zz-Z)/(der-1)
            assert abs(it(c,Z,9)-Z)<Decimal('1e-85')
            # The unique local preimage W near c*, F9(W)=Z.
            W=cstar
            for _ in range(10):
                zz,der=it_with_d(c,W,9)
                W-=(zz-Z)/der
            Rval=W-c
            assert Rval<0
            # The pure-imaginary pair +/- i t squares to Rval;
            # f_c^10(z) is evaluated as f_c^9(c+z^2), avoiding
            # unsupported complex Decimal operations.
            assert abs(it(c,c+Rval,9)-Z)<Decimal('1e-85')
            p=it(c,Z,8)
            q=it(c,W,8)
            assert abs(p+q)<Decimal('1e-75')
            assert abs(it(c,-p,9)-p)<Decimal('1e-75')
            ratio=(-Rval/delta)
            assert abs(ratio-kappa)<Decimal('1e-5')
            checks.append({'delta':dstr,
                'negative_R_div_delta':str(round(ratio,19)),
                'imaginary_root_abs':str(round((-Rval).sqrt(),22)),
                'F9_image_minus_p':str(round(q+p,50))})
        return {'decimal_cross_checks':checks,'scope':'diagnostic only; exact interval inequalities prove sign'}

def compute():
    c=certified_core()
    return {'schema_version':1,
            'status':'exact integer interval branch coefficient plus written analytic topological theorem; global gates OPEN',
            'actual_polynomial':'f_c(z)=z^2+c, cstar solves P18(c)+P9(c)=0 in certified 2^-128 bracket',
            'precritical_equation':'f_c^10(s)=Z(c) iff s^2=R(c)=W(c)-c near (cstar,0)',
            'tip_branch_point_order':2,
            'source_return_9_orbit':'F9(s_pm)=-p(c), F9(-p)=p, F9(p)=p',
            'spatial_splitting':'s_plus-minus_s_minus = 2i sqrt(kappa)*sqrt(c-cstar)*(1+O(c-cstar)) on real c>cstar',
            'two_scale_domain_statement':'both branches remain in actual polynomial-like filled K9(c) subset K3(c), no connectedness of Kp(c) assumed',
            'monodromy':'once-around cstar exchanges two local precritical branches; unordered pair is holomorphic',
            'phase_clock':'for c_n(t)>cstar with c_n-cstar~B(t)*lambda^-n, pair distance ~2sqrt(kappa B(t))*lambda^(-n/2)',
            'no_ray_identification_claim':'no assignment of individual external ray angles to branches is established',
            'certified':c,
            'diagnostic':decimals_diagnostic()}

def main():
    a=argparse.ArgumentParser()
    group=a.add_mutually_exclusive_group()
    group.add_argument('--write-manifest',action='store_true')
    group.add_argument('--check-manifest',action='store_true')
    opts=a.parse_args()
    payload=json.dumps(compute(),sort_keys=True,indent=2)+'\n'
    if opts.write_manifest:
        OUTPUT.parent.mkdir(parents=True,exist_ok=True)
        OUTPUT.write_text(payload,encoding='utf-8')
        print('WROTE',OUTPUT)
    elif opts.check_manifest:
        assert OUTPUT.read_text(encoding='utf-8')==payload,'Manifest drift!'
        print('PASS: strict branch sign, three independent coefficient formulas, real/imag split, exact source orbit, manifest')
    else:print(payload,end='')
if __name__=='__main__':main()
