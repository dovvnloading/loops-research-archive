#!/usr/bin/env python3
"""Independent all-integer transversality test at the actual two-scale tip.

Proves an EXACT rational enclosure of the nonzero phase-to-parameter
transversality for f_c^9 at the Misiurewicz c_tip from the archive. This
finite program does not replace the written uniform Koenigs theorem.
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

P=256
S=1<<P
K=-607918036626757496169199575185708826140
BASE_BITS=128
MANIFEST=Path(__file__).resolve().parents[2]/'results'/'period9_tip_phase_transversality_20261107.json'


def ceil_div(x:int,y:int)->int:
    return -((-x)//y)

@dataclass(frozen=True)
class I:
    lo:int
    hi:int
    def __post_init__(self):assert self.lo<=self.hi
    def add(self,other:I)->I:return I(self.lo+other.lo,self.hi+other.hi)
    def neg(self)->I:return I(-self.hi,-self.lo)
    def sub(self,other:I)->I:return self.add(other.neg())
    def mul(self,other:I)->I:
        q=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return I(min(q)//S,ceil_div(max(q),S))
    def sq(self)->I:
        a=self.hi*self.hi;b=self.lo*self.lo
        low=0 if self.lo<=0<=self.hi else min(a,b)//S
        return I(low,ceil_div(max(a,b),S))
    def times(self,n:int)->I:
        return I(self.lo*n,self.hi*n) if n>=0 else I(self.hi*n,self.lo*n)
    def bounds(self)->list[str]:return [str(F(self.lo,S)),str(F(self.hi,S))]

ZERO=I(0,0);ONE=I(S,S)


def orbit(c:I):
    x=ZERO;d=ZERO
    xs=[x];ds=[d]
    for _ in range(19):
        d=x.mul(d).times(2).add(ONE)
        x=x.sq().add(c)
        xs.append(x);ds.append(d)
    return xs,ds


def compute():
    C=I(K*(1<<(P-BASE_BITS)),(K+1)*(1<<(P-BASE_BITS)))
    xs,ds=orbit(C)
    g=xs[18].add(xs[9]);gd=ds[18].add(ds[9])
    assert F(-71)<F(gd.lo,S)<F(gd.hi,S)<F(-70)
    assert xs[9].hi<0<xs[18].lo
    multiplier=ONE
    for j in range(10,19):multiplier=multiplier.mul(xs[j].times(2))
    assert 3*S<multiplier.lo<=multiplier.hi<4*S
    h_factor=xs[18].sub(xs[9]);num=h_factor.mul(gd)
    den=multiplier.sub(ONE)
    assert num.hi<0 and den.lo>0
    dlo=F(num.lo,den.lo)
    dhi=F(num.hi,den.hi)
    assert F(-1181,1000)<dlo<dhi<F(-1180,1000),(float(dlo),float(dhi))

    # Analytic continuation z(c) of the repelling 9-fixed point:
    # z'(c_tip)=P10'(c_tip)-Delta'(c_tip).  Differentiate the exact nine
    # local orbit factors, retaining both signs of each physical phase.
    def p_add(u,v):return (u[0]+v[0],u[1]+v[1])
    def p_mul(u,v):
        a=[x*y for x in u for y in v]
        return (min(a),max(a))
    def p_div(u,v):
        assert v[0]*v[1]>0
        a=[x/y for x in u for y in v]
        return (min(a),max(a))
    zp=(F(ds[10].lo,S)-dhi,F(ds[10].hi,S)-dlo)
    dl=(F(0),F(0))
    one=(F(1),F(1))
    two=(F(2),F(2))
    for j in range(10,19):
        zj=(F(xs[j].lo,S),F(xs[j].hi,S))
        assert zj[0]*zj[1]>0
        dl=p_add(dl,p_div(zp,zj))
        zp=p_add(p_mul(two,p_mul(zj,zp)),one)
    assert F(-500)<dl[0]<dl[1]<F(-490),(float(dl[0]),float(dl[1]))
    # Independent computation of derivative of f_c^9(P_10(c))-P_10(c).
    # This is d/dc(P_19-P_10). At the exact root P_18+P_9=0,
    # it equals (P_18-P_9)*(P'_18+P'_9).
    direct_hprime=ds[19].sub(ds[10])
    assert direct_hprime.lo < num.hi and direct_hprime.hi > num.lo
    assert direct_hprime.hi < 0
    # At the two endpoints of the certified bracket the function G crosses
    # zero in the source-cited direction. This uses a separate exact
    # one-point iterate, not the box derivative computation above.
    lxs,_=orbit(I(C.lo,C.lo))
    rxs,_=orbit(I(C.hi,C.hi))
    assert lxs[18].add(lxs[9]).lo>0
    assert rxs[18].add(rxs[9]).hi<0
    z0=xs[10]
    # c_tip is inside (-2,-1), so the entire tip neighborhood on the
    # real line lies in M, independently of the tuned-center parameter.
    assert -2*S<C.lo<C.hi<-S
    return {
      'status':'EXACT_REPELLING_PERIOD9_TRANSVERSALITY',
      'parameter_bracket':{'lower_numerator':K,'upper_numerator':K+1,'denominator_power_of_two':BASE_BITS},
      'precision_bits':P,
      'critical_preperiod':10,'repelling_return_period':9,
      'critical_value_x9_sign':'negative','x18_sign':'positive',
      'Gprime_certified_interval':['-71','-70'],
      'return_multiplier_interval':['3','4'],
      'phase_transversality_delta_prime_interval':['-1181/1000','-1180/1000'],
      'phase_transversality_approx':round(float((dlo+dhi)/2),12),
      'log_multiplier_parameter_derivative_bound':['-500','-490'],
      'log_multiplier_parameter_derivative_approx':round(float((dl[0]+dl[1])/2),9),
      'second_order_n_term_coefficient':'-lambda9_prime/lambda9 * B(t)^2, with 490 < -lambda9_prime/lambda9 < 500',
      'repelling_fixed_point_z0_approx':round(float(F(z0.lo+z0.hi,2*S)),12),
      'factorization':'P19-P10=(P18-P9)*(P18+P9)',
      'transversality_identity':'d/dc(P10-z(c_tip))=(P18-P9)*(P18_prime+P9_prime)/(lambda9-1)',
      'independent_forward_derivative_identity_check':True,
      'actual_physical_clock':'10+9*n iterates',
      'native_two_scale_context':'same exact real tip has certified period-3/9 quadratic-like restrictions, but those markings are not transported here',
      'provenance':'exact dyadic integer arithmetic only; general Koenigs phase theorem is written proof; MLC remains open'
    }


def main():
    parser=argparse.ArgumentParser()
    opts=parser.add_mutually_exclusive_group()
    opts.add_argument('--write-manifest',action='store_true')
    opts.add_argument('--check-manifest',action='store_true')
    a=parser.parse_args()
    s=json.dumps(compute(),indent=2,sort_keys=True)+'\n'
    if a.write_manifest:
        MANIFEST.parent.mkdir(parents=True,exist_ok=True)
        MANIFEST.write_text(s,encoding='utf-8')
        print('WROTE',MANIFEST)
    elif a.check_manifest:
        assert MANIFEST.read_text(encoding='utf-8')==s
        print('PASS: exact period-9 landing transversality, multiplier, two independent derivative factorizations and manifest')
    else:print(s,end='')

if __name__=='__main__':main()
