#!/usr/bin/env python3
"""Exact finite regression only; no continuum theorem is machine-checked."""
from fractions import Fraction as F
import json


def arctan_bounds(x, n):
    s = sum(((-1)**j * x**(2*j+1) / (2*j+1) for j in range(n)), F(0))
    t = s + (-1)**n * x**(2*n+1) / (2*n+1)
    return min(s,t), max(s,t)


def pi_bounds():
    a,b = arctan_bounds(F(1,5), 20)
    c,d = arctan_bounds(F(1,239), 8)
    return 16*a-4*d,16*b-4*c


def transit(k):
    # Outward rounding for the nonnegative actual real critical orbit.
    S = 1 << 192
    c = S//4 + (S >> (2*k))
    lo = hi = 0
    hits = {}
    for j in range(1, 4*(1 << k)+100):
        oldhi = hi
        lo,hi = lo*lo//S+c, (hi*hi+S-1)//S+c
        for threshold in (1,2):
            if threshold not in hits and hi >= threshold*S:
                if not (oldhi < threshold*S <= lo):
                    raise ArithmeticError('ambiguous first crossing')
                hits[threshold] = j
        if len(hits)==2:
            break
    if set(hits)!={1,2}:
        raise ArithmeticError('missing crossing')
    n,j = hits[1],hits[2]
    p,q = pi_bounds()
    assert 0 <= j-n <= 4
    # From the written error proof, |N-pi/h| <= 84 log(1/h)+31.
    # Use log(2)<1 to keep this assertion entirely rational.
    assert q*(1<<k)-84*k-31 <= n <= p*(1<<k)+84*k+31
    return {'k':k,'N':n,'J':j,'J_times_h':str(F(j,1<<k))}


def mul(z,w):
    x,y=z; s,t=w
    return x*s-y*t, x*t+y*s


def div(z,w):
    s,t=w
    x,y=mul(z,(s,-t))
    d=s*s+t*t
    return x/d,y/d


def norm2(z):
    return z[0]**2+z[1]**2


def cardioid(w,a):
    # Re sqrt(-w) > a |w| iff sqrt(|w|^2)> Re(w)+2a^2|w|^2.
    # The negative right-hand-side branch must not be squared.
    W=norm2(w)
    rhs=w[0]+2*a*a*W
    return rhs < 0 or W > rhs*rhs


def circle_points():
    yield F(-1),F(0)
    for t in {F(0),F(1),F(-1)} | {s*F(2)**k for k in range(-10,11) for s in (-1,1)}:
        yield (1-t*t)/(1+t*t),2*t/(1+t*t)


def inclusion():
    total=outside=0
    for B in (F(1,4),F(1),F(4)):
        for eta in (F(1,4),F(1,16),F(1,64),F(1,256)):
            for delta in (F(1),eta,eta*eta):
                # Select a with strict lemma hypothesis by exact arithmetic.
                a=F(1,2)
                while 100*B*a*a >= eta*eta*delta:
                    a/=2
                r=(1-eta)/(1+eta)
                for factor in (F(1),F(3,4),F(1,2),F(0)):
                    for x,y in circle_points():
                        z=(r*factor*x,r*factor*y)
                        assert norm2(z)<=r*r
                        w=div((4*B*z[0],4*B*z[1]),mul((1+z[0],z[1]),(1+z[0],z[1])))
                        total+=1
                        if norm2(w)>=B*B*(1+delta)**2:
                            outside+=1
                            assert cardioid(w,a), (B,eta,delta,a,z,w)
    assert outside>0
    return {'total':total,'outside_disk':outside}


def ground_witness():
    total=0
    # For b_s=1, take exact nearby real thresholds R and k=13.
    # These are model coordinates, not computed native Green levels.
    for a in (F(1,256),F(1,1024),F(1,4096)):
        for R in (1-a,1+a,F(1)):
            for x,y in circle_points():
                w=(R+a*x,13*a+a*y)
                assert norm2(w)<=9
                assert w[1]>=12*a
                assert cardioid(w,a)
                total+=1
    return total


if __name__=='__main__':
    print(json.dumps({'transit':[transit(k) for k in range(4,13)],
                      'inclusion':inclusion(),'ground_witness':ground_witness()},indent=2))
