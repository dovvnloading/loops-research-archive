#!/usr/bin/env python3
"""Exact rational/dyadic checks for the physical 3/9 tip; stdlib only.

No numerical floats, no ray landing, no analytic theorem inferred from tests.
Run: python -B check.py
"""
from fractions import Fraction as Q
from math import isqrt
import json

N = -607918036626757496169199575185708826140
A0, A1 = Q(-N-1, 2**128), Q(-N, 2**128)
a0, a1 = Q(1786510, 10**6), Q(1786511, 10**6)
assert a0 < A0 < A1 < a1
assert Q(5,4) < a0*a0-a0 < a1*a1-a1 < Q(29,20)
t0,t1=Q(29,50),Q(1743,1000)
assert t0*t0 < a0-Q(29,20) and a1+Q(5,4) < t1*t1
assert a0>t1 and a1-t0<Q(11,10)**2
assert min(t*t*(a0-t) for t in (t0,t1))>Q(1,9)
# Invariant real interval for the physical end coding.
r=Q(93,100)
assert a0-r>0 and a0*a0-a0>r
assert a0-r>(a1-r*r)**2 # implies a1-sqrt(a0-r)<r*r
# Uniform real upper bound on |g'| along both inverse sheets.
assert Q(64,27)*a1**3 < Q(15,4)**2

B=2**48

def ceildiv(a,b):
    assert b>0
    return -(-a//b)

def enc(lo,hi=None):
    lo=Q(lo);hi=lo if hi is None else Q(hi)
    return (lo.numerator*B//lo.denominator,ceildiv(hi.numerator*B,hi.denominator))

def add(X,Y): return (X[0]+Y[0],X[1]+Y[1])
def sub(X,Y): return (X[0]-Y[1],X[1]-Y[0])
def sqrt(X):
    assert X[0]>0
    l=isqrt(X[0]*B); h=isqrt(X[1]*B)
    return l,h+(h*h<X[1]*B)

A=enc(A0,A1)
I=enc(-r,r)

def parts(X):
    t=sqrt(add(X,A)); v=sqrt(sub(A,t)); return t,v

def phi(X,letter):
    _,v=parts(X)
    return (-v[1],-v[0]) if letter==0 else v

def d(X):
    t,v=parts(X)
    return B**3//(4*t[1]*v[1]),ceildiv(B**3,4*t[0]*v[0])

# Check interval maps really preserve the interval, and derivative contraction.
for j in range(2):
    Y=phi(I,j)
    assert I[0]<Y[0]<=Y[1]<I[1]
assert phi(I,0)[1]<phi(I,1)[0]

m=9
cells=[I]
for _ in range(m):
    cells=[phi(X,j) for j in range(2) for X in cells]
assert len(cells)==2**m
bounds=[d(X) for X in cells]
assert all(0<l<=h<B for l,h in bounds)
assert all(l*15>4*B for l,h in bounds)

# floor(B*(x/B)**(p/q)) by exact integer comparison, no libm.
def root_weight(x,p,q):
    assert 0<x<B and 0<p<q
    rhs=x**p*B**(q-p)
    lo,hi=0,B
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**q<=rhs:lo=mid
        else:hi=mid
    assert lo**q<=rhs<hi**q
    return lo

# Piecewise constant positive test function on the physical prefix cylinders.
# Iterates below merely find candidates; only the final strict integer
# inequalities are used as a certificate.
def test(p,q,direction):
    W=[(root_weight(l,p,q),root_weight(h,p,q)+1) for l,h in bounds]
    n=len(W);V=[B]*n
    for _ in range(60):
        Y=[((l+h)*(V[i//2]+V[n//2+i//2]))//(2*B) for i,(l,h) in enumerate(W)]
        M=max(Y);V=[y*B//M for y in Y]
        assert min(V)>0
    num=[]
    for i,(l,h) in enumerate(W):
        vv=V[i//2]+V[n//2+i//2]
        diff=l*vv-B*V[i] if direction=='lower' else B*V[i]-h*vv
        assert diff>0,(p,q,i,diff)
        num.append(Q(diff,B*V[i]))
    # This lower bound on the certified relative gap is rounded down to ppm.
    gap=min(num)
    return {'exponent':f'{p}/{q}','direction':direction,'states':n,
            'minimum_gap_ppm_floor':(gap*10**6).__floor__()}

report={'parameter_isolator':'inherited exact 128-bit bracket',
        'stadium_real_inequalities':'PASS','dyadic_bits':48,'prefix_depth':m,
        'tests':[test(89,150,'lower'),test(19,32,'upper')]}
print(json.dumps(report,indent=2,sort_keys=True))
