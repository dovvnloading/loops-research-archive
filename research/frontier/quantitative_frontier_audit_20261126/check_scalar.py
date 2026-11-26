#!/usr/bin/env python3
"""Validated interval enclosure of all backward pre-Schwarzians on I0.

Run beside check.py: python -B check_scalar.py
Uses no floats and certifies a uniform L/R split, not just sampled histories.
"""
from bisect import bisect_left, bisect_right
from fractions import Fraction as Q
from math import isqrt
import json

N=-607918036626757496169199575185708826140
B=2**48

def ceil(a,b):
    assert b>0
    return -(-a//b)

def enc(q):
    q=Q(q)
    return q.numerator*B//q.denominator,ceil(q.numerator*B,q.denominator)

def add(X,Y): return X[0]+Y[0],X[1]+Y[1]
def neg(X): return -X[1],-X[0]
def sub(X,Y): return add(X,neg(Y))
def scale(X,n):
    assert n>0
    return n*X[0],n*X[1]
def mul(X,Y):
    vs=[x*y for x in X for y in Y]
    return min(vs)//B,ceil(max(vs),B)
def div(X,Y):
    assert Y[0]>0
    return min(x*B//y for x in X for y in Y),max(ceil(x*B,y) for x in X for y in Y)
def sqrt(X):
    assert X[0]>0
    l=isqrt(X[0]*B);h=isqrt(X[1]*B)
    return l,h+int(h*h<X[1]*B)

A=(enc(Q(-N-1,2**128))[0],enc(Q(-N,2**128))[1])
I=(enc(Q(-93,100))[0],enc(Q(93,100))[1])

def branch_data(X):
    t=sqrt(add(X,A)); v=sqrt(sub(A,t))
    d=div((B,B),scale(mul(t,v),4))
    p=div(sub(scale(t,12),scale(A,8)),scale(mul(mul(t,t),sub(A,t)),16))
    return v,d,p

cells=4096
edges=[I[0]+(I[1]-I[0])*i//cells for i in range(cells+1)]
assert all(edges[i]<edges[i+1] for i in range(cells))

def indices(Y):
    assert I[0]<=Y[0]<=Y[1]<=I[1]
    l=max(0,bisect_right(edges,Y[0])-1)
    h=min(cells-1,bisect_left(edges,Y[1]))
    assert 0<=l<=h<cells
    assert edges[l]<=Y[0] and Y[1]<=edges[h+1]
    return l,h

rows=[]
for i in range(cells):
    v,d,p=branch_data((edges[i],edges[i+1]))
    assert 0<d[0]<=d[1] and 12*d[1]<=5*B
    assert -B<=p[0]<=p[1]<=B
    rows.append((indices(neg(v)),indices(v),d,p))

# For every history, the initial interval [-2,2] contains its
# pre-Schwarzian on every cell: sum_j (5/12)^j <= 12/7 < 2.
# Every update encloses all histories by the chain rule and the
# already validated input enclosures. No convergence assumption.
V=[(-2*B,2*B)]*cells

def image_bounds(V,span):
    l,h=span
    return min(V[i][0] for i in range(l,h+1)),max(V[i][1] for i in range(l,h+1))

def one_step(V,row):
    L,R,d,p=row
    return add(p,mul(d,image_bounds(V,L))),add(p,mul(neg(d),image_bounds(V,R)))

iterations=20
for _ in range(iterations):
    W=[]
    for row in rows:
        l,r=one_step(V,row)
        W.append((min(l[0],r[0]),max(l[1],r[1])))
    V=W

# Opposite most recent symbols, at the *same* arbitrary real input.
# The L interval lies strictly above the R interval in every cell.
gaps=[]
for i,row in enumerate(rows):
    l,r=one_step(V,row)
    gap=l[0]-r[1]
    assert gap>0,(i,gap)
    gaps.append(gap)
assert min(gaps)*1000>5*B
print(json.dumps({'cells':cells,'dyadic_bits':48,'enclosure_iterations':iterations,
                  'minimum_L_minus_R_gap_ppm_floor':min(gaps)*10**6//B,
                  'derivative_upper':'5/12','branch_pre_schwarzian_bound':'1'},
                 sort_keys=True,indent=2))
