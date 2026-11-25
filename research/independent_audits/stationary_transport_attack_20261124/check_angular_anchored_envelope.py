#!/usr/bin/env python3
"""Exact rational regressions for the angular envelope and guard algebra.

The logarithmic envelope is a written modulus proof. These tests check
its finite ratio identities, cyclic distance conditions and scale bounds.
"""
from fractions import Fraction as Q
from itertools import product

def clipped_ratio():
    count=0
    vals=[Q(i,64) for i in range(1,33)]
    for s in vals:
        cap=2*s
        for ell,near in product(vals,repeat=2):
            if near<ell: continue
            a=cap/min(cap,ell)
            b=cap/min(cap,near)
            assert a>=b>=1
            assert a/b==min(cap,near)/min(cap,ell)
            count+=1
    return count

def radial_factorization():
    count=0
    vals=[Q(i,128) for i in range(1,33)]
    for r0,rho,s in product(vals,repeat=3):
        if r0>s or rho<r0: continue
        cut=min(s,rho)
        assert s/r0==(cut/r0)*(s/cut)
        assert s/cut==max(Q(1),s/rho)
        count+=1
    return count

def bank_distance():
    count=0
    for q in range(8,15):
        for c in range(1,(q-3)//2+1):
            small={k%q for k in range(-(c-1),c)}
            large={k%q for k in range(-c,c+1)}
            for k in range(q):
                if k in large: continue
                # Every directed proper base containing k and an
                # open part of the smaller bank must pass through
                # a whole intervening limb (use at least one atom
                # per limb in the real argument).
                for start in range(q):
                    for span in range(1,q):
                        arc=[(start+i)%q for i in range(span+1)]
                        if k not in arc or not small.intersection(arc): continue
                        assert len(arc)>=3
                        for t in small.intersection(arc):
                            i,j=sorted((arc.index(k),arc.index(t)))
                            assert j-i>=2
                        count+=1
    return count

def guard_ratio():
    count=0
    for L,R,inner in product(range(1,21),repeat=3):
        if L+R+inner>50: continue
        g=Q(min(L,R),50); A=Q(L+R+inner,50)
        for s in (Q(1,4),Q(1,8),Q(1,16),Q(1,64)):
            # exp(G_T) <= exp(log_+(2s/g)+log_+(1/(4s))).
            assert A/(2*g)<=max(Q(1),2*s/g)*max(Q(1),1/(4*s))
            count+=1
    return count

def guard_scale():
    count=0
    for a in range(2,101):
        t=Q(1,64*(a+1)**2)
        assert a*a*2*t<=Q(1,16)
        assert t+Q(1,4)<Q(1,2)<1-t
        count+=1
    return count

if __name__=="__main__":
    counts=[clipped_ratio(),radial_factorization(),bank_distance(),
            guard_ratio(),guard_scale()]
    for name,v in zip(("clipped atom ratio","radial interval split",
                       "remote bank separation","terminal guard ratio",
                       "extreme guard scale"),counts):
        print(f"{name}: {v:,} exact cases")
    print(f"PASS: {sum(counts):,} exact discrete checks; geometry not certified.")
