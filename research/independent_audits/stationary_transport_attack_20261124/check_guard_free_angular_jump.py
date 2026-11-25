#!/usr/bin/env python3
"""Finite checks of the guard-free destination and distortion bookkeeping.

No conformal analytic, native chart, or modulus theorem is verified.
"""
from fractions import Fraction as Q
from itertools import product

def destination():
    count=0
    # The choice uses only the position of a maximum. Exhaust all
    # 10-tuples over three positive length levels, including ties.
    for lengths in product((1,2,4),repeat=10):
        t=max(range(10),key=lambda i:lengths[i])
        k=t+2 if t<5 else t-3
        assert 2<=k<=6
        assert k-2>=0 and k+3<10
        assert t in (k-2,k+3)
        pad=lengths[t]
        inner=sum(lengths[k-1:k+3])
        assert inner<=4*pad
        count+=1
    return count

def schedule():
    count=0
    for b in range(1,25):
        c=b+12
        for q in range(2*b+28,2*b+80):
            for t in range(q-b-12,q-b-2):
                kstar=t+2 if t<q-b-7 else t-3
                assert q-b-10<=kstar<=q-b-6
                assert kstar-2>=q-b-12 and kstar+3<=q-b-3
                for k in range(b+2,kstar):
                    r=kstar-k
                    assert k-2>=b and k+3+r-1<=q-b-2
                    assert kstar>=q-c
                    if c<k<q-c:
                        assert r>0 and b+r<=c-1+r<kstar
                        assert kstar+2<=q-b-2
                    count+=1
    return count

def positive_kernel():
    count=0
    # Abstract Herglotz real derivative kernel: summand ratio
    # on (0,1), with t outside [0,1].
    points=[Q(i,20) for i in range(1,20)]
    support=[Q(i,5) for i in range(-15,21) if i<=0 or i>=5]
    for x,y,t in product(points,points,support):
        K=max(Q(1),y/x,(1-y)/(1-x))**2
        assert ((t-y)/(t-x))**2<=K
        count+=1
    return count

def ratios():
    count=0
    for ell,g,p,D in product(range(1,9),repeat=4):
        ell,g,p,D=map(Q,(ell,g,p,D))
        # g<=a, d*ell<=1 after choosing a common scale.
        d=Q(1,max(ell,g))
        new=d*ell
        T=1+g/p
        low=ell/(8*D)
        high=g*D*T*T
        assert high/low+1<=9*D*D*T*T/new
        if g<=4*p:
            assert T<=5
        count+=1
    return count

def absorption():
    count=0
    # The exact polynomial version of sqrt(MA)<=eps*M+A/(4eps).
    for M,A,e in product(range(1,31),range(1,16),range(1,11)):
        M,A,eps=Q(M),Q(A),Q(e,20)
        bound=eps*M+A/(4*eps)
        assert bound>=0 and bound*bound>=M*A
        count+=1
    return count

if __name__=="__main__":
    cs=[destination(),schedule(),positive_kernel(),ratios(),absorption()]
    for label,n in zip(("adaptive padding destination","jump and reflected bank indices",
                        "positive derivative kernel","one-sided ratio envelope",
                        "square-root absorption"),cs):
        print(f"{label}: {n:,} exact cases")
    print(f"PASS: {sum(cs):,} exact discrete checks; geometry not certified.")
