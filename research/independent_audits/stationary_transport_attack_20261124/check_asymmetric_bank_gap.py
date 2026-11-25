#!/usr/bin/env python3
"""Finite asymmetric-bank and backward ratio checks, not geometry proofs."""
from fractions import Fraction as Q
from itertools import product

def banks():
    count=0
    for b in range(1,25):
        h=b+2; H=h+2; c=2*b+20; t=H+2
        for q in range(2*(c+t)+4,2*(c+t)+24):
            B={i%q for i in range(-c,c+1)}
            cap={i%q for i in range(-c,c+t+1)}
            reset={i%q for i in range(-b,b+1)}
            cur=set(B)
            for j in range(H+1):
                assert cur<=cap
                cur=({(i+1)%q for i in cur if i!=0}
                     | (reset if 0 in cur else set()))
                count+=1
            for i in {(x%q) for x in range(-c-1,c+2)}:
                out=reset if i==0 else {(i+1)%q}
                assert out<=cap
                count+=1
            assert {c+2,q-c}<=cap
            for r in range(1,t+1):
                k=c+r
                assert b+r<c<k<q-c<q-b-1
                assert k in cap-B
                assert k-r==c
                assert b<=c<=q-b-1-r
                # Whole left and right bank limbs lie between the
                # actual terminal corridor cuts and the image limb.
                assert b+r<=c<=k-1
                assert k+1<=q-c<=q-b-1
                count+=1
    return count

def ratios():
    count=0
    for old,L,G,D in product(range(1,13),repeat=4):
        old,L,G=Q(old,12),Q(L,12),Q(G,12)
        D=Q(D)
        if L<=G:
            deriv=4*D/G
            assert 4*D*L*deriv==16*D*D*L/G
        else:
            assert old<=16*D*D*L/G
        for sub in range(1,5):
            ell=L/sub
            S=L/ell
            assert S==sub
            assert (16*D*D*L/G)/ell==16*D*D*S/G
            count+=1
    return count

if __name__=="__main__":
    a,b=banks(),ratios()
    print(f"asymmetric cap and backward chart indices: {a:,} exact cases")
    print(f"backward derivative/atom ratio algebra: {b:,} exact cases")
    print(f"PASS: {a+b:,} exact discrete checks; geometry not certified.")
