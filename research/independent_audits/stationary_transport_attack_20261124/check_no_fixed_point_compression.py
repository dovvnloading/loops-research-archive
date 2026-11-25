#!/usr/bin/env python3
"""Finite checks for the no-fixed-point compression and bank plateau.

These check algebra/indices only, not any holomorphic or native chart.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement, product

def left_kernel():
    count=0
    # Exponential-coordinate denominator bound before using the
    # strip MVT to turn it into exp(-pi V)/2.
    a=Q(1)
    for x in (Q(i,8) for i in range(9,33)):
        for y in (Q(i,8) for i in range(9,49)):
            if y<x: continue
            for v in (Q(i,4) for i in range(-12,5)):
                assert (x-v)/(y-v)>=(x-a)/(y-a)
                count+=1
    # MVT lower ratio: a factor D accounts for bounded exponential
    # derivative variation. A left radius at most doubles.
    for m,D,s in product(range(1,13),range(1,9),range(13)):
        m,D=Q(m),Q(D)
        step=m*Q(s,12)
        assert m/(D*(m+step))>=1/(2*D)
        count+=1
    return count

def no_fixed_point():
    count=0
    # H(x0)-x0=-ell with ell<=m. If the chart reaches
    # x0+3m/4 and H'>=3 there, the shift is positive.
    for m,n,slope in product(range(1,25),range(1,25),range(3,13)):
        if n>m: continue
        m,ell=Q(m),Q(n)
        step=3*m/4
        assert -ell+(slope-1)*step>=m/2>0
        count+=1
    # High left average persists in the local interval.
    for D in range(1,25):
        for a in range(25,65):
            A=Q(a*D**3)
            h0=A/(2*D)
            persistent=h0/(4*D**2)
            assert persistent>3
            count+=1
    return count

def plateau():
    count=0
    # Exhaust all monotone bounded atom counts for small abstract
    # occupancies and window lengths. The written pigeonhole proof
    # handles all b and t, without enumerating enormous sequences.
    for cap in range(1,6):
        for t in range(1,5):
            for seq in combinations_with_replacement(range(1,cap+1),cap*t+1):
                increases=sum(x<y for x,y in zip(seq,seq[1:]))
                assert increases<=cap-1
                good=[i for i in range(cap)
                      if seq[i*t]==seq[(i+1)*t]]
                assert good
                assert all(seq[j]==seq[j+1]
                           for j in range(good[0]*t,(good[0]+1)*t))
                count+=1
    # The actual b-dependent windows and their right-forward escape.
    for b in range(1,49):
        cap=6*b; c0=2*b+20; t=b+6
        q0=2*(c0+cap*t)+4
        for i in range(cap):
            c=c0+i*t
            assert q0>=2*(c+t)+4
            assert b<=c<c+t<=q0-b-2
            assert q0-b-1>=q0-c
            for r in (1,t):
                k=c+r
                assert k<q0-b-1
                assert k>=b+2
                count+=1
    return count

def ratio_and_amplification():
    count=0
    for r in range(1,6):
        for a in product((Q(1,2),Q(1),Q(3),Q(24)),repeat=r):
            p=Q(1)
            for ai in a:p*=ai
            assert p<=24**r
            for t in range(r,7):
                assert p<=24**t
                count+=1
    # If width<=C(R+V+1) and width>=C(L+2)R,
    # then V>=L R at R>=1.
    for C,L,R,V in product(range(1,9),range(1,9),
                           range(1,9),range(0,65)):
        lower=C*(L+2)*R
        upper=C*(R+V+1)
        if lower<=upper:
            assert V>=L*R
            count+=1
    return count

if __name__=="__main__":
    cs=[left_kernel(),no_fixed_point(),plateau(),ratio_and_amplification()]
    for label,n in zip(("left kernel persistence","no-fixed-point contradiction",
                        "constant-count plateau and native indices",
                        "absolute ratio and amplification"),cs):
        print(f"{label}: {n:,} exact cases")
    print(f"PASS: {sum(cs):,} exact discrete checks; geometry not certified.")
