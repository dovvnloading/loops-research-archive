#!/usr/bin/env python3
"""Exact directional-kernel and compression bookkeeping regressions.

Not a proof of the conformal representation or native marking.
"""
from fractions import Fraction as Q
from itertools import product

def kernels():
    count=0
    # Exponential coordinate u in a proper real interval (L,U).
    # Check every positive summand comparison before the strip
    # factor exp(-pi V) is applied.
    L,U=Q(1),Q(4)
    pts=[Q(i,10) for i in range(11,40)]
    left=[Q(i,4) for i in range(-12,5)]
    right=[Q(i,4) for i in range(16,33)]
    for y,x in product(pts,repeat=2):
        if y>=x: continue
        for v in left:
            h_y=y/(y-v)**2
            h_x=x/(x-v)**2
            assert h_y>=y/x*h_x
            count+=1
        for v in right:
            h_y=y/(v-y)**2
            h_x=x/(v-x)**2
            assert h_x>=h_y
            count+=1
    return count

def split_means():
    count=0
    # Nonnegative discrete contributions at representative
    # points: left after removing the exponential factor
    # is nonincreasing, right is nondecreasing. Arbitrary
    # positive weights in an E interval.
    for left,right in product(range(4),repeat=2):
        for L0,L1,R0,R1 in product(range(4),repeat=4):
            if not L0>=L1 or not R0<=R1: continue
            mean_l=Q(L0+L1,2);mean_r=Q(R0+R1,2)
            A=mean_l+mean_r
            if mean_l>=A/2 and left>=L0:
                assert left>=A/2
                count+=1
            if mean_r>=A/2 and right>=R1:
                assert right>=A/2
                count+=1
    return count

def indices():
    count=0
    for b in range(1,25):
        t=b+6
        for c in (2*b+20,3*b+30,4*b+50):
            for q in range(2*(c+t)+4,2*(c+t)+24):
                B={i%q for i in range(-c,c+1)}
                for r in range(1,t+1):
                    k=c+r
                    for jstar in range(1,r+1):
                        E=c+jstar
                        assert E<=k<q-b-1
                        assert all(b+1<=j+1<E
                                   for j in range(b,c))
                        # Forward-to-bank chain stays on the right
                        # side of the witness and inside the chart.
                        for n in (k+1,q-b-1):
                            assert E<n<=q-b-1
                        assert q-b-1 in B
                        assert q-b-2>=k
                        count+=1
    return count

def ratios():
    count=0
    # Finite products with possible subdivision. Check the
    # numerator min-ancestor inequality and geometric mean
    # bound by integer-power comparisons, no floating logs.
    for r in range(1,5):
        for a in product((Q(1,2),Q(1),Q(2),Q(3)),repeat=r):
            A=max(a)
            P=Q(1)
            for ai in a:P*=ai
            for S in (Q(1),Q(2),Q(5)):
                assert S*P<=S*A**r
                count+=1
    for n in range(1,6):
        for sizes in product(range(1,5),repeat=n+1):
            R=[Q(sizes[j],sizes[j+1]) for j in range(n)]
            q=min(R)
            assert q**n<=Q(sizes[0],sizes[-1])
            count+=1
    return count

def scalar_negative_control():
    # Arbitrarily large simultaneous left compression can
    # satisfy the finite scalar requirements. Not a native
    # holomorphic or dynamical example.
    count=0
    for n in range(1,20):
        for K in (2,4,16,256):
            widths=[Q(1,4*K**j) for j in range(n+1)]
            assert sum(widths)<1
            assert all(widths[j]/widths[j+1]==K
                       for j in range(n))
            assert widths[0]/widths[-1]==K**n
            count+=1
    return count

if __name__=="__main__":
    cs=[kernels(),split_means(),indices(),ratios(),scalar_negative_control()]
    for label,n in zip(("directional positive kernels","positive mean split",
                        "forward-to-bank indices","compression products",
                        "scalar nonclosure controls"),cs):
        print(f"{label}: {n:,} exact cases")
    print(f"PASS: {sum(cs):,} exact discrete checks; geometry not certified.")
