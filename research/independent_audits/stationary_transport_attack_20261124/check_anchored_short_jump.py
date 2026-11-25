#!/usr/bin/env python3
"""Exact finite tests for short crest guard, long-jump scheduler and width scale.

Not a verifier of holomorphic lifting, the native marking, angle guards,
or modulus estimates.
"""
from fractions import Fraction as Q
from itertools import product

def short_guard():
    count=0
    for q in range(4,9):
        for sizes in product((1,2),repeat=q):
            limb=[]; masks=[]
            for k,n in enumerate(sizes):
                m=0
                for _ in range(n):
                    m |= 1<<len(limb)
                    limb.append(k)
                masks.append(m)
            M=len(limb)
            union_by_anchor=[0]*M
            for a in range(M):
                # Endpoint atoms distinct; the long same-atom route is
                # checked too, with full remaining circle as crest.
                for span in range(2,M+1):
                    z=(a+span)%M
                    if a==z and span!=M: continue
                    crest=0
                    for t in range(1,span): crest|=1<<((a+t)%M)
                    if any(crest&mask==mask for mask in masks): continue
                    base=crest|(1<<a)|(1<<z)
                    touched={limb[j] for j in range(M) if base>>j&1}
                    assert len(touched)<=2
                    if len(touched)==2:
                        x,y=sorted(touched)
                        assert (y-x)%q in (1,q-1)
                    for j in range(M):
                        if crest>>j&1:
                            for k in touched:
                                union_by_anchor[j]|=1<<k
                    count+=1
            for j,U in enumerate(union_by_anchor):
                k=limb[j]
                allowed=(1<<k)|(1<<((k-1)%q))|(1<<((k+1)%q))
                assert U&~allowed==0
                assert U!=(1<<q)-1
                count+=1
    return count

def visits():
    count=0
    for M in range(2,65):
        for r in range(1,min(12,M)+1):
            critical=(1<<r)-1
            for ell in range(1,M):
                hits=0
                for start in range(M):
                    base=0
                    for z in range(ell): base|=1<<((start+z)%M)
                    hits+=bool(base&critical)
                assert hits<=min(M,r+ell-1)
                count+=1
    return count

def jump_schedule():
    count=0
    for b in range(1,17):
        c=b+8
        for q in range(2*b+20,2*b+100):
            kstar=q-b-5
            for k0 in range(1,q):
                for wide in (0,1): # one/two adjacent limbs of crest
                    if k0+wide>=q: continue
                    if not any(min(k,q-k)<=c for k in range(k0,k0+wide+1)):
                        continue
                    k=k0
                    steps=jumps=0
                    while k+wide<q:
                        assert any(min(t,q-t)<=c for t in range(k,k+wide+1))
                        if b+2<=k<kstar:
                            r=kstar-k
                            # check the two extremes of the linearly
                            # translated full band on all input times
                            assert k-2>=b
                            assert k+3+(r-1)<=q-b-2
                            assert k-2+r==q-b-7
                            assert k+3+r==q-b-2
                            assert k+2+r==q-b-3
                            k+=r
                            jumps+=1
                        else:
                            k+=1
                            steps+=1
                        count+=1
                    assert jumps<=1
                    assert steps<=2*b+10
    return count

def guard_geometry():
    count=0
    # Rational strip lengths normalized by a; test local threshold
    # segments' side distance and the energy integral's split points.
    for a in range(2,33):
        for g in range(1,a//2+1):
            for x0 in range(g,a-g+1):
                r0=min(x0,a-x0)
                assert r0>=g
                for dx in (Q(-r0,4),Q(0),Q(r0,4)):
                    x=Q(x0)+dx
                    rad=max(Q(g),min(x,a-x))
                    assert Q(3*r0,4)<=rad<=Q(5*r0,4)
                    assert Q(r0,4)<=rad
                    assert Q(10,1)/rad*Q(r0,8)>=1
                    count+=1
            # padding bound is scale invariant (degree d cancels).
            for d in (2,4,8,64,1024):
                assert Q(a,d)/(2*Q(g,d))==Q(a,2*g)
                count+=1
    return count

def scale():
    count=0
    for a in range(2,101):
        tp=Q(1,64*(a+1)**2)
        # One backwards tolerance step at representative scales,
        # without materializing double-exponential exact rationals.
        for t in (tp,tp/2,tp/100,Q(1,1000),Q(1,100000)):
            s=t*t/(64*(a+1)**2)
            assert 2*s<=t/2
            assert a*a*2*s <= (t/4)**2
            assert tp<=Q(1,256)
            # At terminal tolerance eta<=tp, u<=tp,
            # the series term is at most 1/4.
            assert a*a*2*tp <= Q(1,16)
            assert 4*tp<=Q(1,16)
            assert tp+Q(1,4)<Q(1,2)<1-tp
            count+=1
    return count

if __name__=="__main__":
    a=short_guard()
    b=visits()
    c=jump_schedule()
    d=guard_geometry()
    e=scale()
    for name,value in zip(("short base outside guard","critical interval visit census",
                           "proper middle jump schedule","local guard geometry",
                           "backward deficit scale"),(a,b,c,d,e)):
        print(f"{name}: {value:,} exact cases")
    print(f"PASS: {a+b+c+d+e:,} exact discrete checks; geometry not certified.")
