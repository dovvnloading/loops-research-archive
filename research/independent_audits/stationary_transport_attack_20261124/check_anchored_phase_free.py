#!/usr/bin/env python3
"""Finite exact checks for the phase-free anchored comparison.

Only the discrete order and width-accounting implications are tested.
No native geometric, modulus or Borel assertion is certified.
"""
from fractions import Fraction as Q
from itertools import product

def probes():
    total=pos=neg=0
    for q in range(4,11):
        for sizes in product((1,2), repeat=q):
            limb=[]; first=[]; last=[]
            for k,size in enumerate(sizes):
                first.append(len(limb))
                limb.extend([k]*size)
                last.append(len(limb)-1)
            m=len(limb)
            # Precompute each actual directed proper base's interior mask.
            arcs=[]
            for s in range(m):
                for span in range(2,m):
                    e=(s+span)%m
                    inside=0
                    for a in range(1,span):
                        inside |= 1<<((s+a)%m)
                    arcs.append((s,e,inside))
            for k in range(1,q):
                for l in range(1,q):
                    if not (l>=k+2 or l<=k-2): continue
                    positive=l>=k+2
                    inc=({first[k+1],last[l-1]} if positive
                         else {first[k-1],last[k-1]})
                    exc=({first[0],last[0],last[k-1]} if positive
                         else {first[0],last[0],first[(k+1)%q],last[l-1]})
                    im=sum(1<<x for x in inc)
                    em=sum(1<<x for x in exc)
                    forbid=im|em
                    for s,e,interior in arcs:
                        if ((1<<s)|(1<<e))&forbid: continue
                        if interior&im != im or interior&em: continue
                        assert limb[s]>0 and limb[e]>0 and s<e
                        if positive:
                            assert limb[s]==k and limb[e]>=l
                            pos+=1
                        else:
                            assert limb[e]==k and l<=limb[s]<=k-2
                            neg+=1
                        total+=1
    return total,pos,neg

def median_loss():
    count=0
    for g,L in product(range(41), repeat=2):
        g,L=Q(g,4),Q(L,4)
        x=g/2
        y=max(Q(0),g/2-L)
        if x*y<=1:
            assert g<=2+2*L
            count+=1
    # Shared union charge, disjoint original support.
    for ns in range(1,5):
        for losses in product(range(4),repeat=ns):
            widths=[2+2*x for x in losses]
            assert sum(widths)==2*ns+2*sum(losses)
            count+=1
    return count

def scale():
    count=0
    for b in range(1,25):
        h=b+2
        K=6*b*(2*b+h+1)+1
        N=h+12*b*2**h
        J=max(12*K,N,2)
        for t in range(1,33):
            sigma=Q(t,32)
            delta=sigma*sigma/(32*J*(h+11)**2)
            lam=delta/2
            assert lam>0 and lam<1
            assert (h+11)**2*2*J*delta==(sigma/4)**2
            assert sigma/4+sigma/4<sigma
            for C,E,Ea,R,Q2,QK,QN in (
                (1,2,3,4,5,6,7),
                (0,1,0,2,0,5,3),
                (3,0,7,1,2,4,6)):
                A=4*K+24*K*C+2*QK
                U=2*C+Q2
                Z=4*C+2*Q2
                B=E+8*K+(48*K+12+2*h)*C+Ea+4*R
                assert E+2*A+2*U+2*Z+h*(2*C+Q2)+Ea+4*R+QN == (
                    B+4*QK+(h+6)*Q2+QN)
                count+=1
    return count

if __name__=="__main__":
    a,p,n=probes()
    b=median_loss()
    c=scale()
    print(f"bounded signed-probe order: {a:,} cases ({p:,} positive, {n:,} negative)")
    print(f"median loss and union accounting: {b:,} cases")
    print(f"anchored near-critical scale: {c:,} cases")
    print(f"PASS: {a+b+c:,} exact discrete checks; geometry not certified.")
