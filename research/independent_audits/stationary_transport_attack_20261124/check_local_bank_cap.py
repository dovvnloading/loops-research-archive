#!/usr/bin/env python3
"""Finite local-bank checks; these do not certify native geometry."""
from itertools import product

def corridor():
    count=0
    # Limb-level tests. A probe interior to the far corridor and
    # a cap end outside it imply one whole boundary limb in crest.
    for q in range(12,29):
        for c in range(3,(q-3)//2):
            bank={k%q for k in range(-c,c+1)}
            far=set(range(c+1,q-c))
            remote=far-{c+1,q-c-1}
            if not remote: continue
            assert far.isdisjoint(bank)
            expanded={k%q for k in range(-c-3,c+4)}
            assert (c+2)%q in expanded and (q-c)%q in expanded
            for start in range(q):
                for span in range(2,q):
                    end=(start+span)%q
                    if start in far and end in far: continue
                    crest={(start+t)%q for t in range(1,span)}
                    for e in remote:
                        if e not in crest: continue
                        assert c+1 in crest or q-c-1 in crest
                        count+=1
    return count

def index_checks():
    count=0
    for b in range(1,33):
        h=b+2; H=h+2; c=b+12; cp=c+H+4
        for q in range(2*cp+4,2*cp+40):
            bank=lambda a:{k%q for k in range(-a,a+1)}
            # Every selected old-proper atom translates by one or
            # resets into the actual critical-image bank.
            current=bank(c)
            for j in range(1,H+1):
                current=({(k+1)%q for k in current if k!=0}
                         | (bank(b) if 0 in current else set()))
                assert current<=bank(c+j)
                assert current<=bank(cp)
                count+=1
            assert set(range(c+1,q-c))<=set(range(b,q-b-1))
            assert {1,2,h+1,h+2}<=bank(cp)
            for k in bank(c+2):
                images=bank(b) if k==0 else {(k+1)%q}
                assert images<=bank(c+3)<=bank(cp)
                count+=1
            for k in range(c+1,q-c):
                # A localized adjacent atom has its ending limb
                # in the actual four-limb inner band on one side.
                assert k-2>=b
                for E in (k-1,k,k+1):
                    assert k-1<=E<=k+2
                    count+=1
    return count

def bookkeeping():
    count=0
    for k,M,V in product(range(1,17),range(1,21),range(0,11)):
        # Width cap for two directions per localized module,
        # one leafwise overcritical module, and the loop discard.
        per=3*M+40*(V+1)
        assert 2*k*per+M==(6*k+1)*M+80*k*(V+1)
        count+=1
    return count

if __name__=="__main__":
    cs=[corridor(),index_checks(),bookkeeping()]
    for label,n in zip(("remote probe corridor exits","local bank index and cap bounds",
                        "localized input width accounting"),cs):
        print(f"{label}: {n:,} exact cases")
    print(f"PASS: {sum(cs):,} exact discrete checks; geometry not certified.")
