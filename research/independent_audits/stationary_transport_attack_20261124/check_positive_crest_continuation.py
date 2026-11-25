"""Exact finite checks for the conditional positive-crest continuation.

These check width bookkeeping, not the native geometric hypotheses.
All quantities are normalized by the positive input width W.
"""
from fractions import Fraction as F
from itertools import product


def recurrence():
    n = 0
    # Actual discard c, surviving source mass, double mass, and output.
    # Only the double portion is lost after the anchor pruning.
    for l, c, lam, good, double in product(range(11), repeat=5):
        l, c, lam, good, double = map(lambda x: F(x, 10), (l,c,lam,good,double))
        if good < 1-l-c or double > good or good+double > 1+lam:
            continue
        assert double <= l+c+lam
        assert good-double >= 1-(2*l+2*c+lam)
        n += 1
    return n


def scale():
    n = 0
    for h in range(3, 18):
        b = h-2
        N = h+12*b*2**h
        tau = F(1, 65536*N)
        lam = tau/2**(h+2)
        # V and C_2 chosen inside the absolute-scale premise.
        for i, j in product(range(11), repeat=2):
            if i+j > 10:
                continue
            V = (tau/2)*F(i, 10)/2**(2*h+1)
            C = (tau/2)*F(j, 10)/(4*(2**h-1)+1)
            A = 2**(2*h+1)*V+4*(2**h-1)*C
            assert A+C <= tau/2
            L = 2**(h+1)*V
            for k in range(h+1):
                assert L == 2**(k+h+1)*V+(2**k-1)*(4*C+lam)
                assert L+C <= tau
                if k < h:
                    L = 2*L+4*C+lam
                n += 1
            # Avoid square roots: the upper bound on the squared
            # post-pruning over-critical fraction is strictly below
            # the square of the target fraction minus its discard.
            assert F(1,32)-3*C > 0
            assert 2*(1+lam)*(lam+L+C) < (F(1,32)-3*C)**2
            assert L+F(3,4)*lam <= F(1,32)
            # Entire remaining auxiliary fraction after the three losses.
            w = 1-F(3,4)*(1+lam)-L-F(1,32)-F(1,32)
            assert w >= F(1,8)
            assert 1-L+w*w/(2*N) > 1+lam
            # Small q: the whole stopped packet has the mixed cap.
            assert 1-L > F(3,4)*(1+lam)+F(1,32)
            n += 5
    return n


if __name__ == '__main__':
    r, s = recurrence(), scale()
    print(f'Positive crest recurrence: {r:,} exact cases')
    print(f'Integrated scale: {s:,} exact cases')
    print(f'PASS: {r+s:,} exact cases; geometric premises are not tested.')
