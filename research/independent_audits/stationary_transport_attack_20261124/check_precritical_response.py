#!/usr/bin/env python3
"""Exact finite tests for PRECRITICAL_TERMINAL_RESPONSE.md."""
from fractions import Fraction as Q
from itertools import product


def short_block_checks():
    # Discrete circle of circumference 2m. The pulled precritical
    # block has length < m, and the cap has span < m/2 (confinement).
    # A cap containing both end atoms must run through the block.
    cases = 0
    for m in range(4, 19):
        for k in range(1, m):
            block = set(range(k))
            for first, last in product(range(1, k+1), repeat=2):
                if first + last > k and first != k and last != k:
                    continue
                E = set(range(first)) | set(range(k-last, k))
                for a in range(2*m):
                    for length in range(1, (m+1)//2):
                        cap = {(a+i) % (2*m) for i in range(length)}
                        if E <= cap:
                            assert block <= cap
                        cases += 1
    return cases


def deck_chart_checks():
    cases = 0
    for n in range(8, 101, 8):
        # half-turn deck mate; open radius n/8 gives disjoint charts
        for a in range(n):
            b = (a+n//2) % n
            chart = lambda e: {x for x in range(n)
                               if min((x-e) % n, (e-x) % n) < n//8}
            assert chart(a).isdisjoint(chart(b))
            assert {x % (n//2) for x in chart(a)} == {x % (n//2) for x in chart(b)}
            cases += 1
    return cases


def precritical_mix_checks():
    cases = 0
    W = Q(1)
    for n in range(1, 61):
        lam = Q(1, 512*n)
        cap = (1+lam)*W
        for k in range(9):
            D = cap*Q(k, 8)
            for l in range(9):
                O = (cap-D)*Q(l, 8)
                for L in (Q(0), Q(1, 128), Q(1, 16)):
                    if O > cap/2 + L:
                        continue
                    assert D/2 + O <= 3*cap/4 + L/2
                    cases += 1
    return cases


def integrated_scale_checks():
    cases = 0
    W = Q(1)
    for n in range(1, 101):
        lam = Q(1, 512*n)
        for E in (Q(0), lam/2, lam):
            for L in (E, Q(1, 32), Q(1, 16)):
                w = W-3*(1+lam)*W/4-L
                assert w >= W/8
                for B in (Q(n, 2), Q(n), n*(1+lam), Q(2*n)):
                    primary = W-E+w*w/B
                    assert primary >= W+3*lam
                    assert primary > (1+lam)*W
                    cases += 1
    return cases


if __name__ == '__main__':
    counts = [short_block_checks(), deck_chart_checks(),
              precritical_mix_checks(), integrated_scale_checks()]
    for name, count in zip(('short pulled block', 'deck charts',
                           'precritical mixture', 'integrated response'), counts):
        print(f'{name}: {count:,} cases')
    print(f'total: {sum(counts):,} finite checks passed')
