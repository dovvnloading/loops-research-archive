#!/usr/bin/env python3
"""Exact finite checks for SUFFIX_ANCHOR_RESPONSE.md, not geometric proofs."""
from fractions import Fraction as Q
from itertools import combinations, product


def covering_square_checks():
    cases = 0
    # C_{r-1} has n grid points, C_0 has m.  A monotone degree-one
    # lift has increments 0 or 1 and total increment m in n steps.
    # Its two-sheet lift has increments repeated twice.
    for n in range(1, 8):
        for m in range(1, min(n, 4) + 1):
            for increases in combinations(range(n), m):
                inc = set(increases)
                for shift in range(m):
                    v = [shift]
                    for i in range(2*n-1):
                        v.append(v[-1] + (i % n in inc))
                    for y in range(n):
                        assert {v[y] % (2*m), v[y+n] % (2*m)} == {
                            v[y] % m, v[y] % m + m}
                    for mask in range(1 << (2*m)):
                        S = {i for i in range(2*m) if mask >> i & 1}
                        actual = {x % n for x in range(2*n) if v[x] % (2*m) in S}
                        image = {s % m for s in S}
                        expected = {y for y in range(n) if v[y] % m in image}
                        assert actual == expected
                        if len(image) == m:
                            assert actual == set(range(n))
                        cases += 1
    return cases


def cyclic_exclusion_checks():
    cases = 0
    for q in range(3, 10):
        for sizes in product((1, 2), repeat=q):
            limb = [k for k, size in enumerate(sizes) for _ in range(size)]
            m = len(limb)
            critical = {i for i, k in enumerate(limb) if k == 0}
            for i, k in enumerate(limb):
                if k != q-1:
                    continue
                for a, k_a in enumerate(limb):
                    if not 1 <= k_a <= q-2:
                        continue
                    arc = {(i+t) % m for t in range(1, (a-i) % m)}
                    assert critical <= arc
                    cases += 1
    return cases


def backward_checks():
    cases = 0
    # Allow every possible stay in the critical limb and every
    # rotational inverse, including paths for which actual dynamics
    # might impose further exclusions.  A noncritical predecessor
    # of a critical point requires an auxiliary at that suffix.
    for h in range(1, 11):
        for q in range(h+2, h+5):
            for choices in product((0, 1), repeat=h):
                route = [0]
                for choose_rotate in choices:
                    route.append((route[-1]-1) % q if choose_rotate else 0)
                route.reverse()
                forced = {j for j in range(h) if route[j+1] == 0 and route[j] != 0}
                assert all(route[j] == q-1 for j in forced)
                assert bool(forced) == any(route)
                for mask in (0, (1 << h)-1, sum(1 << j for j in forced)):
                    aux = {j for j in range(h) if mask >> j & 1}
                    if forced <= aux:
                        assert aux or all(k == 0 for k in route)
                    cases += 1
    return cases


def signed_gap_checks():
    cases = 0
    # Finite signed-crossing identity: sum of signs is one.
    # For every designated primary, either it is a positive gap
    # or a distinct positive candidate exists.  A zero entry means
    # the corresponding gap is not over the anchor.
    for n in range(1, 10):
        for signs in product((-1, 0, 1), repeat=n):
            if sum(signs) != 1:
                continue
            for primary in range(n):
                assert signs[primary] == 1 or any(
                    sign == 1 for i, sign in enumerate(signs) if i != primary)
                cases += 1
    return cases


def series_checks():
    cases = 0
    W = Q(1)
    for N in range(1, 101):
        lam = Q(1, 64*N)
        for E in (Q(0), lam/2, lam):
            for w in (Q(1, 2), Q(3, 4), 1-E):
                for B in (Q(N, 2), Q(N), N*(1+lam), Q(2*N)):
                    primary = W-E+w*w/B
                    assert primary >= W+7*lam
                    assert primary > (1+lam)*W
                    cases += 1
    return cases


if __name__ == '__main__':
    counts = [covering_square_checks(), cyclic_exclusion_checks(),
              backward_checks(), signed_gap_checks(), series_checks()]
    for name, count in zip(('covering fiber square', 'cyclic exclusion',
                           'backward dichotomy', 'signed gaps', 'series scale'), counts):
        print(f'{name}: {count:,} cases')
    print(f'total: {sum(counts):,} finite checks passed')
