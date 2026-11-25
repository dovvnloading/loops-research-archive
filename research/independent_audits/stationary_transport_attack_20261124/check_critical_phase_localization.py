#!/usr/bin/env python3
"""Exact finite phase-localization and alternative-window regressions.

These test only the discrete circle/configuration implications, not
actual prime ends, raw windows, conformal metrics, or native dynamics.
"""
from itertools import combinations, product
from fractions import Fraction as Q


def localization_checks():
    # Target circle with n equal cells, BL1 represented by a proper
    # consecutive run of cells (normalize its first cell to zero).
    # Source circumference 2n, with one injective translated corridor
    # [k,n] in the lift, where BL1=(0,k).
    count = 0
    for n in range(2, 13):
        for k in range(1, n):
            corridor = set(range(k, n))
            omitted = set(range(k))
            for start in range(n):
                for end in range(n):
                    if start == end:
                        continue
                    e = end if end > start else end+n
                    arc = set(range(start,e+1))
                    phase_intersections = [
                        {x % (2*n) for x in range(start+s*n,e+1+s*n)}
                        & corridor for s in (0,1)]
                    both = all(phase_intersections)
                    # Whole BL1 strictly between the end cells when
                    # both phase intervals contain noncritical cells.
                    middle = {x % n for x in range(start+1,e)}
                    if both:
                        assert start in corridor and end in corridor
                        assert omitted <= middle
                    count += 1
    return count


def configurations(pairs):
    return [set(zip(range(pairs), bits))
            for bits in product((0,1), repeat=pairs)]


def eligible_sets(pairs):
    types = [(c,s) for c in range(pairs) for s in (0,1)]
    return [set(x) for j in range(1,len(types)+1)
            for x in combinations(types,j)]


def exchange_and_expectation():
    count = 0
    # Exhaust pairs of distinct nonempty label sets with rational
    # integer width weights, on 1--3 directed cell pairs.
    for p in range(1,4):
        configs = configurations(p)
        sets = eligible_sets(p)
        for L1,L2 in combinations(sets,2):
            for w1,w2 in product((1,2,3), repeat=2):
                labels = (L1,L2)
                weights = (w1,w2)
                def covered(conf):
                    return {i for i,L in enumerate(labels) if L & conf}
                def width(ids):
                    return sum(weights[i] for i in ids)
                values = [width(covered(conf)) for conf in configs]
                best_index = max(range(len(configs)), key=lambda j: values[j])
                best = configs[best_index]
                kept = covered(best)
                lost = set(range(2))-kept
                delta = width(lost)
                for c in range(p):
                    s = next(s for c0,s in best if c0 == c)
                    t = 1-s
                    U = {i for i in lost if (c,t) in labels[i]}
                    P = {i for i in kept if labels[i]&best == {(c,s)}
                         and (c,t) not in labels[i]}
                    alt = best-{(c,s)}|{(c,t)}
                    assert covered(alt)-kept == U
                    assert kept-covered(alt) == P
                    assert width(U) <= width(P)
                    count += 1
                expected = Q(sum(sum(weights)-v for v in values), len(values))
                formula = Q(0)
                for i,L in enumerate(labels):
                    if any({(c,0),(c,1)} <= L for c in range(p)):
                        continue
                    r = len({c for c,s in L})
                    formula += Q(weights[i],2**r)
                assert delta <= expected == formula
                # A fixed one-label selection cannot beat the optimum.
                for t1,t2 in product(sorted(L1),sorted(L2)):
                    fixed = sum(weights)-max(
                        sum(w for w,t in zip(weights,(t1,t2)) if t in conf)
                        for conf in configs)
                    assert delta <= fixed
                    count += 1
    return count


def explicit_conflict_and_repair():
    labels = [{(0,0)}, {(0,1)}]
    assert max(sum(bool(L&conf) for L in labels)
               for conf in configurations(1)) == 1
    labels[1].add((1,0))  # a genuinely realized alternative type
    assert max(sum(bool(L&conf) for L in labels)
               for conf in configurations(2)) == 2
    labels = [{(0,0),(0,1)}]  # both lifts of a singleton: always covered
    assert all(labels[0]&conf for conf in configurations(1))
    return 3


if __name__ == '__main__':
    a = localization_checks()
    b = exchange_and_expectation()
    c = explicit_conflict_and_repair()
    print(f'critical-bank finite localization: {a:,} cases')
    print(f'alternative labels and exact phase exchanges: {b:,} cases')
    print(f'conflict/repair controls: {c:,} cases')
    print(f'PASS: {a+b+c:,} exact discrete checks; geometry is not certified.')
