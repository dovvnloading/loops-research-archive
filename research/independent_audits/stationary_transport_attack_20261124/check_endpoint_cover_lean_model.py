#!/usr/bin/env python3
"""Independent exact regression of the finite real-valued Lean interface.

This is an enumerated sanity check, not a substitute for kernel checking
the universal theorem, or a proof of any analytic realization premise.
"""
from fractions import Fraction as Q
from itertools import product, combinations


def main():
    edges = list(combinations(range(3), 2))
    checked = 0
    for x in product(range(3), repeat=len(edges)):
        load = [sum(w for e, w in zip(edges, x) if j in e)
                for j in range(3)]
        for a in product([Q(0), Q(1, 2), Q(1)], repeat=3):
            if any(a[u] + a[v] < 1 for u, v in edges):
                continue
            for slack in product(range(2), repeat=3):
                # Deliberately invalid real capacity at uncharged ends.
                # No incidence inequality may be needed there.
                L = [load[j] + slack[j] if a[j] > 0 else -100
                     for j in range(3)]
                weighted = sum(a[j] * load[j] for j in range(3))
                assert weighted == sum(
                    (a[u] + a[v]) * w for (u, v), w in zip(edges, x))
                assert sum(x) <= weighted <= sum(
                    a[j] * L[j] for j in range(3))
                checked += 1
    assert checked == 2376
    print(f"PASS: {checked} exact assignments, including uncharged ends")

    # Reproduce the four sharp configurations in the source note without
    # using its certificate checker.
    pairs = list(combinations(range(4), 2))
    cycle = {(0, 1), (1, 2), (2, 3), (0, 3)}
    cases = [
        ("fixed", 4, [(0, 1), (0, 2), (0, 3)], [1, 1, 0],
         [1, 0, 0, 0], [2, 1, 1, 1], Q(2)),
        ("variable", 5, [(j, 4) for j in range(4)], [2] * 4,
         [1] * 4 + [0], [2] * 4 + [None], Q(8)),
        ("inner", 4, pairs, [int(e in cycle) for e in pairs],
         [Q(1, 2)] * 4, [2] * 4, Q(4)),
        ("triangle", 3, edges, [Q(1, 2)] * 3,
         [Q(1, 2)] * 3, [1] * 3, Q(3, 2)),
    ]
    for name, n, pairs, x, a, L, expected in cases:
        assert all(u != v and a[u] + a[v] >= 1 for u, v in pairs)
        load = [sum(w for e, w in zip(pairs, x) if j in e)
                for j in range(n)]
        assert all(not a[j] or (L[j] is not None and load[j] <= L[j])
                   for j in range(n))
        assert sum(x) == sum(a[j] * L[j] for j in range(n) if a[j]) == expected
        print(f"PASS: {name}: {expected}")


if __name__ == "__main__":
    main()
