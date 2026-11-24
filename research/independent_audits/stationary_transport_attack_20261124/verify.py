#!/usr/bin/env python3
"""Exact primal/dual checks for the variable-end modulus accounting.

These finite certificates check the endpoint-budget algebra, not existence
of native stationary exits or realization of the example widths by a surface.
No floating point, optimizer, symbolic enumeration of paths, or external package.
"""

from fractions import Fraction as Q
from itertools import combinations


def verify_cover(capacities, edges, dual, primal):
    """Check fractional-cover feasibility and a matching optimum witness.

    None capacity denotes an uncharged endpoint (e.g. an outer exit): its
    coefficient must be zero, and it supplies no local-width constraint.
    """
    n = len(capacities)
    assert len(dual) == n and len(primal) == len(edges)
    assert all(a >= 0 for a in dual)
    assert all(x >= 0 for x in primal)
    used = [Q(0) for _ in range(n)]
    normalized = set()
    for (u, v), x in zip(edges, primal):
        assert 0 <= u < v < n, "self-returns and reversed edges are not exits"
        assert (u, v) not in normalized, "repeated endpoint-pair entry"
        normalized.add((u, v))
        assert dual[u] + dual[v] >= 1, "uncovered occurring endpoint pair"
        used[u] += x
        used[v] += x
    cost = Q(0)
    for cap, a, amount in zip(capacities, dual, used):
        if cap is None:
            assert a == 0, "uncharged end cannot supply a width estimate"
        else:
            assert cap >= 0 and amount <= cap, "endpoint width budget exceeded"
            cost += cap * a
    assert sum(primal) == cost, "primal and dual do not certify the same optimum"
    return cost


def verify_degree_census(degree, target_partitions):
    """Each full inverse target end must use exactly the covering degree."""
    assert isinstance(degree, int) and degree > 0
    for parts in target_partitions:
        assert parts and all(isinstance(d, int) and d > 0 for d in parts)
        assert sum(parts) == degree, "hidden peripheral-degree overspend or omission"
    return sum(map(sum, target_partitions))


def rejected(label, operation):
    try:
        operation()
    except AssertionError:
        return label
    raise AssertionError(f"invalid certificate was accepted: {label}")


def main():
    # One fixed degree-two end supplies the entire estimate.
    fixed = verify_cover([Q(2), Q(1), Q(1), Q(1)],
                         [(0, 1), (0, 2), (0, 3)],
                         [Q(1), Q(0), Q(0), Q(0)],
                         [Q(1), Q(1), Q(0)])
    assert fixed == 2

    # Four degree-two bank ends; the other endpoint is uncharged outer.
    bank = verify_cover([Q(2)] * 4 + [None],
                        [(j, 4) for j in range(4)],
                        [Q(1)] * 4 + [Q(0)], [Q(2)] * 4)
    assert bank == 8

    # If every exit is inner-bank, a half-cover halves that budget.
    pairs = list(combinations(range(4), 2))
    cycle = {(0, 1), (1, 2), (2, 3), (0, 3)}
    inner = verify_cover([Q(2)] * 4, pairs, [Q(1, 2)] * 4,
                         [Q(int(e in cycle)) for e in pairs])
    assert inner == 4

    triangle = list(combinations(range(3), 2))
    odd = verify_cover([Q(1)] * 3, triangle,
                       [Q(1, 2)] * 3, [Q(1, 2)] * 3)
    integral = min(sum((mask >> v) & 1 for v in range(3))
                   for mask in range(8)
                   if all((mask >> u) & 1 or (mask >> v) & 1
                          for u, v in triangle))
    assert odd == Q(3, 2) < integral == 2

    # Different component counts can have the same full degree budget.
    census = verify_degree_census(8, [[1, 1, 2, 4], [8]])
    assert census == 2 * 8
    failures = [
        rejected("missing edge constraint", lambda: verify_cover(
            [Q(1)] * 3, triangle, [Q(1), Q(0), Q(0)], [Q(0)] * 3)),
        rejected("hidden degree overspend", lambda: verify_degree_census(8, [[5, 4]])),
        rejected("uncharged outer used as a bound", lambda: verify_cover(
            [Q(2), None], [(0, 1)], [Q(0), Q(1)], [Q(0)])),
        rejected("self-return mislabeled as an exit", lambda: verify_cover(
            [Q(1)], [(0, 0)], [Q(1)], [Q(1)])),
    ]
    print("PASS: exact fixed-end, variable-bank, inner-bank, triangle, and degree certificates")
    print(f"Budgets in units of R: fixed={fixed}, variable={bank}, inner={inner}, triangle={odd}")
    print("Rejected: " + "; ".join(failures))
    print("Scope: finite endpoint-accounting certificates; native exit existence remains open")


if __name__ == "__main__":
    main()
