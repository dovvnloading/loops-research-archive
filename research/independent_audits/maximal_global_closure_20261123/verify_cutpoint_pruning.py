#!/usr/bin/env python3
"""Exact finite checks for CUTPOINT_PRUNING.md; no analytic conclusion.

Run from any directory with Python 3, using only the standard library.
The proof is in the note.  Here the hull is computed by leaf pruning,
independently of the cut-component test in the asserted conclusion.
"""

from itertools import product
import json


def labelled_trees(n):
    if n == 1:
        yield [set()]
        return
    for word in product(range(n), repeat=n - 2):
        degree = [1] * n
        for v in word:
            degree[v] += 1
        graph = [set() for _ in range(n)]
        for v in word:
            u = next(i for i in range(n) if degree[i] == 1)
            graph[u].add(v)
            graph[v].add(u)
            degree[u] -= 1
            degree[v] -= 1
        u, v = [i for i, d in enumerate(degree) if d == 1]
        graph[u].add(v)
        graph[v].add(u)
        yield graph


def hull(graph, marked):
    retained = set(range(len(graph)))
    while True:
        leaves = {
            v for v in retained - marked
            if len(graph[v] & retained) <= 1
        }
        if not leaves:
            return retained
        retained -= leaves


def components(graph, excluded):
    unseen = set(range(len(graph))) - excluded
    answer = []
    while unseen:
        component = {min(unseen)}
        queue = list(component)
        unseen -= component
        while queue:
            v = queue.pop()
            fresh = graph[v] & unseen
            unseen -= fresh
            component |= fresh
            queue.extend(fresh)
        answer.append(component)
    return answer


def contract_edges(graph, selected_edges):
    parent = list(range(len(graph)))

    def find(v):
        while parent[v] != v:
            v = parent[v]
        return v

    for u, v in selected_edges:
        parent[find(u)] = find(v)
    roots = sorted({find(v) for v in range(len(graph))})
    labels = {r: i for i, r in enumerate(roots)}
    q = [labels[find(v)] for v in range(len(graph))]
    quotient = [set() for _ in roots]
    for u, adj in enumerate(graph):
        for v in adj:
            if q[u] != q[v]:
                quotient[q[u]].add(q[v])
    return q, quotient


def main():
    tree_count = incidence_checks = contraction_checks = 0
    for n in range(1, 7):
        for graph in labelled_trees(n):
            tree_count += 1
            edges = [(u, v) for u, adj in enumerate(graph) for v in adj if u < v]
            for mask in range(1, 1 << n):
                marked = {v for v in range(n) if mask & (1 << v)}
                minimal = hull(graph, marked)
                for a in set(range(n)) - marked:
                    for branch in components(graph, {a}):
                        assert bool(minimal & branch) == bool(marked & branch)
                        incidence_checks += 1
                if n > 5:
                    continue
                for edge_mask in range(1 << len(edges)):
                    contracted = [e for i, e in enumerate(edges) if edge_mask & (1 << i)]
                    q, quotient = contract_edges(graph, contracted)
                    image_marks = {q[v] for v in marked}
                    image_hull = hull(quotient, image_marks)
                    full_lift = {v for v in range(n) if q[v] in image_hull}
                    for a in set(range(n)) - marked:
                        if sum(q[v] == q[a] for v in range(n)) != 1:
                            continue
                        for branch in components(graph, {a}):
                            assert bool(full_lift & branch) == bool(marked & branch)
                            intersection = full_lift & branch
                            if intersection:
                                remaining = components(graph, set(range(n)) - intersection)
                                assert len(remaining) == 1
                            contraction_checks += 1

    # A non-singleton cut fiber makes full-hull terminal pruning false.
    triod = [{1, 2, 3}, {0}, {0}, {0}]
    marked = {1, 2}
    q, quotient = contract_edges(triod, [(0, 3)])
    image_hull = hull(quotient, {q[v] for v in marked})
    full_lift = {v for v in range(4) if q[v] in image_hull}
    bad_branch = {3}
    assert q[0] == q[3]
    assert full_lift & bad_branch
    assert not marked & bad_branch
    print(json.dumps({
        "status": "PASS",
        "labelled_trees_through_six_vertices": tree_count,
        "terminal_incidence_checks": incidence_checks,
        "singleton_fiber_contraction_checks_through_five_vertices": contraction_checks,
        "non_singleton_triod_fails_as_expected": True,
        "scope": "finite combinatorial regression only; continuum proofs are written",
    }, indent=2))


if __name__ == "__main__":
    main()
