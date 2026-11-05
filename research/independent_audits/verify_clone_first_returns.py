#!/usr/bin/env python3
"""Independently enumerate *all* first-return edge occurrences of delayed clones.

Uses only Python's standard library.  Unlike a numerical eigenvalue test, it
tracks integer path multiplicity in the actual finite directed graph. Gates
are removed from the active path states as soon as they are reached, so only
first returns are counted.

The graph is topologically ordered away from the two gates, making every
gate-avoiding walk finite. Tested lengths are finite diagnostics, *not* a
substitute for a universal Lean proof.
"""
from __future__ import annotations

from collections import Counter


def clone_edges(n: int) -> tuple[int, tuple[int, int], tuple[tuple[int, ...], ...]]:
    if n < 0:
        raise ValueError("n must be nonnegative")
    size = 2 * n + 5
    e, f = 0, n + 3
    # Cyclic order e_0,...,e_n,b,a,f_0,...,f_n,c.
    outgoing = [((i + 1) % size,) for i in range(size)]
    outgoing[n] = (n + 1, n + 2)  # extra shortcut e_n -> a
    # Distinct entries are distinct edge occurrences, not merely endpoints.
    return size, (e, f), tuple(outgoing)


def check_acyclic_between_gates(n: int) -> None:
    size, gates, edges = clone_edges(n)
    gate_set = set(gates)
    # Every edge between nongates strictly increases the vertex index.
    # Thus the gate-avoiding subgraph has no directed cycles.
    for u in range(size):
        if u in gate_set:
            continue
        for v in edges[u]:
            if v in gate_set:
                continue
            assert u < v, (n, u, v)


def first_return_counts(n: int) -> Counter[tuple[int, int, int]]:
    check_acyclic_between_gates(n)
    size, gates, edges = clone_edges(n)
    count: Counter[tuple[int, int, int]] = Counter()
    for source in gates:
        states = Counter({source: 1})
        # With gates excluded from intermediate states, all remaining steps
        # strictly increase the index, so L+1 steps is more than enough.
        for length in range(1, size + 2):
            new_states: Counter[int] = Counter()
            for u, multiplicity in states.items():
                for v in edges[u]:
                    if v in gates:
                        count[(source, v, length)] += multiplicity
                    else:
                        new_states[v] += multiplicity
            states = new_states
            if not states:
                break
        assert not states, ("nonterminating gate-avoiding path", n)
    return count


def expected(n: int) -> Counter[tuple[int, int, int]]:
    _, (e, f), _ = clone_edges(n)
    return Counter({
        (e, f, n + 2): 1,
        (e, f, n + 3): 1,
        (f, e, n + 2): 1,
    })


def main() -> None:
    for n in range(65):
        observed = first_return_counts(n)
        predicted = expected(n)
        assert observed == predicted, {
            "n": n,
            "observed": dict(observed),
            "expected": dict(predicted),
        }
        if n in {0, 1, 2, 4, 8, 16, 32, 64}:
            print(f"n={n:2d}: {dict(sorted(observed.items()))}")

    # At n=0, the two e->f returns have lengths 2 and 3,
    # and f->e has length 2. Hence D*C and D*Q*C add to R.
    zero = first_return_counts(0)
    assert sum(c for (u, v, _), c in zero.items() if (u, v) == (0, 3)) == 2
    assert sum(c for (u, v, _), c in zero.items() if (u, v) == (3, 0)) == 1
    assert all(u != v for u, v, _ in zero)
    print("PASS: 65 exact integer first-return incidence tests, n=0..64")


if __name__ == "__main__":
    main()
