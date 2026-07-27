#!/usr/bin/env python3
"""Exact audits for the nested-separator contact method.

Checks:
1. the alternating-attachment rectangle bypass is captured by the current separator;
2. the root-shared mask obeys R_{j+1}=tau_a(R_j cap A_a);
3. exact recursive separator composition agrees with one-shot Kron reduction.

All network arithmetic is rational (SymPy). No pseudoinverse or numerical cutoff is used.
"""
from __future__ import annotations

from dataclasses import dataclass
import json
import random
from pathlib import Path
from typing import Dict, List, Sequence, Set, Tuple

import sympy as sp
from shapely.geometry import box

OUT = Path(__file__).with_name("separator_contact_report.json")


def geom_bypass_check() -> dict:
    D = [
        box(0, 0, 10, 10),
        box(1, 1, 9, 10),
        box(3, 3, 9, 8),
        box(3, 4, 8, 7),
    ]
    # Prefix Ω_2 = int(D0)\D2 and next shell S_3 = int(D2)\D3.
    U2 = D[0].difference(D[2])
    S3 = D[2].difference(D[3])
    contact = U2.boundary.intersection(S3.boundary)
    separator = D[2].boundary
    outside_separator = contact.difference(separator.buffer(1e-9))
    bypass = box(9 - 1e-8, 3, 9 + 1e-8, 8).intersection(contact)
    return {
        "contact_length": float(contact.length),
        "contact_outside_current_separator_length": float(outside_separator.length),
        "known_bypass_arc_detected_length": float(bypass.length),
        "separator_capture_pass": outside_separator.length < 1e-7 and bypass.length > 4.9,
    }


@dataclass(frozen=True)
class Symbol:
    shared: frozenset[int]
    tau: Tuple[int, ...]
    conductance: Tuple[int, ...]


def mask_step(R: Set[int], sym: Symbol) -> Set[int]:
    return {sym.tau[e] for e in R.intersection(sym.shared)}


class DSU:
    def __init__(self) -> None:
        self.parent: Dict[object, object] = {}

    def find(self, x):
        self.parent.setdefault(x, x)
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]

    def union(self, a, b) -> None:
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.parent[rb] = ra


def add_edge(L: sp.Matrix, i: int, j: int, c: sp.Rational) -> None:
    L[i, i] += c
    L[j, j] += c
    L[i, j] -= c
    L[j, i] -= c


def compress_form(
    raw_nodes: Sequence[object],
    dsu: DSU,
    form_entries: Sequence[Tuple[object, object, sp.Rational]],
) -> Tuple[sp.Matrix, Dict[object, int]]:
    reps = sorted({dsu.find(x) for x in raw_nodes}, key=str)
    idx = {r: i for i, r in enumerate(reps)}
    L = sp.zeros(len(reps), len(reps))
    for a, b, value in form_entries:
        ra, rb = dsu.find(a), dsu.find(b)
        L[idx[ra], idx[rb]] += value
    return L, idx


def schur_response(
    L: sp.Matrix,
    ground: int,
    terminals: Sequence[int],
) -> sp.Matrix:
    """Exact grounded response lifted to the labeled terminal list."""
    uniq: List[int] = []
    pos: Dict[int, int] = {}
    lift: List[int | None] = []
    for t in terminals:
        if t == ground:
            lift.append(None)
            continue
        if t not in pos:
            pos[t] = len(uniq)
            uniq.append(t)
        lift.append(pos[t])

    internal = [i for i in range(L.rows) if i != ground and i not in uniq]
    K = L.extract(uniq, uniq)
    if internal:
        B = L.extract(uniq, internal)
        C = L.extract(internal, internal)
        if C.det() == 0:
            raise RuntimeError("Internal grounded block unexpectedly singular")
        K = sp.simplify(K - B * C.inv() * B.T)

    out = sp.zeros(len(terminals), len(terminals))
    for i, pi in enumerate(lift):
        if pi is None:
            continue
        for j, pj in enumerate(lift):
            if pj is not None:
                out[i, j] = K[pi, pj]
    return sp.simplify(out)


def build_full_network(word: Sequence[Symbol], m: int):
    """Build the entire grounded contact-identified network."""
    dsu = DSU()
    root = ("root", 0)
    for e in range(m):
        dsu.union(root, (0, e))

    edge_data: List[Tuple[object, object, sp.Rational]] = []
    raw_nodes: List[object] = [root]
    raw_nodes.extend((0, e) for e in range(m))

    for j, sym in enumerate(word):
        raw_nodes.extend((j + 1, e) for e in range(m))
        for e in range(m):
            parent = (j, e)
            child = (j + 1, sym.tau[e])
            if e in sym.shared:
                dsu.union(parent, child)
            else:
                edge_data.append((parent, child, sp.Rational(sym.conductance[e], 1)))
        # Fixed finite multi-port coupling on the new separator.
        for e in range(m - 1):
            edge_data.append(((j + 1, e), (j + 1, e + 1), sp.Rational(1 + ((j + e) % 3), 2)))

    # Convert resistor edges to Laplacian entries before compressing.
    entries: List[Tuple[object, object, sp.Rational]] = []
    for a, b, c in edge_data:
        entries.extend([(a, a, c), (b, b, c), (a, b, -c), (b, a, -c)])
    L, idx = compress_form(raw_nodes, dsu, entries)
    ground = idx[dsu.find(root)]
    final = [idx[dsu.find((len(word), e))] for e in range(m)]
    return L, ground, final, dsu


def one_shot_response(word: Sequence[Symbol], m: int) -> Tuple[sp.Matrix, List[Set[int]]]:
    L, ground, final, dsu = build_full_network(word, m)
    q = schur_response(L, ground, final)
    root_rep = dsu.find(("root", 0))
    masks = [
        {e for e in range(m) if dsu.find((j, e)) == root_rep}
        for j in range(len(word) + 1)
    ]
    return q, masks


def recursive_step(
    q_parent: sp.Matrix,
    R_parent: Set[int],
    sym: Symbol,
    stage: int,
) -> Tuple[sp.Matrix, Set[int]]:
    """Compose the exact reduced prefix response with one root-normalized cell.

    q_parent is the grounded DtN form on the current labeled separator atoms.
    R_parent records the labels already identified with the fixed root boundary.
    """
    m = q_parent.rows
    dsu = DSU()
    root = ("root", stage)
    parent = [("p", stage, e) for e in range(m)]
    child = [("c", stage, e) for e in range(m)]
    raw_nodes: List[object] = [root, *parent, *child]

    for e in R_parent:
        dsu.union(root, parent[e])
    for e in range(m):
        if e in sym.shared:
            dsu.union(parent[e], child[sym.tau[e]])

    entries: List[Tuple[object, object, sp.Rational]] = []
    # Add the prior exact response form on parent labels. Grounded labels have value zero;
    # after compression, entries incident to ground are retained in the full matrix and then
    # handled by deleting the ground coordinate in the Schur complement.
    for i in range(m):
        for j in range(m):
            if q_parent[i, j] != 0:
                entries.append((parent[i], parent[j], q_parent[i, j]))

    # Add the new cell.
    for e in range(m):
        if e not in sym.shared:
            p = parent[e]
            c = child[sym.tau[e]]
            value = sp.Rational(sym.conductance[e], 1)
            entries.extend([(p, p, value), (c, c, value), (p, c, -value), (c, p, -value)])
    for e in range(m - 1):
        a, b = child[e], child[e + 1]
        value = sp.Rational(1 + ((stage + e) % 3), 2)
        entries.extend([(a, a, value), (b, b, value), (a, b, -value), (b, a, -value)])

    L, idx = compress_form(raw_nodes, dsu, entries)
    ground = idx[dsu.find(root)]
    terminals = [idx[dsu.find(child[e])] for e in range(m)]
    q_child = schur_response(L, ground, terminals)
    R_child = mask_step(R_parent, sym)
    return q_child, R_child


def recursive_response(word: Sequence[Symbol], m: int) -> Tuple[sp.Matrix, List[Set[int]]]:
    q = sp.zeros(m, m)
    R: Set[int] = set(range(m))
    masks = [set(R)]
    for stage, sym in enumerate(word):
        q, R = recursive_step(q, R, sym, stage)
        masks.append(set(R))
    return sp.simplify(q), masks


def random_symbol(rng: random.Random, m: int) -> Symbol:
    shared = frozenset(e for e in range(m) if rng.random() < 0.45)
    perm = list(range(m))
    rng.shuffle(perm)
    conductance = tuple(rng.randint(1, 5) for _ in range(m))
    return Symbol(shared, tuple(perm), conductance)


def exact_network_trials(seed: int = 20260726, trials: int = 250) -> dict:
    rng = random.Random(seed)
    max_diff = sp.Rational(0)
    mask_failures = 0
    for _ in range(trials):
        m = rng.randint(2, 5)
        alphabet = [random_symbol(rng, m), random_symbol(rng, m)]
        word = [rng.choice(alphabet) for _ in range(rng.randint(2, 8))]
        one, actual_masks = one_shot_response(word, m)
        rec, recursive_masks = recursive_response(word, m)
        local_max = max((abs(x) for x in one - rec), default=sp.Rational(0))
        max_diff = max(max_diff, local_max)
        if actual_masks != recursive_masks:
            mask_failures += 1
    return {
        "seed": seed,
        "trials": trials,
        "max_exact_one_shot_vs_recursive_difference": str(max_diff),
        "mask_recurrence_failures": mask_failures,
        "pass": max_diff == 0 and mask_failures == 0,
    }


def main() -> None:
    report = {
        "geometry": geom_bypass_check(),
        "exact_network": exact_network_trials(),
        "interpretation": {
            "what_is_tested": [
                "nonconsecutive bypass contact lies on the current separator",
                "root-shared mask recurrence under shared-boundary transport",
                "exact equality of one-shot Kron reduction and genuinely recursive separator composition",
            ],
            "what_is_not_proved_by_computation": [
                "source authorization of a specific ray/equipotential overlay",
                "Sobolev trace regularity at puzzle vertices",
                "uniform response contraction across unbounded decoration blocks",
                "MBTT, coercivity, rigidity, or MLC",
            ],
        },
    }
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
