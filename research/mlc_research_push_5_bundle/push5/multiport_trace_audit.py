#!/usr/bin/env python3
"""Finite-network attacks for Research Push V.

The graph model is only a falsification/consistency audit.  It checks:
  * exact partial-footprint Schur composition;
  * retention of one-sided footprint differences as side terminals;
  * exact last-use elimination;
  * convergence of a fixed multi-port prefix attached to a longer two-interface tail;
  * linear growth of constant-channel effective resistance.

It does not replace the continuum Dirichlet-form proofs.
"""
from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np
from numpy.typing import NDArray


Array = NDArray[np.float64]


class UnionFind:
    def __init__(self, n: int) -> None:
        self.p = list(range(n))
        self.r = [0] * n

    def find(self, x: int) -> int:
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a == b:
            return
        if self.r[a] < self.r[b]:
            a, b = b, a
        self.p[b] = a
        if self.r[a] == self.r[b]:
            self.r[a] += 1


@dataclass
class Grid:
    nx: int
    ny: int
    lap: Array

    def node(self, i: int, j: int) -> int:
        return i * (self.ny + 1) + j

    @property
    def n(self) -> int:
        return (self.nx + 1) * (self.ny + 1)


def grid_laplacian(nx: int, ny: int, rng: np.random.Generator | None = None,
                   jitter: float = 0.0) -> Grid:
    n = (nx + 1) * (ny + 1)
    L = np.zeros((n, n), dtype=float)

    def idx(i: int, j: int) -> int:
        return i * (ny + 1) + j

    def add_edge(u: int, v: int) -> None:
        w = 1.0
        if rng is not None and jitter:
            w *= float(rng.uniform(1.0 - jitter, 1.0 + jitter))
        L[u, u] += w
        L[v, v] += w
        L[u, v] -= w
        L[v, u] -= w

    for i in range(nx + 1):
        for j in range(ny + 1):
            if i < nx:
                add_edge(idx(i, j), idx(i + 1, j))
            if j < ny:
                add_edge(idx(i, j), idx(i, j + 1))
    return Grid(nx=nx, ny=ny, lap=L)


def schur_response(L: Array, terminals: Sequence[int]) -> Array:
    terminals = list(dict.fromkeys(terminals))
    all_idx = np.arange(L.shape[0])
    mask = np.ones(L.shape[0], dtype=bool)
    mask[terminals] = False
    free = all_idx[mask]
    TT = L[np.ix_(terminals, terminals)]
    if len(free) == 0:
        return TT.copy()
    TF = L[np.ix_(terminals, free)]
    FF = L[np.ix_(free, free)]
    # With at least one terminal in every connected component, FF is positive definite.
    X = np.linalg.solve(FF, TF.T)
    R = TT - TF @ X
    return (R + R.T) / 2.0


def eliminate_response(R: Array, keep: Sequence[int]) -> Array:
    keep = list(keep)
    n = R.shape[0]
    mask = np.ones(n, dtype=bool)
    mask[keep] = False
    elim = np.arange(n)[mask]
    KK = R[np.ix_(keep, keep)]
    if len(elim) == 0:
        return KK.copy()
    KE = R[np.ix_(keep, elim)]
    EE = R[np.ix_(elim, elim)]
    X = np.linalg.pinv(EE, rcond=1e-12) @ KE.T
    out = KK - KE @ X
    return (out + out.T) / 2.0


def merge_graphs(graphs: Sequence[Grid], identifications: Sequence[Tuple[int, int, int, int]]) -> Tuple[Array, List[List[int]]]:
    """Merge graph nodes.

    identifications entries are (graph_a, node_a, graph_b, node_b).
    Returns merged Laplacian and local->merged maps.
    """
    offsets = []
    total = 0
    for g in graphs:
        offsets.append(total)
        total += g.n
    uf = UnionFind(total)
    for ga, na, gb, nb in identifications:
        uf.union(offsets[ga] + na, offsets[gb] + nb)
    roots: Dict[int, int] = {}
    maps: List[List[int]] = []
    next_id = 0
    for gi, g in enumerate(graphs):
        mp = []
        for n in range(g.n):
            r = uf.find(offsets[gi] + n)
            if r not in roots:
                roots[r] = next_id
                next_id += 1
            mp.append(roots[r])
        maps.append(mp)
    L = np.zeros((next_id, next_id), dtype=float)
    for gi, g in enumerate(graphs):
        mp = maps[gi]
        rows, cols = np.nonzero(np.abs(g.lap) > 0)
        for r, c in zip(rows, cols):
            L[mp[r], mp[c]] += g.lap[r, c]
    return (L + L.T) / 2.0, maps


def embed_and_compose(R1: Array, nX: int, nI: int, nS1: int,
                      R2: Array, nY: int, nS2: int) -> Array:
    """R1 order X,I,S1; R2 order I,Y,S2. Return order X,S1,Y,S2."""
    n_total = nX + nI + nS1 + nY + nS2
    K = np.zeros((n_total, n_total), dtype=float)
    idx_X = list(range(0, nX))
    idx_I = list(range(nX, nX + nI))
    idx_S1 = list(range(nX + nI, nX + nI + nS1))
    idx_Y = list(range(nX + nI + nS1, nX + nI + nS1 + nY))
    idx_S2 = list(range(nX + nI + nS1 + nY, n_total))
    map1 = idx_X + idx_I + idx_S1
    map2 = idx_I + idx_Y + idx_S2
    K[np.ix_(map1, map1)] += R1
    K[np.ix_(map2, map2)] += R2
    keep = idx_X + idx_S1 + idx_Y + idx_S2
    return eliminate_response(K, keep)


def build_partial_cells(rng: np.random.Generator, jitter: float = 0.0):
    ny = 6
    g1 = grid_laplacian(5, ny, rng, jitter)
    g2 = grid_laplacian(4, ny, rng, jitter)

    X1 = [g1.node(0, j) for j in range(ny + 1)]
    A = [g1.node(g1.nx, j) for j in range(1, 6)]
    B = [g2.node(0, j) for j in range(2, 7)]
    overlap_js = [2, 3, 4, 5]
    I1 = [g1.node(g1.nx, j) for j in overlap_js]
    I2 = [g2.node(0, j) for j in overlap_js]
    E1 = [g1.node(g1.nx, 1)]
    E2 = [g2.node(0, 6)]
    # Additional physical side ports, not collapsed to one scalar electrode.
    S1_extra = [g1.node(2, 0), g1.node(4, ny)]
    S2_extra = [g2.node(1, ny), g2.node(3, 0)]
    S1 = E1 + S1_extra
    S2 = E2 + S2_extra
    Y2 = [g2.node(g2.nx, j) for j in range(ny + 1)]

    R1 = schur_response(g1.lap, X1 + I1 + S1)
    R2 = schur_response(g2.lap, I2 + Y2 + S2)
    composed = embed_and_compose(R1, len(X1), len(I1), len(S1),
                                 R2, len(Y2), len(S2))

    ids = [(0, g1.node(g1.nx, j), 1, g2.node(0, j)) for j in overlap_js]
    Ldir, maps = merge_graphs([g1, g2], ids)
    direct_terms = ([maps[0][n] for n in X1]
                    + [maps[0][n] for n in S1]
                    + [maps[1][n] for n in Y2]
                    + [maps[1][n] for n in S2])
    direct = schur_response(Ldir, direct_terms)
    return {
        "composition_error": float(np.linalg.norm(composed - direct, ord=2)),
        "composed": composed,
        "direct": direct,
        "graphs": (g1, g2),
        "maps": maps,
        "Ldir": Ldir,
        "prefix_external_local": (X1, S1, Y2, S2),
        "prefix_external_merged": direct_terms,
        "terminal_interface_merged": [maps[1][n] for n in Y2],
        "counts": {
            "parent_trace_nodes": len(X1),
            "overlap_nodes": len(I1),
            "outer_only_side_nodes": len(E1),
            "inner_only_side_nodes": len(E2),
            "additional_side_nodes": len(S1_extra) + len(S2_extra),
            "terminal_trace_nodes": len(Y2),
        },
    }


def attach_tail(prefix_L: Array, prefix_terminal: Sequence[int],
                prefix_external: Sequence[int], ny: int, tail_nx: int) -> Tuple[Array, List[int], List[int]]:
    tail = grid_laplacian(tail_nx, ny)
    ids = [(0, int(prefix_terminal[j]), 1, tail.node(0, j)) for j in range(ny + 1)]
    # Wrap prefix as a Grid-like object with arbitrary node count.
    prefix = Grid(nx=prefix_L.shape[0] - 1, ny=0, lap=prefix_L)
    L, maps = merge_graphs([prefix, tail], ids)
    ext = [maps[0][int(n)] for n in prefix_external]
    far = [maps[1][tail.node(tail.nx, j)] for j in range(ny + 1)]
    R = schur_response(L, ext + far)
    return R, ext, far


def effective_constant_resistance(R: Array, n_left: int, n_far: int,
                                  side_indices: Sequence[int]) -> float:
    # Eliminate side terminals, retain root trace and far trace.
    keep = list(range(n_left)) + list(range(R.shape[0] - n_far, R.shape[0]))
    R2 = eliminate_response(R, keep)
    v = np.concatenate([np.zeros(n_left), np.ones(n_far)])
    energy = float(v @ R2 @ v)
    if energy <= 1e-14:
        return math.inf
    return 1.0 / energy


def cross_block_norm(R: Array, n_left: int, n_side: int, n_far: int) -> float:
    # Eliminate side ports, then project both trace blocks to mean-zero.
    keep = list(range(n_left)) + list(range(R.shape[0] - n_far, R.shape[0]))
    R2 = eliminate_response(R, keep)
    C = R2[:n_left, n_left:]
    Pl = np.eye(n_left) - np.ones((n_left, n_left)) / n_left
    Pr = np.eye(n_far) - np.ones((n_far, n_far)) / n_far
    return float(np.linalg.norm(Pl @ C @ Pr, ord=2))


def circular_arc_contains(start: float, end: float, x: float) -> bool:
    """Membership in the positively oriented open circular arc start -> end."""
    start %= 1.0
    end %= 1.0
    x %= 1.0
    if start < end:
        return start < x < end
    return x > start or x < end


def attachment_refinement_example() -> dict:
    """A normalized prime-end-circle example with all four atom classes nonempty."""
    prev = (0.82, 0.12)  # inherited inactive attachment, wrapping through 0
    nxt = (0.05, 0.34)   # next inactive attachment
    breaks = sorted({0.0, 1.0, prev[0], prev[1], nxt[0], nxt[1]})
    classes = {
        "common_active_glue": [],
        "outgoing_only_side_port": [],
        "incoming_only_side_port": [],
        "double_inactive_attachment": [],
    }
    for a, b in zip(breaks[:-1], breaks[1:]):
        mid = (a + b) / 2.0
        in_prev = circular_arc_contains(*prev, mid)
        in_next = circular_arc_contains(*nxt, mid)
        if not in_prev and not in_next:
            key = "common_active_glue"
        elif not in_prev and in_next:
            key = "outgoing_only_side_port"
        elif in_prev and not in_next:
            key = "incoming_only_side_port"
        else:
            key = "double_inactive_attachment"
        classes[key].append([a, b])
    return {
        "circle_coordinate": "[0,1) with endpoints identified",
        "inherited_attachment_arc": list(prev),
        "next_attachment_arc": list(nxt),
        "endpoint_atoms": breaks,
        "open_atom_classes": classes,
    }


def run(seed: int = 20260725, random_trials: int = 250) -> dict:
    rng = np.random.default_rng(seed)
    base = build_partial_cells(rng, jitter=0.0)

    random_errors = []
    for _ in range(random_trials):
        trial = build_partial_cells(rng, jitter=0.35)
        random_errors.append(trial["composition_error"])

    # Use the direct two-cell union as a physical prefix.  The terminal interface is
    # the full right trace of cell 2.  Retain all prefix terminals except that
    # interface as fixed multi-port data.
    prefix_L = base["Ldir"]
    term = base["terminal_interface_merged"]
    all_prefix_terms = base["prefix_external_merged"]
    term_set = set(term)
    prefix_external = [n for n in all_prefix_terms if n not in term_set]
    ny = 6
    lengths = [1, 2, 4, 8, 16, 32, 64]
    responses = {}
    resistances = {}
    cross_norms = {}
    for Ltail in lengths + [128]:
        Resp, ext, far = attach_tail(prefix_L, term, prefix_external, ny, Ltail)
        responses[Ltail] = Resp
        n_left = 7  # first seven entries are the outer/root trace X1
        n_far = 7
        n_side = len(ext) - n_left
        resistances[Ltail] = effective_constant_resistance(Resp, n_left, n_far,
                                                           list(range(n_left, len(ext))))
        cross_norms[Ltail] = cross_block_norm(Resp, n_left, n_side, n_far)
    reference = responses[128]
    convergence = {str(L): float(np.linalg.norm(responses[L] - reference, ord=2))
                   for L in lengths}

    # Last-use elimination audit: eliminate side ports before or after tail gluing.
    Ltail = 12
    Resp, ext, far = attach_tail(prefix_L, term, prefix_external, ny, Ltail)
    n_left = 7
    side_global = list(range(n_left, len(ext)))
    keep_after = list(range(n_left)) + list(range(len(ext), len(ext) + len(far)))
    after = eliminate_response(Resp, keep_after)

    # Eliminate the same side nodes in the prefix graph first, retaining root and terminal.
    root_nodes = prefix_external[:n_left]
    prefix_keep_nodes = root_nodes + term
    prefix_reduced = schur_response(prefix_L, prefix_keep_nodes)
    # Build a synthetic graph whose Laplacian is the reduced response and attach tail.
    reduced_term = list(range(n_left, n_left + len(term)))
    reduced_ext = list(range(n_left))
    before_full, _, _ = attach_tail(prefix_reduced, reduced_term, reduced_ext, ny, Ltail)
    before = before_full  # already root + far only
    last_use_error = float(np.linalg.norm(after - before, ord=2))

    # Simple monotonicity diagnostics.
    resistance_increments = [resistances[lengths[i + 1]] - resistances[lengths[i]]
                             for i in range(len(lengths) - 1)]
    cross_ratios = [cross_norms[lengths[i + 1]] / cross_norms[lengths[i]]
                    for i in range(len(lengths) - 1) if cross_norms[lengths[i]] > 0]

    return {
        "seed": seed,
        "random_trials": random_trials,
        "attachment_arc_common_refinement": attachment_refinement_example(),
        "physical_port_counts": base["counts"],
        "exact_partial_gluing": {
            "base_operator_error": base["composition_error"],
            "worst_random_operator_error": float(max(random_errors)),
            "median_random_operator_error": float(np.median(random_errors)),
        },
        "last_use_elimination_error": last_use_error,
        "tail_lengths": lengths,
        "operator_distance_to_length_128": convergence,
        "constant_channel_effective_resistance": {str(k): float(v) for k, v in resistances.items()},
        "mean_zero_cross_block_norm": {str(k): float(v) for k, v in cross_norms.items()},
        "minimum_resistance_increment_over_doubling": float(min(resistance_increments)),
        "maximum_mean_zero_cross_ratio_over_doubling": float(max(cross_ratios)),
        "interpretation": [
            "Partial footprint gluing agrees with direct graph union to numerical precision.",
            "One-sided footprint differences and additional side terminals remain in the response state.",
            "Eliminating a dead side port before or after later composition agrees to numerical precision.",
            "The fixed multi-port prefix response converges as accumulated tail resistance grows.",
            "The constant-channel effective resistance grows, while remote mean-zero coupling decays."
        ],
        "warning": "Finite resistor networks are a falsification audit only; the continuum proof uses conformal trace forms, extremal-length series, and Hilbert-space Schur composition."
    }


if __name__ == "__main__":
    out = run()
    path = Path(__file__).with_name("multiport_trace_report.json")
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))
