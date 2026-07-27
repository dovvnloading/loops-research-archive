#!/usr/bin/env python3
"""Numerical audit for the finite-network analogue of Research Push III.

This script does not prove the analytic surface theorem.  It checks the exact
Schur-complement inequalities used in Theorem 17 on finite conductance graphs:

    0 <= Lambda_connected - Lambda_disconnected,
    ||Lambda_connected - Lambda_disconnected||_op <= 2 * sum(neck conductances).

It also evaluates the adaptive depth formula c_i <= 1/(ell_i R_i).
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


TOL = 1e-9


def graph_laplacian(n: int, edges: list[tuple[int, int, float]]) -> np.ndarray:
    L = np.zeros((n, n), dtype=float)
    for u, v, c in edges:
        if not (0 <= u < n and 0 <= v < n and u != v and c > 0):
            raise ValueError(f"invalid edge {(u, v, c)} for n={n}")
        L[u, u] += c
        L[v, v] += c
        L[u, v] -= c
        L[v, u] -= c
    return L


def response_matrix(L: np.ndarray, terminals: list[int]) -> np.ndarray:
    """Dirichlet-to-Neumann response by Schur complement.

    Each connected component must contain at least one terminal.  The internal
    block is then positive definite.  Numerical pseudoinverse is used as a
    defensive fallback for nearly singular inputs.
    """
    n = L.shape[0]
    T = np.array(sorted(set(terminals)), dtype=int)
    if len(T) == 0:
        raise ValueError("at least one terminal is required")
    I = np.array([i for i in range(n) if i not in set(T.tolist())], dtype=int)
    Ltt = L[np.ix_(T, T)]
    if len(I) == 0:
        return Ltt
    Lti = L[np.ix_(T, I)]
    Lit = L[np.ix_(I, T)]
    Lii = L[np.ix_(I, I)]
    inv = np.linalg.pinv(Lii, rcond=1e-12)
    R = Ltt - Lti @ inv @ Lit
    return 0.5 * (R + R.T)


def random_connected_edges(rng: np.random.Generator, n: int) -> list[tuple[int, int, float]]:
    edges: list[tuple[int, int, float]] = []
    # Random spanning tree.
    for v in range(1, n):
        u = int(rng.integers(0, v))
        c = float(rng.uniform(0.2, 2.0))
        edges.append((u, v, c))
    # Extra edges.
    for u in range(n):
        for v in range(u + 1, n):
            if rng.random() < 0.25 and all(not (a == u and b == v) for a, b, _ in edges):
                edges.append((u, v, float(rng.uniform(0.1, 1.5))))
    return edges


@dataclass
class TrialResult:
    min_psd_eigenvalue: float
    operator_norm: float
    bound: float
    ratio: float


def one_trial(rng: np.random.Generator, bubbles: int) -> TrialResult:
    base_n = int(rng.integers(4, 8))
    base_edges = random_connected_edges(rng, base_n)
    base_terminals = [0, 1]
    base_attach = 2

    component_edges: list[tuple[int, int, float]] = list(base_edges)
    terminal_indices: list[int] = list(base_terminals)
    necks: list[tuple[int, int, float]] = []
    offset = base_n

    for _ in range(bubbles):
        n = int(rng.integers(3, 7))
        edges = random_connected_edges(rng, n)
        # Bubble has two observed terminals and one attachment node.
        component_edges.extend((u + offset, v + offset, c) for u, v, c in edges)
        terminal_indices.extend([offset, offset + 1])
        bubble_attach = offset + 2
        c_neck = float(rng.uniform(1e-4, 0.25))
        necks.append((base_attach, bubble_attach, c_neck))
        offset += n

    n_total = offset
    L_disc = graph_laplacian(n_total, component_edges)
    L_conn = graph_laplacian(n_total, component_edges + necks)

    R_disc = response_matrix(L_disc, terminal_indices)
    R_conn = response_matrix(L_conn, terminal_indices)
    delta = 0.5 * ((R_conn - R_disc) + (R_conn - R_disc).T)
    eig = np.linalg.eigvalsh(delta)
    op = float(max(abs(eig.min()), abs(eig.max())))
    bound = 2.0 * sum(c for _, _, c in necks)
    return TrialResult(
        min_psd_eigenvalue=float(eig.min()),
        operator_norm=op,
        bound=bound,
        ratio=op / bound if bound > 0 else 0.0,
    )


def adaptive_depths(resistances: list[float], epsilon: float) -> list[int]:
    if epsilon <= 0:
        raise ValueError("epsilon must be positive")
    s = len(resistances)
    if s == 0:
        return []
    lengths = []
    for R in resistances:
        if R <= 0:
            raise ValueError("all cell resistances must be positive")
        lengths.append(int(np.ceil(2.0 * s / (epsilon * R))))
    return lengths


def run(seed: int, trials: int, max_bubbles: int, epsilon: float, resistances: list[float]) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    results: list[TrialResult] = []
    for _ in range(trials):
        b = int(rng.integers(1, max_bubbles + 1))
        results.append(one_trial(rng, b))

    lengths = adaptive_depths(resistances, epsilon)
    depth_bound = 2.0 * sum(1.0 / (ell * R) for ell, R in zip(lengths, resistances)) if lengths else 0.0

    worst_min = min(r.min_psd_eigenvalue for r in results)
    worst_ratio = max(r.ratio for r in results)
    worst_excess = max(r.operator_norm - r.bound for r in results)

    return {
        "status": "pass" if worst_min >= -1e-7 and worst_excess <= 1e-7 and depth_bound <= epsilon + 1e-12 else "fail",
        "note": "Finite-network numerical audit only; the analytic proof is the Dirichlet-principle argument in the research note.",
        "seed": seed,
        "trials": trials,
        "max_bubbles": max_bubbles,
        "response_inequality": {
            "worst_min_eigenvalue_of_delta": worst_min,
            "worst_operator_norm_to_bound_ratio": worst_ratio,
            "worst_operator_norm_minus_bound": worst_excess,
            "bound_formula": "2 * sum(neck_conductances)",
        },
        "adaptive_depth": {
            "epsilon": epsilon,
            "cell_resistances": resistances,
            "chosen_tail_lengths": lengths,
            "certified_operator_bound": depth_bound,
            "formula": "ell_i = ceil(2*s/(epsilon*R_i))",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20260724)
    parser.add_argument("--trials", type=int, default=250)
    parser.add_argument("--max-bubbles", type=int, default=8)
    parser.add_argument("--epsilon", type=float, default=0.01)
    parser.add_argument("--resistances", type=float, nargs="+", default=[0.07, 0.11, 0.19, 0.23])
    parser.add_argument("--output", type=Path, default=Path("plumbing_response_report.json"))
    args = parser.parse_args()

    report = run(args.seed, args.trials, args.max_bubbles, args.epsilon, args.resistances)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    if report["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
