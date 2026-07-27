#!/usr/bin/env python3
"""Exact algebra audit for the fixed-block KKL Value moment state.

This checks only the finite-dimensional identities proved in Research Push VII:
  Val = <aa^T, M>,
  M_child = P_L M P_L^T + P_R M P_R^T,
  vec(M_child) = (P_L tensor P_L + P_R tensor P_R) vec(M).
It does not prove that a virtual block has a uniformly bounded terminal tree or
an actual typed factor to the terminal Hubbard incidence.
"""
from __future__ import annotations

import argparse
import json
import random
from pathlib import Path

import sympy as sp


def col_vec(M: sp.Matrix) -> sp.Matrix:
    return sp.Matrix([M[i, j] for j in range(M.cols) for i in range(M.rows)])


def random_matrix(rng: random.Random, rows: int, cols: int, low: int = 0, high: int = 2) -> sp.Matrix:
    return sp.Matrix(rows, cols, [rng.randint(low, high) for _ in range(rows * cols)])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output")
    parser.add_argument("--seed", type=int, default=20260725)
    parser.add_argument("--trials", type=int, default=100)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    failures: list[dict[str, object]] = []
    examples: list[dict[str, object]] = []
    checks = 0

    for trial in range(args.trials):
        m = rng.randint(2, 5)  # realized pair-state dimension in the audit
        k = rng.randint(2, 7)  # number of WAD support arcs
        a = sp.Matrix([rng.randint(1, 5) for _ in range(m)])
        zs = [sp.Matrix([rng.randint(0, 4) for _ in range(m)]) for _ in range(k)]
        weights = [sp.Integer(rng.randint(1, 5)) for _ in range(k)]

        M = sp.zeros(m, m)
        direct_value = sp.Integer(0)
        for weight, z in zip(weights, zs):
            M += weight * (z * z.T)
            direct_value += weight * (a.dot(z) ** 2)

        moment_value = (a.T * M * a)[0]
        checks += 1
        if sp.simplify(direct_value - moment_value) != 0:
            failures.append({"trial": trial, "check": "value_moment"})

        PL = random_matrix(rng, m, m, 0, 2)
        PR = random_matrix(rng, m, m, 0, 2)
        direct_child = sp.zeros(m, m)
        for weight, z in zip(weights, zs):
            zl = PL * z
            zr = PR * z
            direct_child += weight * (zl * zl.T + zr * zr.T)
        cp_child = PL * M * PL.T + PR * M * PR.T
        checks += 1
        if direct_child != cp_child:
            failures.append({"trial": trial, "check": "cp_transport"})

        kron = sp.kronecker_product(PL, PL) + sp.kronecker_product(PR, PR)
        checks += 1
        if col_vec(cp_child) != kron * col_vec(M):
            failures.append({"trial": trial, "check": "vectorized_transport"})

        if trial < 3:
            examples.append({
                "trial": trial,
                "pair_state_dimension": m,
                "wad_support_size": k,
                "value": str(moment_value),
                "moment_rank": int(M.rank()),
                "child_moment_rank": int(cp_child.rank()),
            })

    report = {
        "seed": args.seed,
        "trials": args.trials,
        "exact_checks": checks,
        "failures": failures,
        "passed": not failures,
        "examples": examples,
        "interpretation": (
            "Exact symbolic verification of the fixed-block Value second-moment "
            "identity and completely positive binary transport. This is not a "
            "proof of universal terminal-tree dimension or virtual incidence realization."
        ),
    }
    Path(args.output).write_text(json.dumps(report, indent=2) + "\n")
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
