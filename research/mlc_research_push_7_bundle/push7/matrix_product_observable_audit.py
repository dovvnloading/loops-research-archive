#!/usr/bin/env python3
"""Exact audit of the binary matrix-product observable identity.

Uses SymPy integer/rational arithmetic.  It compares exhaustive 2^r leaf
summation with the fixed-dimension Kronecker transfer formula.
"""
from __future__ import annotations

import argparse
import json
import random
from itertools import product
from pathlib import Path

import sympy as sp


def rand_matrix(rng: random.Random, rows: int, cols: int, bound: int = 3) -> sp.Matrix:
    return sp.Matrix(rows, cols, [rng.randint(-bound, bound) for _ in range(rows * cols)])


def word_product(mats: dict[str, sp.Matrix], word: str) -> sp.Matrix:
    if not word:
        size = next(iter(mats.values())).rows
        return sp.eye(size)
    result = sp.eye(next(iter(mats.values())).rows)
    for letter in word:
        result = result * mats[letter]
    return result


def exhaustive(
    M: dict[str, sp.Matrix],
    R: dict[str, sp.Matrix],
    u: sp.Matrix,
    v: sp.Matrix,
    x: sp.Matrix,
    depth: int,
) -> sp.Matrix:
    total = sp.zeros(x.rows, 1)
    for letters in product(("L", "R"), repeat=depth):
        word = "".join(letters)
        coeff = (u.T * word_product(M, word) * v)[0]
        total += coeff * word_product(R, word) * x
    return sp.simplify(total)


def transfer(
    M: dict[str, sp.Matrix],
    R: dict[str, sp.Matrix],
    u: sp.Matrix,
    v: sp.Matrix,
    x: sp.Matrix,
    depth: int,
) -> sp.Matrix:
    w = x.rows
    K = sp.kronecker_product(M["L"], R["L"]) + sp.kronecker_product(M["R"], R["R"])
    left = sp.kronecker_product(u.T, sp.eye(w))
    right = sp.kronecker_product(v, x)
    return sp.simplify(left * (K ** depth) * right)


def run(seed: int, trials: int, max_depth: int) -> dict:
    rng = random.Random(seed)
    failures = []
    checks = 0
    examples = []
    for trial in range(trials):
        d = rng.randint(1, 3)
        w = rng.randint(1, 4)
        M = {a: rand_matrix(rng, d, d) for a in ("L", "R")}
        R = {a: rand_matrix(rng, w, w) for a in ("L", "R")}
        u = rand_matrix(rng, d, 1)
        v = rand_matrix(rng, d, 1)
        x = rand_matrix(rng, w, 1)
        for depth in range(max_depth + 1):
            lhs = exhaustive(M, R, u, v, x, depth)
            rhs = transfer(M, R, u, v, x, depth)
            checks += 1
            if lhs != rhs:
                failures.append(
                    {
                        "trial": trial,
                        "depth": depth,
                        "d": d,
                        "w": w,
                        "lhs": [str(z) for z in lhs],
                        "rhs": [str(z) for z in rhs],
                    }
                )
                break
        if trial < 3:
            examples.append(
                {
                    "trial": trial,
                    "coefficient_dimension": d,
                    "feature_dimension": w,
                    "max_depth": max_depth,
                    "terminal_value": [
                        str(z) for z in transfer(M, R, u, v, x, max_depth)
                    ],
                }
            )
    return {
        "seed": seed,
        "trials": trials,
        "max_depth": max_depth,
        "exact_checks": checks,
        "failures": failures,
        "passed": not failures,
        "examples": examples,
        "interpretation": "Exact integer/rational verification of the Kronecker matrix-product observable identity; not a proof that KKL Value coefficients satisfy a universal finite-state law."
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--seed", type=int, default=20260725)
    parser.add_argument("--trials", type=int, default=100)
    parser.add_argument("--max-depth", type=int, default=7)
    args = parser.parse_args()
    report = run(args.seed, args.trials, args.max_depth)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    if not report["passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
