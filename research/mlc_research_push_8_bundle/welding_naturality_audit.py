#!/usr/bin/env python3
"""Exact rational audit for welding composition and enlargement naturality."""
from __future__ import annotations

import json
import random
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parent


def rand_matrix(rng: random.Random, rows: int, cols: int) -> sp.Matrix:
    return sp.Matrix(rows, cols, [rng.randint(-2, 2) for _ in range(rows * cols)])


def inclusion(new_dim: int, old_dim: int) -> sp.Matrix:
    M = sp.zeros(new_dim, old_dim)
    for i in range(old_dim):
        M[i, i] = 1
    return M


def extension_factor(
    rng: random.Random,
    old: sp.Matrix,
    A_out: sp.Matrix,
    A_in: sp.Matrix,
    new_out_dim: int,
    new_in_dim: int,
) -> sp.Matrix:
    """Build X+ with X+ A_in = A_out X exactly."""
    Xp = rand_matrix(rng, new_out_dim, new_in_dim)
    constrained = A_out * old
    # A_in is the standard coordinate inclusion, so its columns select the first
    # old input columns of Xp.
    for j in range(old.cols):
        Xp[:, j] = constrained[:, j]
    assert Xp * A_in == constrained
    return Xp


def trial(rng: random.Random) -> None:
    p = rng.randint(1, 5)
    s = rng.randint(1, 6)
    o = rng.randint(1, 6)
    R = rand_matrix(rng, s, p)  # immersion/end restriction and subdivision
    P = rand_matrix(rng, o, s)  # covering transport
    W = P * R

    ep, es, eo = rng.randint(0, 3), rng.randint(0, 3), rng.randint(0, 3)
    A_p = inclusion(p + ep, p)
    A_s = inclusion(s + es, s)
    A_o = inclusion(o + eo, o)
    R_plus = extension_factor(rng, R, A_s, A_p, s + es, p + ep)
    P_plus = extension_factor(rng, P, A_o, A_s, o + eo, s + es)
    W_plus = P_plus * R_plus
    assert R_plus * A_p == A_s * R
    assert P_plus * A_s == A_o * P
    assert W_plus * A_p == A_o * W

    # Exact word composition on same-dimensional interface spaces.
    d = rng.randint(1, 5)
    W1 = rand_matrix(rng, d, d)
    W2 = rand_matrix(rng, d, d)
    W3 = rand_matrix(rng, d, d)
    x = rand_matrix(rng, d, 1)
    assert W3 * (W2 * (W1 * x)) == (W3 * W2 * W1) * x


def main() -> None:
    seed = 20260725
    trials = 1000
    rng = random.Random(seed)
    for _ in range(trials):
        trial(rng)
    report = {
        "seed": seed,
        "trials": trials,
        "exact_failures": 0,
        "checks": [
            "factorwise enlargement squares",
            "welding enlargement naturality",
            "word composition associativity",
        ],
        "arithmetic": "exact SymPy integers",
    }
    (ROOT / "welding_naturality_report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True)
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
