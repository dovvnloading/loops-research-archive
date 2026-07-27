#!/usr/bin/env python3
"""Audit the full Sobolev-trace plumbing formulas used in Research Push IV.

This script checks finite Fourier truncations of the exact Neumann-wall rectangle
Dirichlet-to-Neumann operator. It validates:

1. the exact mode formula;
2. the response semigroup N(R1) star N(R2) = N(R1+R2);
3. the sharp trace-renormalized relative bound
       |N(R)-N#(R)| <= eta(R) N#(R),
   eta(R)=2/(exp(pi*R)-1);
4. preservation of the same multiplicative bound after eliminating arbitrary
   random Hilbert-interface variables by Schur complement;
5. compact convergence to the two half-cylinder response operators; and
6. failure of scalar/equipotential collapse on a nonconstant trace mode.

The finite-mode computation is a stress test, not the proof. The proof is the
mode-by-mode harmonic extension and variational gluing argument in the memo.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


def coth_stable(t: float) -> float:
    if t > 350.0:
        return 1.0
    return 1.0 + 2.0 / math.expm1(2.0 * t)


def csch_stable(t: float) -> float:
    if t > 350.0:
        return 0.0
    e = math.exp(-t)
    return 2.0 * e / (1.0 - e * e)


def eta(R: float) -> float:
    if R <= 0:
        raise ValueError("R must be positive")
    t = math.pi * R
    if t > 350.0:
        return 0.0
    return 2.0 / math.expm1(t)


def neck_response(R: float, modes: int) -> np.ndarray:
    """Exact DtN matrix on modes 0,...,modes for a width-one rectangle.

    Boundary order is (left modes, right modes). Side walls are Neumann.
    The cosine basis is L2-orthonormal on [0,1].
    """
    if R <= 0 or modes < 0:
        raise ValueError("invalid R or mode count")
    d = modes + 1
    N = np.zeros((2 * d, 2 * d), dtype=float)

    # Constant mode.
    c = 1.0 / R
    N[0, 0] = c
    N[d, d] = c
    N[0, d] = -c
    N[d, 0] = -c

    # Mean-zero cosine modes.
    for n in range(1, d):
        kappa = n * math.pi
        t = kappa * R
        diagonal = kappa * coth_stable(t)
        coupling = kappa * csch_stable(t)
        N[n, n] = diagonal
        N[d + n, d + n] = diagonal
        N[n, d + n] = -coupling
        N[d + n, n] = -coupling
    return N


def trace_renormalized_response(R: float, modes: int) -> np.ndarray:
    """Two half-cylinder self responses plus exact constant-mode resistor."""
    d = modes + 1
    N = np.zeros((2 * d, 2 * d), dtype=float)
    c = 1.0 / R
    N[0, 0] = c
    N[d, d] = c
    N[0, d] = -c
    N[d, 0] = -c
    for n in range(1, d):
        kappa = n * math.pi
        N[n, n] = kappa
        N[d + n, d + n] = kappa
    return N


def infinite_neck_limit(modes: int) -> np.ndarray:
    d = modes + 1
    N = np.zeros((2 * d, 2 * d), dtype=float)
    for n in range(1, d):
        kappa = n * math.pi
        N[n, n] = kappa
        N[d + n, d + n] = kappa
    return N


def trace_norm_gram(modes: int) -> np.ndarray:
    """H^{1/2}-type gram matrix on two boundaries, constants weighted by 1."""
    d = modes + 1
    W = np.zeros((2 * d, 2 * d), dtype=float)
    W[0, 0] = 1.0
    W[d, d] = 1.0
    for n in range(1, d):
        kappa = n * math.pi
        W[n, n] = kappa
        W[d + n, d + n] = kappa
    return W


def sym(A: np.ndarray) -> np.ndarray:
    return 0.5 * (A + A.T)


def schur(A: np.ndarray, external: list[int]) -> np.ndarray:
    n = A.shape[0]
    ext = np.array(external, dtype=int)
    ext_set = set(ext.tolist())
    internal = np.array([j for j in range(n) if j not in ext_set], dtype=int)
    Aee = A[np.ix_(ext, ext)]
    if internal.size == 0:
        return sym(Aee)
    Aei = A[np.ix_(ext, internal)]
    Aii = A[np.ix_(internal, internal)]
    # Test matrices are strictly positive on internal variables.
    X = np.linalg.solve(Aii, Aei.T)
    return sym(Aee - Aei @ X)


def invsqrt_spd(A: np.ndarray) -> np.ndarray:
    w, V = np.linalg.eigh(sym(A))
    if w.min() <= 1e-12:
        raise ValueError(f"matrix not SPD; min eigenvalue={w.min()}")
    return (V / np.sqrt(w)) @ V.T


def relative_spectrum(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Eigenvalues of B^{-1/2} A B^{-1/2}, for SPD B."""
    S = invsqrt_spd(B)
    return np.linalg.eigvalsh(sym(S @ A @ S))


def compose_necks(R1: float, R2: float, modes: int) -> float:
    d = modes + 1
    N1 = neck_response(R1, modes)
    N2 = neck_response(R2, modes)
    # Variables are left, middle, right, each of dimension d.
    total = np.zeros((3 * d, 3 * d), dtype=float)
    idx_l = list(range(0, d))
    idx_m = list(range(d, 2 * d))
    idx_r = list(range(2 * d, 3 * d))
    idx_lm = idx_l + idx_m
    idx_mr = idx_m + idx_r
    total[np.ix_(idx_lm, idx_lm)] += N1
    total[np.ix_(idx_mr, idx_mr)] += N2
    composed = schur(total, idx_l + idx_r)
    target = neck_response(R1 + R2, modes)
    return float(np.linalg.norm(composed - target, ord=2))


def random_component_form(
    rng: np.random.Generator, external_dim: int, interface_dim: int
) -> np.ndarray:
    n = external_dim + interface_dim
    rows = n + int(rng.integers(2, 8))
    B = rng.normal(size=(rows, n))
    Q = B.T @ B
    # Uniform coercivity is only for numerical stability; the theorem allows
    # semidefinite forms modulo constants.
    Q += 0.3 * np.eye(n)
    return sym(Q)


def gluing_trial(
    rng: np.random.Generator, R: float, modes: int
) -> dict[str, float]:
    d = modes + 1
    p_left = int(rng.integers(1, 6))
    p_right = int(rng.integers(1, 6))
    Ql = random_component_form(rng, p_left, d)
    Qr = random_component_form(rng, p_right, d)

    # Global variable order: ext-left, ext-right, trace-left, trace-right.
    p = p_left + p_right
    total_exact = np.zeros((p + 2 * d, p + 2 * d), dtype=float)
    total_red = np.zeros_like(total_exact)

    map_l = list(range(0, p_left)) + list(range(p, p + d))
    map_r = list(range(p_left, p)) + list(range(p + d, p + 2 * d))
    for total in (total_exact, total_red):
        total[np.ix_(map_l, map_l)] += Ql
        total[np.ix_(map_r, map_r)] += Qr
    traces = list(range(p, p + 2 * d))
    total_exact[np.ix_(traces, traces)] += neck_response(R, modes)
    total_red[np.ix_(traces, traces)] += trace_renormalized_response(R, modes)

    ext = list(range(p))
    Rex = schur(total_exact, ext)
    Rred = schur(total_red, ext)
    spectrum = relative_spectrum(Rex, Rred)
    e = eta(R)
    return {
        "min_relative_eigenvalue": float(spectrum.min()),
        "max_relative_eigenvalue": float(spectrum.max()),
        "lower_margin": float(spectrum.min() - (1.0 - e)),
        "upper_margin": float((1.0 + e) - spectrum.max()),
    }


def run(seed: int, trials: int, max_modes: int) -> dict[str, Any]:
    rng = np.random.default_rng(seed)

    # Sharp modewise relative bound.
    mode_bound_errors: list[float] = []
    compactness_errors: list[float] = []
    semigroup_errors: list[float] = []
    gluing_results: list[dict[str, float]] = []

    for _ in range(trials):
        R = float(rng.uniform(0.4, 5.0))
        modes = int(rng.integers(1, max_modes + 1))
        N = neck_response(R, modes)
        Nr = trace_renormalized_response(R, modes)
        W = trace_norm_gram(modes)

        # Relative error restricted to the complement of the common constant
        # kernel, using the trace-renormalized gram matrix itself.
        w, V = np.linalg.eigh(Nr)
        active = w > 1e-11
        S = (V[:, active] / np.sqrt(w[active]))
        rel = sym(S.T @ (N - Nr) @ S)
        actual = float(np.max(np.abs(np.linalg.eigvalsh(rel))))
        mode_bound_errors.append(actual - eta(R))

        Ninf = infinite_neck_limit(modes)
        Winv = invsqrt_spd(W)
        compact_norm = float(np.linalg.norm(sym(Winv @ (N - Ninf) @ Winv), ord=2))
        compact_bound = max(2.0 / R, eta(R))
        compactness_errors.append(compact_norm - compact_bound)

        R1 = float(rng.uniform(0.2, 3.0))
        R2 = float(rng.uniform(0.2, 3.0))
        semigroup_errors.append(compose_necks(R1, R2, modes))

        gluing_results.append(gluing_trial(rng, R, modes))

    # Scalar-collapse counterexample: first mean-zero cosine mode.
    counter_R = 8.0
    mean_zero_energy = math.pi * coth_stable(math.pi * counter_R)
    scalar_model_energy = 0.0

    worst_mode_excess = max(mode_bound_errors)
    worst_compact_excess = max(compactness_errors)
    worst_semigroup = max(semigroup_errors)
    worst_lower_margin = min(r["lower_margin"] for r in gluing_results)
    worst_upper_margin = min(r["upper_margin"] for r in gluing_results)

    status = "pass"
    if worst_mode_excess > 2e-9:
        status = "fail"
    if worst_compact_excess > 2e-9:
        status = "fail"
    if worst_semigroup > 2e-8:
        status = "fail"
    if worst_lower_margin < -2e-8 or worst_upper_margin < -2e-8:
        status = "fail"
    if mean_zero_energy <= 3.0 or scalar_model_energy != 0.0:
        status = "fail"

    contraction_mu = 0.82
    admissible_eta = (1.0 - contraction_mu) / (1.0 + contraction_mu)
    target_eta = 0.5 * admissible_eta
    required_R = math.log1p(2.0 / target_eta) / math.pi
    effective_mu = contraction_mu * (1.0 + target_eta) / (1.0 - target_eta)

    return {
        "status": status,
        "note": (
            "Finite Fourier and finite-dimensional Schur-complement audit only. "
            "The analytic proof is the harmonic mode formula plus variational gluing."
        ),
        "seed": seed,
        "trials": trials,
        "max_modes": max_modes,
        "sharp_relative_bound": {
            "formula": "eta(R)=2/(exp(pi*R)-1)",
            "worst_actual_minus_bound": worst_mode_excess,
        },
        "trace_semigroup": {
            "formula": "N(R1) star N(R2) = N(R1+R2)",
            "worst_operator_norm_error": worst_semigroup,
        },
        "schur_complement_stability": {
            "formula": "(1-eta) Lambda# <= Lambda <= (1+eta) Lambda#",
            "worst_lower_margin": worst_lower_margin,
            "worst_upper_margin": worst_upper_margin,
        },
        "compact_limit": {
            "limit": "two independent half-cylinder |D_N| responses; constants decouple",
            "bound": "max(2/R, eta(R)) in the normalized H^{1/2}->H^{-1/2} norm",
            "worst_actual_minus_bound": worst_compact_excess,
        },
        "equipotential_collapse_no_go": {
            "R": counter_R,
            "trace": "left cos(pi*y), right 0",
            "trace_means": [0.0, 0.0],
            "actual_energy": mean_zero_energy,
            "scalar_mean_only_energy": scalar_model_energy,
            "conclusion": "geometric equipotential curves do not force electrical equipotential traces",
        },
        "strict_transition_example": {
            "root_mu": contraction_mu,
            "maximum_eta_for_strictness": admissible_eta,
            "chosen_eta": target_eta,
            "required_total_resistance": required_R,
            "effective_mu": effective_mu,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20260725)
    parser.add_argument("--trials", type=int, default=500)
    parser.add_argument("--max-modes", type=int, default=24)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("full_trace_plumbing_report.json"),
    )
    args = parser.parse_args()
    report = run(args.seed, args.trials, args.max_modes)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    if report["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
