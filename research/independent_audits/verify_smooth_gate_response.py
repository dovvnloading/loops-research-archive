#!/usr/bin/env python3
"""Reproducible analysis of an actual smooth three-terminal conformal annulus.

This verifies finite Fourier / matrix calculations and rigorous stated bound
coefficients.  It does not verify any KKL prime-end immersion, WAD, or MLC.

  python research/independent_audits/verify_smooth_gate_response.py --check-manifest
"""
from __future__ import annotations

import argparse
import cmath
import json
import math
from pathlib import Path

H = math.log(2.0)
WIDTH = math.pi / 3.0
STARTS = (0.0, math.pi / 2.0, math.pi)
MANIFEST = Path(__file__).resolve().parents[2] / 'results' / 'smooth_gate_response_20261107.json'


def integral_exp(n: int) -> complex:
    """Integral of exp(-i*n*t) over 0 <= t <= pi/3 (exact elementary formula)."""
    if n == 0:
        return complex(WIDTH)
    return (1.0 - cmath.exp(-1j * n * WIDTH)) / (1j * n)


def fourier(n: int, a: float = 0.0) -> complex:
    """Fourier coefficient of the normalized C^1 cosine arch at start a."""
    c = (integral_exp(n) - .5 * integral_exp(n - 6)
         - .5 * integral_exp(n + 6)) / (2 * math.pi * WIDTH)
    return cmath.exp(-1j * n * a) * c


def gram(nmax: int, height: float = H) -> list[list[float]]:
    """Real symmetric 3x3 Neumann-to-Dirichlet response on a literal annulus."""
    cs = [[fourier(n, a) for n in range(nmax + 1)] for a in STARTS]
    g = [[0.0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            val = height * (cs[i][0] * cs[j][0].conjugate()).real
            for n in range(1, nmax + 1):
                val += (2.0 * math.tanh(n * height) / n
                        * (cs[i][n] * cs[j][n].conjugate()).real)
            g[i][j] = 2.0 * math.pi * val
    return g


def transpose(a: list[list[float]]) -> list[list[float]]:
    return [list(row) for row in zip(*a)]


def invert(a: list[list[float]]) -> list[list[float]]:
    """Gauss-Jordan inverse: independent from all Fourier computations."""
    n = len(a)
    x = [list(a[i]) + [float(i == j) for j in range(n)]
         for i in range(n)]
    for i in range(n):
        pivot = max(range(i, n), key=lambda p: abs(x[p][i]))
        assert abs(x[pivot][i]) > 1e-13
        x[i], x[pivot] = x[pivot], x[i]
        scale = x[i][i]
        x[i] = [v / scale for v in x[i]]
        for j in range(n):
            if i != j:
                factor = x[j][i]
                x[j] = [v - factor * u for v, u in zip(x[j], x[i])]
    return [row[n:] for row in x]


def determinant3(g: list[list[float]]) -> float:
    a, b, c = g
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def quadratic(g: list[list[float]], x: list[float]) -> float:
    return sum(x[i] * x[j] * g[i][j] for i in range(len(x))
               for j in range(len(x)))


def sharp_step_partial(nmax: int, epsilon: float = 0.0) -> float:
    """Exact Fourier partial energy for 0/1 half-circle trace, outer trace 0."""
    energy = math.pi / (2.0 * H)
    for n in range(1, nmax + 1, 2):
        energy += (4.0 / math.pi) * math.exp(-2.0 * epsilon * n) / n * (1.0 / math.tanh(n * H))
    return energy


def verify() -> dict:
    # Three normalized disjoint ideal-arc probes, including endpoint derivative 0.
    assert STARTS[0] + WIDTH < STARTS[1]
    assert STARTS[1] + WIDTH < STARTS[2]
    assert STARTS[2] + WIDTH < 2 * math.pi
    assert abs(fourier(0).real - 1.0 / (2 * math.pi)) < 1e-14
    assert abs(abs(fourier(1)) - 54.0 / (35 * math.pi**2)) < 1e-14
    assert abs(math.tanh(H) - 3.0 / 5.0) < 1e-14

    alpha = H / (2.0 * math.pi)
    beta = 34992.0 / (6125.0 * math.pi**3)
    lower = 2.0 * alpha * beta / (3.0 * alpha + beta)
    # The truncated 0,±1 matrix is the provably positive-semidefinite
    # Fourier part, with exact projection geometry for starts 0, pi/2, pi.
    g1 = gram(1)
    model = [[alpha + beta, alpha, alpha - beta],
             [alpha, alpha + beta, alpha],
             [alpha - beta, alpha, alpha + beta]]
    assert max(abs(g1[i][j] - model[i][j])
               for i in range(3) for j in range(3)) < 1e-13
    assert lower > 0.078
    # Three principal minors of g1 - lower*I verify the displayed spectral
    # lower bound numerically, while the written 2x2 trace/determinant
    # argument is the non-numerical proof.
    shifted = [[g1[i][j] - (lower if i == j else 0)
                for j in range(3)] for i in range(3)]
    assert shifted[0][0] > 0
    assert shifted[0][0]*shifted[1][1] - shifted[0][1]**2 > 0
    assert determinant3(shifted) > -1e-13

    # Check N-dependent rigorous absolute tail estimate and the actual N gap.
    n1, n2 = 128, 256
    g64, g128 = gram(n1), gram(n2)
    tail_n1 = 13824.0 / (math.pi**3 * n1**6)
    tail_n2 = 13824.0 / (math.pi**3 * n2**6)
    gap = max(abs(g128[i][j] - g64[i][j])
              for i in range(3) for j in range(3))
    assert gap < tail_n1
    assert tail_n2 < 2e-12
    assert max(abs(g128[i][j]-g128[j][i])
               for i in range(3) for j in range(3)) < 1e-14
    assert all(quadratic(g128, v) > 0 for v in ([1,0,0], [0,1,0],
                [0,0,1], [1,-1,0], [1,1,1], [1,-2,1]))
    k = invert(g128)
    # Forget/relax terminal 3, comparing 2x2 principal N-to-D inverse
    # directly with the Schur complement of the 3-terminal D-to-N matrix.
    kron = [[k[i][j] - k[i][2]*k[2][j]/k[2][2] for j in range(2)]
            for i in range(2)]
    independent = invert([r[:2] for r in g128[:2]])
    kron_gap = max(abs(kron[i][j]-independent[i][j])
                   for i in range(2) for j in range(2))
    assert kron_gap < 1e-11
    charge = [1.0, -1.0]
    assert abs(quadratic(kron, charge) - quadratic(independent, charge)) < 1e-11

    # New analytic no-go: if the conformal height tends to zero, every
    # smooth averaged Neumann-to-Dirichlet eigenvalue also tends to zero.
    # Plancherel proves G_h <= h*D, with D_ij = integral psi_i*psi_j;
    # our separated arch probes have D=(9/(2*pi))*identity.
    d = 9.0 / (2.0 * math.pi)
    thin = []
    for height in (1/4, 1/8, 1/16, 1/32, 1/64):
        gh = gram(256, height)
        # Numeric consequences of the symbol inequality tanh(nh)/n <= h.
        assert all(quadratic(gh, v) <= height * d * sum(x*x for x in v) + 1e-11
                   for v in ([1,0,0],[0,1,0],[0,0,1],[1,1,1],[1,-1,1],[2,1,-3]))
        thin.append({'height':height, 'diag_over_height':gh[0][0]/height,
                     'offdiag_over_height':gh[0][1]/height})
    assert abs(thin[-1]['diag_over_height'] - d) < .008
    assert abs(thin[-1]['offdiag_over_height']) < .008

    # Direct step voltages give a divergent harmonic series; the subtractive
    # remainder approaches the predicted (2/pi) log N coefficient.
    e256, e1024, e4096 = [sharp_step_partial(n) for n in (256, 1024, 4096)]
    slope = (e4096 - e1024) / math.log(4096 / 1024)
    assert e4096 > e1024 > e256
    assert abs(slope - 2.0 / math.pi) < 0.004
    smoothed = [(eps, sharp_step_partial(5000, eps)) for eps in (1/32,1/64,1/128,1/256)]
    residuals = [energy - (2/math.pi)*math.log(1/eps) for eps, energy in smoothed]
    assert max(residuals) - min(residuals) < .06

    # A genuine degree-two holomorphic cylinder covering (t,theta) ->
    # (2t,2theta) between heights H/2 and H: u=e^-t cos(theta).
    target_energy = math.pi * (1 - math.exp(-2*H))
    pullback_energy = 2 * math.pi * (1 - math.exp(-2*H))
    assert abs(pullback_energy - 2 * target_energy) < 1e-14

    fmt = lambda v: round(v, 12)
    return {
        'schema_version': 1,
        'scope': 'exact analytic smooth annulus example and numerical checks only; not KKL native WAD',
        'physical_annulus': {'height': 'log(2)', 'width': 'pi/3', 'starts': ['0','pi/2','pi']},
        'boundary_voltage_no_go': {
            'step_energy_partial_256': fmt(e256),
            'step_energy_partial_1024': fmt(e1024),
            'step_energy_partial_4096': fmt(e4096),
            'estimated_log_growth_slope': fmt(slope),
            'predicted_coefficient': fmt(2/math.pi),
            'smooth_epsilon_residuals': [fmt(x) for x in residuals],
            'conclusion': 'sharp 0/1 Dirichlet trace has infinite energy',
        },
        'smooth_average_response': {
            'number_of_probes': 3,
            'nmax': n2,
            'alpha': fmt(alpha), 'beta': fmt(beta),
            'certified_min_eigenvalue_lower_bound': fmt(lower),
            'rigorous_entrywise_tail_256': fmt(tail_n2),
            'observed_gram_128_vs_256_gap': fmt(gap),
            'gram_256': [[fmt(x) for x in row] for row in g128],
            'kron_2terminal_residual': fmt(kron_gap),
            'two_terminal_opposite_charge_energy': fmt(quadratic(kron, charge)),
        },
        'thin_modulus_obstruction': {
            'theorem': '0 < G_h <= (9*h/(2*pi))*identity; G_h/h -> (9/(2*pi))*identity as h -> 0',
            'limit_coefficient': fmt(d),
            'measurements': [{k: fmt(v) for k,v in row.items()} for row in thin],
            'interpretation': 'no uniform positive lower eigenvalue over arbitrary thin annuli; not a KKL stage',
        },
        'covering_energy': {
            'covering_degree': 2,
            'target_energy': fmt(target_energy),
            'pullback_energy': fmt(pullback_energy),
            'ratio': fmt(pullback_energy/target_energy),
        },
        'analytic_trust_boundary': 'no actual KKL f_*iota^* graph arrows, non-LC attachment census, or WAD comparison checked',
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group()
    g.add_argument('--write-manifest',action='store_true')
    g.add_argument('--check-manifest',action='store_true')
    args = p.parse_args()
    result = json.dumps(verify(), indent=2, sort_keys=True) + '\n'
    if args.write_manifest:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(result, encoding='utf-8')
        print('Wrote '+str(MANIFEST))
    elif args.check_manifest:
        assert MANIFEST.read_text(encoding='utf-8') == result, 'manifest differs from exact recomputation'
        print('PASS: smooth annular gate response and byte-identical manifest')
    else:
        print(result, end='')


if __name__ == '__main__':
    main()
