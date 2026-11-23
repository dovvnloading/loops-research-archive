#!/usr/bin/env python3
"""Exact finite readout regressions and optional clone asymptotic diagnostics.

The default checks stationary rational Markov chains using Gaussian-rational
arithmetic. Path-moment propagation is independent of the closed covariance
formula. One chain has a non-real pseudo-covariance, so treating Re(g) as an
automatically phase-aligned readout is an explicitly rejected mutation.

--numerics uses mpmath at 90 decimal digits. Root residuals and convergence
values are diagnostics, not certified enclosures or proofs of limiting claims.
The all-delay and measure-theoretic proofs are in the accompanying note.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import json
from math import comb
from pathlib import Path


@dataclass(frozen=True)
class CQ:
    """A Gaussian rational, with no floating-point arithmetic."""

    re: Q = Q(0)
    im: Q = Q(0)

    def __add__(self, other: CQ) -> CQ:
        return CQ(self.re + other.re, self.im + other.im)

    def __neg__(self) -> CQ:
        return CQ(-self.re, -self.im)

    def __sub__(self, other: CQ) -> CQ:
        return self + (-other)

    def __mul__(self, other: CQ) -> CQ:
        return CQ(self.re * other.re - self.im * other.im,
                  self.re * other.im + self.im * other.re)

    def conj(self) -> CQ:
        return CQ(self.re, -self.im)

    def norm_sq(self) -> Q:
        return self.re**2 + self.im**2

    def scale(self, scalar: Q | int) -> CQ:
        return CQ(scalar * self.re, scalar * self.im)

    def __truediv__(self, other: CQ) -> CQ:
        return (self * other.conj()).scale(1 / other.norm_sq())

    def __pow__(self, exponent: int) -> CQ:
        assert exponent >= 0
        out = ONE
        base = self
        while exponent:
            if exponent & 1:
                out = out * base
            base = base * base
            exponent //= 2
        return out


ZERO = CQ()
ONE = CQ(Q(1))
I = CQ(Q(0), Q(1))


def csum(values: list[CQ]) -> CQ:
    out = ZERO
    for value in values:
        out = out + value
    return out


def act(matrix: list[list[Q]], vector: list[CQ]) -> list[CQ]:
    return [csum([value.scale(weight) for value, weight in zip(vector, row)])
            for row in matrix]


def inner(pi: list[Q], left: list[CQ], right: list[CQ]) -> CQ:
    return csum([(x.conj() * y).scale(p) for p, x, y in zip(pi, left, right)])


def path_variances(matrix: list[list[Q]], pi: list[Q], g: list[CQ],
                   horizon: int) -> list[Q]:
    """Propagate exact conditional path moments, without a covariance formula.

    At step k, a[j]=E[S_k 1_{X_(k-1)=j}], b[j]=E[|S_k|^2 1_{...}].
    """
    size = len(pi)
    mass = pi[:]
    first = [g[j].scale(pi[j]) for j in range(size)]
    second = [pi[j] * g[j].norm_sq() for j in range(size)]
    out = [Q(0), sum(second)]
    for _ in range(1, horizon):
        next_mass = [sum(mass[i] * matrix[i][j] for i in range(size))
                     for j in range(size)]
        next_first = [csum([(first[i] + g[j].scale(mass[i])).scale(matrix[i][j])
                           for i in range(size)]) for j in range(size)]
        next_second = [sum(matrix[i][j] *
                           (second[i] + 2 * (g[j].conj() * first[i]).re
                            + mass[i] * g[j].norm_sq())
                           for i in range(size)) for j in range(size)]
        mass, first, second = next_mass, next_first, next_second
        out.append(sum(second))
    return out


def exact_chain(name: str, matrix: list[list[Q]], pi: list[Q],
                g: list[CQ], lam: CQ, horizon: int = 18) -> dict[str, object]:
    size = len(pi)
    assert all(value >= 0 for row in matrix for value in row)
    assert all(sum(row) == 1 for row in matrix)
    assert sum(pi) == 1 and all(value > 0 for value in pi)
    assert [sum(pi[i] * matrix[i][j] for i in range(size))
            for j in range(size)] == pi
    assert act(matrix, g) == [lam * value for value in g]
    assert csum([value.scale(weight) for value, weight in zip(g, pi)]) == ZERO
    variance = inner(pi, g, g).re
    assert variance > 0 and lam.norm_sq() < 1

    power_g = g[:]
    for q in range(horizon + 1):
        assert inner(pi, g, power_g) == (lam**q).scale(variance)
        power_g = act(matrix, power_g)

    # Independent path-moment recursion versus both exact closed expressions.
    observed = path_variances(matrix, pi, g, horizon)
    dc = (1 - lam.norm_sq()) / (ONE - lam).norm_sq()
    for n in range(1, horizon + 1):
        triangular = Q(n) + 2 * sum((n-q) * (lam**q).re for q in range(1, n))
        correction = (lam * (ONE - lam**n) / ((ONE - lam)**2)).re
        closed = n * dc - 2 * correction
        assert observed[n] == variance * triangular == variance * closed

    # Finite algebra behind the stationary martingale-difference variance.
    u = [value / (ONE - lam) for value in g]
    innovations = sum(pi[i] * matrix[i][j] * (u[j] - lam * u[i]).norm_sq()
                      for i in range(size) for j in range(size))
    assert innovations == variance * dc

    # Rational points on the unit circle check the Poisson-kernel identity.
    for phase in [ONE, I, CQ(Q(3, 5), Q(-4, 5)), CQ(Q(-5, 13), Q(12, 13))]:
        mode = lam * phase
        assert phase.norm_sq() == 1
        spectrum = (1 - lam.norm_sq()) / (ONE - mode).norm_sq()
        assert spectrum == 1 + 2 * (mode / (ONE - mode)).re > 0

    lazy = [[(matrix[i][j] + Q(i == j)) / 2 for j in range(size)]
            for i in range(size)]
    eta = (ONE + lam).scale(Q(1, 2))
    assert act(lazy, g) == [eta * value for value in g]
    for q in range(horizon + 1):
        clock_sum = csum([(lam**k).scale(Q(comb(q, k), 2**q)) for k in range(q+1)])
        assert clock_sum == eta**q

    return {"name": name, "states": size, "horizons": horizon,
            "correlation_lags": horizon + 1, "poisson_kernel_points": 4,
            "lazy_clock_lags": horizon + 1}


def exact_regressions() -> dict[str, object]:
    g = [ONE, I, -ONE, -I]
    chains = []
    weights = [
        [Q(1, 2), Q(1, 2), Q(0), Q(0)],
        [Q(1, 3), Q(1, 2), Q(1, 6), Q(0)],
        [Q(1, 10), Q(1, 5), Q(3, 10), Q(2, 5)],
        [Q(0), Q(3, 4), Q(0), Q(1, 4)],
    ]
    for number, row in enumerate(weights, start=1):
        matrix = [[row[(j-i) % 4] for j in range(4)] for i in range(4)]
        lam = csum([g[j].scale(row[j]) for j in range(4)])
        chains.append(exact_chain(f"circulant-{number}", matrix, [Q(1, 4)] * 4, g, lam))

    # P=J+(1/6)K, Kx=-y, Ky=x, x=(1,-1,0), y=(1,0,-1).
    # E[g^2]=2i/3, so blindly replacing Re(g)'s covariance by Re(lambda^q)
    # is false. The rational real readout x+y is phase-aligned.
    matrix = [[Q(1, 3), Q(1, 2), Q(1, 6)],
              [Q(5, 18), Q(5, 18), Q(4, 9)],
              [Q(7, 18), Q(2, 9), Q(7, 18)]]
    pi = [Q(1, 3)] * 3
    mode = [CQ(Q(1), Q(1)), CQ(Q(-1)), CQ(Q(0), Q(-1))]
    lam = CQ(Q(0), Q(1, 6))
    chains.append(exact_chain("nonorthogonal-real-imaginary", matrix, pi, mode, lam))
    raw = [CQ(value.re) for value in mode]
    aligned = [CQ(value.re + value.im) for value in mode]
    assert inner(pi, raw, act(matrix, raw)).re != inner(pi, raw, raw).re * lam.re
    assert csum([(value * value).scale(weight) for weight, value in zip(pi, mode)]) == CQ(Q(0), Q(2, 3))
    power_aligned = aligned[:]
    for q in range(19):
        assert inner(pi, aligned, power_aligned).re == inner(pi, aligned, aligned).re * (lam**q).re
        power_aligned = act(matrix, power_aligned)
    aligned_variances = path_variances(matrix, pi, aligned, 18)
    for n in range(1, 19):
        predicted = n + 2 * sum((n-q) * (lam**q).re for q in range(1, n))
        assert aligned_variances[n] == inner(pi, aligned, aligned).re * predicted

    # Orientation and omission mutations are rejected on non-real modes.
    assert inner(pi, mode, act(matrix, mode)) != lam.conj().scale(inner(pi, mode, mode).re)
    dc = (1-lam.norm_sq()) / (ONE-lam).norm_sq()
    assert path_variances(matrix, pi, mode, 2)[2] != 2 * inner(pi, mode, mode).re * dc
    return {"chains": chains, "phase_aligned_real_horizons": 18,
            "mutations_rejected": 3,
            "scope": "Finite rational regressions; not universal proofs or clone root certificates"}


def numerical_diagnostics(delays: list[int]) -> list[dict[str, object]]:
    import mpmath as mp

    out: list[dict[str, object]] = []
    with mp.workdps(90):
        for n in delays:
            d = 2*n + 5
            D = mp.mpf(d) - mp.mpf("0.5")

            def equation(w: object, k: int) -> object:
                return d*w - mp.log(1+mp.exp(w)) - 2j*mp.pi*k

            w0 = mp.findroot(lambda w: equation(w, 0), mp.log(2)/D)
            w1 = mp.findroot(lambda w: equation(w, 1), (mp.log(2)+2j*mp.pi)/D)
            residual = max(abs(equation(w0, 0)), abs(equation(w1, 1)))
            assert residual < mp.mpf("1e-75")
            assert 2*mp.pi/d < mp.im(w1) < 2*mp.pi/(d-1)
            w = w1 - w0
            lam = mp.exp(w)
            rho, theta = abs(lam), mp.im(w)
            gamma = -mp.expm1(mp.re(w))
            assert 0 < rho < 1

            def spectrum(omega: object) -> object:
                return (1-rho*rho) / abs(1-lam*mp.exp(-1j*omega))**2

            dc = spectrum(0)
            peak = (1+rho)/gamma
            horizon = 2*d - 1
            variance = horizon*dc - 2*mp.re(lam*(-mp.expm1(horizon*w)) / (1-lam)**2)
            # Independent triangular covariance sum at the specified actual horizon.
            triangular = horizon + 2*mp.re(mp.fsum([(horizon-q)*lam**q for q in range(1, horizon)]))
            assert abs(variance-triangular) < mp.mpf("1e-65")
            eta = (1+lam)/2
            lorentz_error = max(abs(gamma*spectrum(theta+gamma*u)-2/(1+u*u))
                                for u in [-3, -1, 0, 1, 3])
            full_width = 4*mp.asin(gamma/(2*mp.sqrt(rho)))
            out.append({
                "delay": n, "D": mp.nstr(D, 12),
                "D_times_DC": mp.nstr(D*dc, 24),
                "peak_over_D_cubed": mp.nstr(peak/D**3, 24),
                "peak_DC_ratio_over_D_fourth": mp.nstr(peak/dc/D**4, 24),
                "two_rotation_sum_variance": mp.nstr(variance, 24),
                "two_rotation_correlation_envelope": mp.nstr(rho**horizon, 24),
                "D_squared_times_lazy_mode_gap": mp.nstr(D**2*(1-abs(eta)), 24),
                "D_squared_times_poisson_mode_rate": mp.nstr(D**2*(1-mp.re(lam)), 24),
                "quality_factor_over_D_squared": mp.nstr(theta/full_width/D**2, 24),
                "sampled_rescaled_profile_max_error": mp.nstr(lorentz_error, 12),
                "root_equation_residual": mp.nstr(residual, 8),
            })
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerics", action="store_true",
                        help="add 90-digit diagnostics; not certified enclosures")
    parser.add_argument("--output", type=Path, help="write a machine-readable JSON report")
    args = parser.parse_args()
    report: dict[str, object] = {"exact_regressions": exact_regressions(),
                                "numeric_status": "not requested"}
    print("PASS: 5 rational stationary chains; 90 path-variance horizons; "
          "18 phase-aligned real horizons; 3 mutations rejected")
    if args.numerics:
        report["numeric_status"] = "90-digit diagnostics, not certified enclosures"
        report["numeric_diagnostics"] = numerical_diagnostics([0, 2, 10, 50, 100, 500])
        print("DIAGNOSTIC only: D*S(0)->1/4; V_(2D)->1; D^2 lazy mode gap->pi^2/2")
        for row in report["numeric_diagnostics"]:
            print(f"  n={row['delay']:>3}  D*S(0)={row['D_times_DC']}  "
                  f"V_(2D)={row['two_rotation_sum_variance']}  "
                  f"D^2 lazy gap={row['D_squared_times_lazy_mode_gap']}")
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
