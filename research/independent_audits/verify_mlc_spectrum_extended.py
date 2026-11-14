#!/usr/bin/env python3
"""Exact finite Jungreis coefficients and Mandelbrot Laurent packet energies.

Implements the Ewing--Schober beta recursion and certifies every coefficient
by forward composition with a Faber polynomial. The published OEIS table
provides a separate comparison for the first 28 scaled integers.

Sources:
Ewing--Schober, On the coefficients of the mapping to the exterior of the
Mandelbrot set (1990), https://doi.org/10.1307/mmj/1029004138 .
Ewing--Schober, The Area of the Mandelbrot Set (Numer. Math. 61, 1992).
OEIS A331814, https://oeis.org/A331814 .
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as Q
from math import isqrt, log, pi, sin
from pathlib import Path

# OEIS A331814, a(n) = 2^(2n+1) b_n, indexed from b_0; published sequence.
PUBLISHED_SCALED_28 = (
    -1, 1, -8, 15, 0, -94, -512, 987, 0, -7346, 65536, -122058,
    0, -2757820, -22020096, 59250963, 0, -329425898, 2617245696,
    -4805611678, -34359738368, -19403249316, 498216206336,
    -36302282082, 0, 14136557849100, -71399536328704,
    -88183884706356,
)


def jungreis_coefficients(last_index: int) -> list[Q]:
    """Compute b_0,...,b_last_index, all exactly.

    The Ewing--Schober beta recursion is (m >= 1, k >= 1):
    beta(k-1,m) = 0 if m < 2^k-1; otherwise
      (beta(k,m) - beta(0,m-2^k+1)
       - sum_{a=2^k-1}^{m-2^k+1} beta(k-1,a) beta(k-1,m-a)) / 2.
    All beta(k,0)=1; all sufficiently high beta(k,m) vanish for m>0;
    b_n=beta(0,n+1). Read m in increasing order and k in reverse order.
    """
    if last_index < 0:
        raise ValueError("last_index must be nonnegative")
    layers = (last_index + 3).bit_length() + 1
    beta = [[Q(1)] for _ in range(layers)]
    for m in range(1, last_index + 2):
        for k in range(layers - 1, 0, -1):
            threshold = (1 << k) - 1
            if m < threshold:
                value = Q(0)
            else:
                conv = sum(
                    (beta[k - 1][a] * beta[k - 1][m - a]
                     for a in range(threshold, m - threshold + 1)),
                    Q(0),
                )
                value = (beta[k][m] - beta[0][m - threshold] - conv) / 2
            beta[k - 1].append(value)
        beta[-1].append(Q(0))
    return beta[0][1:last_index + 2]


def verify_prefix(coefficients: list[Q]) -> None:
    assert len(coefficients) >= len(PUBLISHED_SCALED_28)
    for n, expected in enumerate(PUBLISHED_SCALED_28):
        actual = coefficients[n] * (1 << (2 * n + 1))
        assert actual == expected, (n, actual, expected)
    for number in coefficients:
        assert number.denominator & (number.denominator - 1) == 0


def verify_faber_composition(coefficients: list[Q]) -> None:
    """Check p_k(Psi(w)) = w^(2^k) + O(1/w) through the supplied prefix.

    Put t=1/(4w), X=Psi(w)/w, and Y=p_k(Psi(w))/w^d for d=2^k.
    Start with d=1, Y=X. The forward orbit p -> p^2 + c gives
    Y_next = Y^2 + (4t)^(2d-1) X. All operations are truncated at degree
    len(coefficients), and scaling makes the coefficients integers.

    At d >= len(coefficients) the Faber identity forces Y=1 through that
    degree. This determines every checked coefficient: the first change
    at degree j in X changes Y_j by d times that change, since the
    derivative in X at t=0, X=1 is d.
    """
    order = len(coefficients)
    source = [1]
    for j, value in enumerate(coefficients, 1):
        scaled = value * (1 << (2 * j))
        if scaled.denominator != 1:
            raise ValueError(f"coefficient b_{j - 1} does not have integral scaling")
        source.append(scaled.numerator)

    series = source
    degree = 1
    while degree < max(order, 2):
        degree *= 2
        shift = degree - 1
        square = [
            sum(series[i] * series[j - i] for i in range(j + 1))
            for j in range(order + 1)
        ]
        for j in range(shift, order + 1):
            square[j] += source[j - shift] << (2 * shift)
        series = square
    for j in range(1, order + 1):
        if series[j] != 0:
            raise ValueError(f"degree-{degree} Faber identity fails at b_{j - 1}")


def verify_finite_lemma_steps() -> None:
    """Only sample elementary finite inequalities, never an infinite proof."""
    # Integral comparison for reciprocal harmonic block, checked at finite j.
    for j in range(0, 9):
        a = 1 << j
        harmonic = sum((Q(1, n) for n in range(a, 2 * a)), Q(0))
        assert float(harmonic) < log(2) + 1 / a

    # m*(sin(pi/m)/2) tends to pi/2, and 2^J << 4^m.
    # These finite tests only catch algebraic or index mistakes.
    for m in (8, 16, 32, 64, 128, 256):
        root_ceiling = isqrt(m)
        if root_ceiling * root_ceiling < m:
            root_ceiling += 1
        J = 2 * m - root_ceiling
        assert m < J < 2 * m
        assert 1 << J < 4**m
        assert 0 < m * sin(pi / m) / 2 < pi / 2


def exact_manifest(last_index: int) -> dict:
    coefficients = jungreis_coefficients(last_index)
    verify_prefix(coefficients)
    verify_faber_composition(coefficients)
    verify_finite_lemma_steps()
    zero_indices = [n for n in range(1, last_index + 1) if coefficients[n] == 0]
    packets = []
    for j in range(last_index.bit_length()):
        lower = 1 << j
        if lower > last_index:
            break
        upper = min((1 << (j + 1)) - 1, last_index)
        exact = sum((n * coefficients[n] ** 2 for n in range(lower, upper + 1)), Q(0))
        packets.append({
            "j": j, "n_min": lower, "n_max": upper,
            "energy_exact": str(exact), "energy_float_for_display_only": float(exact),
        })
    energy_sum = sum((n * coefficients[n] ** 2 for n in range(1, last_index + 1)), Q(0))
    sequence = "".join(f"{n}:{value}\n" for n, value in enumerate(coefficients))
    digest = hashlib.sha256(sequence.encode("ascii")).hexdigest()
    return {
        "scope": "finite rational arithmetic only; no proof of MLC, ray landing or asymptotic tail",
        "last_index": last_index,
        "recurrence": "Ewing-Schober (1992) beta recurrence",
        "published_prefix_check": "OEIS A331814 first 28 scaled integers",
        "independent_full_check": "forward Faber polynomial composition through every supplied coefficient",
        "exact_coefficient_sha256": digest,
        "coefficient_count": len(coefficients),
        "zero_indices": zero_indices,
        "weighted_area_partial_energy_exact": str(energy_sum),
        "weighted_area_partial_energy_float_for_display_only": float(energy_sum),
        "gronwall_area_upper_bound_over_pi_exact": str(1 - energy_sum),
        "dyadic_packets": packets,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-index", type=int, default=127)
    parser.add_argument("--check-manifest", type=Path, default=None)
    options = parser.parse_args()
    if options.max_index < 27:
        parser.error("--max-index must be >= 27 for the independent published check")
    actual = exact_manifest(options.max_index)
    if options.check_manifest is not None:
        expected = json.loads(options.check_manifest.read_text(encoding="utf-8"))
        if actual != expected:
            raise SystemExit(f"Manifest mismatch: {options.check_manifest}")
        print("PASS: published coefficient prefix, full Faber identity, rational packets and locked manifest")
        print(f"n={options.max_index} coefficients={actual['coefficient_count']} "
              f"zeroes={len(actual['zero_indices'])} "
              f"sha256={actual['exact_coefficient_sha256']}")
    else:
        print(json.dumps(actual, indent=2, ensure_ascii=True) + "\n")


if __name__ == "__main__":
    main()
