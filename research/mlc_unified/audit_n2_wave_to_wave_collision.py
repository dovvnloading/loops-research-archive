"""Diagnostic checks for the analytic construction in
kkl_stationary_n2_wave_to_wave_collision.md.

The script checks numerical identities and separation margins only.
The proof obligations are discharged analytically in the note.
"""

from __future__ import annotations

import cmath
import math


R = 75.0
P = 100.0
BETA = 2.0 * math.pi / P
DELTA = math.exp(2.0 * BETA) - 1.0
A = math.sqrt(R * R - (P / 2.0) ** 2)


def immersion(z: complex) -> complex:
    return (cmath.exp(BETA * (z + 1.0)) - 1.0) / DELTA


def cover(z: complex) -> complex:
    return z * z


def lower(x: float) -> complex:
    return complex(x, -P / 2.0)


def upper(x: float) -> complex:
    return complex(x, P / 2.0)


def run() -> None:
    assert math.isclose(A, 25.0 * math.sqrt(5.0), rel_tol=0.0, abs_tol=1e-12)

    samples = [(-A + 2.0 * A * j / 1000.0) for j in range(1001)]
    immersion_error = max(abs(immersion(lower(x)) - immersion(upper(x))) for x in samples)
    cover_error = max(abs(cover(lower(x)) - cover(upper(-x))) for x in samples)
    assert immersion_error < 1e-10
    assert cover_error < 1e-10

    eta = [immersion(lower(x)) for x in samples]
    assert max(abs(z.imag) for z in eta) < 1e-10
    assert max(z.real for z in eta) < 0.0
    assert all(eta[j + 1].real < eta[j].real for j in range(len(eta) - 1))

    delta = [cover(lower(x)) for x in samples]
    assert max(abs(z) for z in delta[1:-1]) < R * R
    assert math.isclose(abs(delta[0]), R * R, rel_tol=0.0, abs_tol=1e-8)
    assert math.isclose(abs(delta[-1]), R * R, rel_tol=0.0, abs_tol=1e-8)
    assert min(abs(z - 0.5) for z in delta) > 1.0

    u = immersion(lower(-A)).real
    v = immersion(lower(A)).real
    assert v < u < 0.0
    assert max(abs(u), abs(v)) < 400.0

    print("PASS: periodic immersion equality")
    print("PASS: quadratic deck-image equality")
    print("PASS: eta is a simple negative-real interval")
    print("PASS: common cover image is a proper outer-to-outer arc")
    print(f"margins: A={A:.12f}, u={u:.12f}, v={v:.12f}")


if __name__ == "__main__":
    run()
