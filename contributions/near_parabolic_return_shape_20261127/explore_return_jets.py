#!/usr/bin/env python3
"""Numerical exploration only: not a certificate, proof, or Lean substitute.

Uses floating-point mpmath and heuristic bisections to select candidate
noncentral collisions. It proves neither uniqueness, the Shot predicate,
an enclosure, nor any statement uniform in the period.
"""
import mpmath as m

m.mp.dps = 60


def H(t, x):
    q = m.mpf(7) / 4 - t
    return q - ((q - x * x) ** 2 - q) ** 2


def iterate(t, x, n):
    for _ in range(n):
        x = H(t, x)
    return x


def track(t, k):
    x = m.mpf(0)
    for _ in range(k):
        x = min(m.mpf(".4"), H(t, x))
    return x


def bisect_candidate(f, a, b, target, steps=180):
    # Monotonicity and root bracketing are not certified by this routine.
    for _ in range(steps):
        z = (a + b) / 2
        if f(z) > target:
            b = z
        else:
            a = z
    return (a + b) / 2


def main():
    print("NUMERICAL EXPLORATION ONLY; NO MATHEMATICAL CERTIFICATE")
    print("k t e collision_residual second_exit A_times_e B_times_e_cubed")
    for k in (4, 8, 16, 32, 64, 128):
        a = bisect_candidate(
            lambda t: track(t, k), m.mpf(0), m.mpf(".01"), m.mpf(".35")
        )
        b = bisect_candidate(
            lambda t: track(t, k), m.mpf(0), m.mpf(".01"), m.mpf(".38")
        )
        center = bisect_candidate(lambda t: -iterate(t, 0, k + 2), a, b, 0)

        def parameter_at_e(e):
            return bisect_candidate(
                lambda t: -iterate(t, 0, k + 2), a, center, -e, 130
            )

        elo, ehi = m.mpf("0.0000001"), m.mpf(".01")
        for _ in range(90):
            e = (elo + ehi) / 2
            t = parameter_at_e(e)
            if iterate(t, e, k) > m.mpf(".39"):
                ehi = e
                continue
            if iterate(t, e, k + 2) + e < 0:
                ehi = e
            else:
                elo = e
        e = (elo + ehi) / 2
        t = parameter_at_e(e)
        c = -m.mpf(7) / 4 + t
        value, quadratic, quartic = 0, 0, 0
        for j in range(3 * (k + 2)):
            quartic = 2 * value * quartic + quadratic * quadratic
            quadratic = 2 * value * quadratic + (1 if j == 0 else 0)
            value = value * value + c
        print(
            k,
            m.nstr(t, 12),
            m.nstr(e, 12),
            m.nstr(iterate(t, e, k + 2) + e, 4),
            m.nstr(iterate(t, e, k), 8),
            m.nstr(quadratic * e, 12),
            m.nstr(quartic * e**3, 12),
            flush=True,
        )


if __name__ == "__main__":
    main()
