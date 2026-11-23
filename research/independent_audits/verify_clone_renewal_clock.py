#!/usr/bin/env python3
"""Exact finite clone/renewal identities, with optional numerical diagnostics.

The default uses only Python integers in Z[x]/(x^d-x-1). It verifies
the actual full adjacency rows, Perron-change-of-coordinates rows,
stationary weights, and return-time normalization for declared finite
delays. It is a regression, not a proof of the universal analytic theorem.

--numerics requires mpmath. Its root residuals and asymptotic values are
high-precision diagnostics, never interval certificates or proofs.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from verify_full_clone_adjacency import edge_targets


class QuotientRing:
    """Integer polynomial arithmetic modulo x^d-x-1, with fixed-length values."""

    def __init__(self, degree: int) -> None:
        if degree < 3:
            raise ValueError("degree must be at least 3")
        self.d = degree
        self.zero = (0,) * degree
        self.one = (1,) + (0,) * (degree - 1)
        self.x = (0, 1) + (0,) * (degree - 2)

    def reduce(self, coefficients: list[int]) -> tuple[int, ...]:
        out = coefficients + [0] * max(0, self.d - len(coefficients))
        # x^k = x^(k-d+1) + x^(k-d) for k >= d.
        for k in range(len(out) - 1, self.d - 1, -1):
            out[k - self.d] += out[k]
            out[k - self.d + 1] += out[k]
            out[k] = 0
        return tuple(out[: self.d])

    def add(self, a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
        return tuple(x + y for x, y in zip(a, b, strict=True))

    def scale(self, k: int, a: tuple[int, ...]) -> tuple[int, ...]:
        return tuple(k * x for x in a)

    def mul(self, a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
        out = [0] * (2 * self.d - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        out[i + j] += x * y
        return self.reduce(out)

    def sum(self, values: list[tuple[int, ...]]) -> tuple[int, ...]:
        out = self.zero
        for value in values:
            out = self.add(out, value)
        return out


def exact_check(n: int) -> dict[str, int]:
    d = 2 * n + 5
    ring = QuotientRing(d)
    powers = [ring.one]
    for _ in range(d):
        powers.append(ring.mul(powers[-1], ring.x))
    assert powers[d] == ring.add(ring.x, ring.one)

    # For odd d, (1+x) * (x^(d-1)-x^(d-2)+...+x^2-x) = 1 mod p.
    a = tuple(0 if j == 0 else (-1) ** j for j in range(d))
    b = ring.mul(ring.x, a)
    assert ring.mul(ring.add(ring.one, ring.x), a) == ring.one
    assert ring.add(a, b) == ring.one

    h = [powers[i] if i <= n else ring.mul(powers[i], a) for i in range(d)]
    rows = [edge_targets(n, i) for i in range(d)]
    p_rows: list[dict[int, tuple[int, ...]]] = []
    for i, targets in enumerate(rows):
        assert ring.sum([h[j] for j in targets]) == ring.mul(ring.x, h[i])
        p_rows.append({n + 1: a, n + 2: b} if i == n else {targets[0]: ring.one})

    checked_similarity_rows = 0
    for i in range(d):
        assert ring.sum(list(p_rows[i].values())) == ring.one
        for j in range(d):
            lhs = h[j] if j in rows[i] else ring.zero
            rhs = ring.mul(ring.mul(ring.x, h[i]), p_rows[i].get(j, ring.zero))
            assert lhs == rhs, (n, i, j, "similarity")
            checked_similarity_rows += 1

    # Unnormalized stationary law q: every visited vertex has mass 1,
    # except the skipped vertex, whose per-excursion occupancy is a.
    q = [a if i == n + 1 else ring.one for i in range(d)]
    for j in range(d):
        incoming = ring.sum(
            [ring.mul(q[i], p_rows[i].get(j, ring.zero)) for i in range(d)]
        )
        assert incoming == q[j], (n, j, "stationarity")
    mean = ring.add(ring.scale(d, ring.one), ring.scale(-1, b))
    assert ring.sum(q) == mean
    assert ring.add(ring.scale(d, a), ring.scale(d - 1, b)) == mean

    # Mutation checks: a changed geometric row or reversed branch weights
    # must break the spectral/normalization identification.
    wrong_targets = (n + 1, n + 3)
    assert ring.sum([h[j] for j in wrong_targets]) != ring.mul(ring.x, h[n])
    assert h[n + 1] != ring.mul(ring.mul(ring.x, h[n]), b)
    assert h[n + 1] != ring.mul(ring.x, h[n])  # removed shortcut

    return {"delay": n, "vertices": d, "similarity_entries": checked_similarity_rows,
            "mutations_rejected": 3}


def numerical_diagnostics(delays: list[int]) -> list[dict[str, object]]:
    import mpmath as mp

    data: list[dict[str, object]] = []
    with mp.workdps(90):
        for n in delays:
            d = 2 * n + 5
            D = mp.mpf(d) - mp.mpf("0.5")

            def equation(w: object, k: int) -> object:
                return d * w - mp.log(1 + mp.exp(w)) - 2j * mp.pi * k

            w0 = mp.findroot(lambda w: equation(w, 0), mp.log(2) / D)
            w1 = mp.findroot(lambda w: equation(w, 1), (mp.log(2) + 2j * mp.pi) / D)
            t, z = mp.exp(w0), mp.exp(w1)
            r = abs(z)
            assert abs(mp.im(t)) < mp.mpf("1e-75")
            t = mp.re(t)
            assert 1 < r < t < 2
            assert 2 * mp.pi / d < mp.im(w1) < 2 * mp.pi / (d - 1)
            root_residual = max(abs(equation(w0, 0)), abs(equation(w1, 1)))
            assert root_residual < mp.mpf("1e-75")
            a, b = 1 / (1 + t), t / (1 + t)
            mean = d - b
            h = [t**i if i <= n else t**i / (1 + t) for i in range(d)]
            v = [z**i if i <= n else z**i / (1 + z) for i in range(d)]
            g = [v[i] / h[i] for i in range(d)]
            pi = [a / mean if i == n + 1 else 1 / mean for i in range(d)]
            centered_residual = abs(sum(pi[i] * g[i] for i in range(d)))
            assert centered_residual < mp.mpf("1e-70")
            log_ratio = mp.re(w0) - mp.re(w1)
            gap = -mp.expm1(-log_ratio)
            data.append({
                "delay": n,
                "vertices": d,
                "D": mp.nstr(D, 12),
                "perron_root": mp.nstr(t, 28),
                "subleading_modulus": mp.nstr(r, 28),
                "relative_gap": mp.nstr(gap, 24),
                "D_cubed_times_relative_gap": mp.nstr(D**3 * gap, 24),
                "target_pi_squared_over_two": mp.nstr(mp.pi**2 / 2, 24),
                "log_entropy_rate": mp.nstr(mp.log(t), 24),
                "correlation_efolding_time": mp.nstr(1 / log_ratio, 24),
                "root_equation_residual": mp.nstr(root_residual, 8),
                "centering_residual": mp.nstr(centered_residual, 8),
            })
    return data


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerics", action="store_true",
                        help="include high-precision diagnostics (not interval certificates)")
    parser.add_argument("--output", type=Path, help="write the report JSON to this path")
    args = parser.parse_args()
    exact = [exact_check(n) for n in [*range(17), 24, 32]]
    report: dict[str, object] = {
        "scope": "Finite exact quotient-ring regressions; not an all-delay analytic proof",
        "polynomial": "x^(2*n+5)-x-1",
        "exact_checks": exact,
        "numeric_status": "not requested",
    }
    print(f"PASS: {len(exact)} exact clone/renewal checks; "
          f"{sum(row['similarity_entries'] for row in exact)} similarity entries; "
          f"{sum(row['mutations_rejected'] for row in exact)} mutations rejected")
    if args.numerics:
        report["numeric_status"] = "90-digit diagnostics, not certified enclosures"
        report["numeric_diagnostics"] = numerical_diagnostics([0, 2, 10, 50, 100, 500])
        print("DIAGNOSTIC only: D^3(1-r/t) should tend to pi^2/2.")
        for row in report["numeric_diagnostics"]:
            print(f"  n={row['delay']:>3}  d={row['vertices']:>4}  "
                  f"D^3 gap={row['D_cubed_times_relative_gap']}")
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
