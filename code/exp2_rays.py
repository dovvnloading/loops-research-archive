"""Experiment 2: Parameter-space external rays of the Mandelbrot set.

MLC is equivalent to: every external ray R_theta lands, and the landing map
theta -> gamma(theta) is continuous (Caratheodory / pinched-disk model).
Here we trace rays numerically (Newton continuation on z_n(c) = w^{2^n},
the standard Jungreis-style algorithm) and measure landing:

  - rational rays with known landing points (1/2 -> -2; 1/3, 2/3 -> -3/4;
    1/7 -> root of the 1/3-satellite on the main cardioid),
  - the Thue-Morse-angle ray, whose landing point is the Feigenbaum
    parameter c_F: this ray's landing is a THEOREM only since Dudko-Lyubich
    2023 (MLC at Feigenbaum points). We watch it converge.

Angles are handled exactly: rationals via Fraction, the Thue-Morse angle via
its binary digits (doubling the angle = shifting the digit stream), so no
precision is lost at depth 2^n.
"""
import json
from fractions import Fraction
import numpy as np

OUT = r"..\results\exp2_rays.json"

LOG_TARGET = 16.0  # aim 2^n * t in [LOG_TARGET, 2*LOG_TARGET); |target| in [9e6, 8e13]


def thue_morse_digit(i):
    return bin(i).count("1") & 1


def make_angle_fn(theta):
    """Return fn(n) = fractional part of 2^n * theta, exactly shifted."""
    if isinstance(theta, Fraction):
        def fn(n):
            return float((theta * (2 ** n)) % 1)
        return fn
    if theta == "thue-morse":
        def fn(n, bits=64):
            acc = 0.0
            p = 0.5
            for i in range(bits):
                if thue_morse_digit(n + i):
                    acc += p
                p *= 0.5
            return acc
        return fn
    raise ValueError(theta)


def trace_ray(theta, t0=6.0, steps_per_halving=24, t_min=1e-11, max_newton=12):
    angle_of = make_angle_fn(theta)
    th0 = angle_of(0)
    c = complex(np.exp(t0) * np.cos(2 * np.pi * th0), np.exp(t0) * np.sin(2 * np.pi * th0))
    ts, cs = [], []
    t = t0
    ratio = 2 ** (-1.0 / steps_per_halving)
    while t > t_min:
        # after n iterations of z -> z^2 + c (z_1 = c), z_n ~ Phi_M(c)^{2^{n-1}}
        m = max(0, int(np.ceil(np.log2(LOG_TARGET / t))))  # depth exponent: 2^m * t in [LT, 2LT)
        n = m + 1
        frac = angle_of(m)
        target = np.exp(complex((2 ** m) * t, 2 * np.pi * frac))
        c_anchor = c
        for _ in range(max_newton):
            z = 0j
            dz = 0j
            blown = False
            for _ in range(n):
                dz = 2 * z * dz + 1
                z = z * z + c
                if abs(z) > 1e140 or abs(dz) > 1e290:
                    blown = True
                    break
            if blown or not np.isfinite(z.real):
                c = 0.5 * (c + c_anchor)  # backtrack toward last on-ray point
                continue
            step = (z - target) / dz
            # damp huge steps to keep continuation on-branch
            if abs(step) > 0.4 * max(abs(c), 0.1):
                step *= 0.4 * max(abs(c), 0.1) / abs(step)
            c = c - step
            if abs(step) < 1e-14 * max(1.0, abs(c)):
                break
        ts.append(t)
        cs.append(c)
        t *= ratio
    return np.array(ts), np.array(cs)


def landing_report(theta, label, known=None, **kw):
    ts, cs = trace_ray(theta, **kw)
    end = cs[-1]
    # Cauchy-style tail increments as landing evidence
    tail = np.abs(np.diff(cs[-24:]))
    report = {
        "label": label,
        "endpoint_c": [end.real, end.imag],
        "final_potential": float(ts[-1]),
        "max_tail_increment": float(tail.max()),
        "n_points": len(ts),
        "path": [[float(ts[i]), float(cs[i].real), float(cs[i].imag)]
                 for i in range(0, len(ts), 4)],
    }
    if known is not None:
        report["known_landing_point"] = [known.real, known.imag]
        report["distance_to_known"] = float(abs(end - known))
    # sample of distances along the ray for Holder-rate fit
    if known is not None:
        d = np.abs(cs - known)
        good = d > 1e-14
        report["potential_vs_distance"] = [
            [float(ts[i]), float(d[i])] for i in range(0, len(ts), 12) if good[i]
        ]
        lt, ld = np.log(ts[good][-200:]), np.log(d[good][-200:])
        A = np.vstack([lt, np.ones_like(lt)]).T
        slope, _ = np.linalg.lstsq(A, ld, rcond=None)[0]
        report["holder_rate_along_ray"] = float(slope)
    return report


def cardioid_root(p, q):
    mu = np.exp(2j * np.pi * p / q)
    return mu / 2 - mu * mu / 4


if __name__ == "__main__":
    c_F = -1.4011551890920506  # from exp3 cascade
    reports = [
        landing_report(Fraction(1, 2), "ray 1/2 (tip)", known=complex(-2.0, 0.0)),
        landing_report(Fraction(1, 3), "ray 1/3 (period-2 root)", known=complex(-0.75, 0.0)),
        landing_report(Fraction(2, 3), "ray 2/3 (period-2 root)", known=complex(-0.75, 0.0)),
        landing_report(Fraction(1, 7), "ray 1/7 (1/3-satellite root)", known=cardioid_root(1, 3)),
        landing_report(Fraction(2, 7), "ray 2/7 (1/3-satellite root)", known=cardioid_root(1, 3)),
        landing_report(Fraction(1, 4), "ray 1/4 (preperiodic)", known=None),
        landing_report("thue-morse", "Thue-Morse ray -> Feigenbaum point", known=complex(c_F, 0.0), t_min=2e-14),
    ]
    with open(OUT, "w") as f:
        json.dump(reports, f, indent=2)
    for r in reports:
        print(r["label"], "-> c =", r["endpoint_c"],
              "| dist to known:", r.get("distance_to_known"),
              "| tail increment:", r["max_tail_increment"])
