"""Experiment 1 (wake method): p/q-limb diameters via exact wake boundaries.

The p/q-limb is M intersected with the p/q-wake, the region bounded by the two
external rays landing at the p/q root of the main cardioid. The wake angles are
the adjacent pair m/(2^q-1), (m+1)/(2^q-1) in the doubling orbit of the
Sturmian rotation word of p/q (Douady-Hubbard / Goldberg-Milnor combinatorics).
We trace both rays, close the region through the root, and take the diameter of
the in-or-near-M grid points inside the polygon. No flood fill => no leakage.
"""
import json
from fractions import Fraction
from math import floor
import numpy as np
import sys
sys.path.insert(0, r"..")
from mlc_common import cardioid_root, dem_grid
from exp2_rays import trace_ray
from matplotlib.path import Path

OUT = r"..\results\exp1_limbs.json"

GRID = 700


def wake_angles(p, q):
    word = [floor((k + 1) * p / q) - floor(k * p / q) for k in range(q)]
    A = 0
    for b in word:
        A = (A << 1) | b
    mod = (1 << q) - 1
    orbit = set()
    x = A % mod
    for _ in range(q):
        orbit.add(x)
        x = (2 * x) % mod
    pair = [m for m in orbit if (m + 1) in orbit]
    assert len(pair) == 1, (p, q, sorted(orbit))
    m = pair[0]
    return Fraction(m, mod), Fraction(m + 1, mod)


def measure_limb(p, q, grid=GRID):
    root = cardioid_root(p, q)
    lo, hi = wake_angles(p, q)
    t_lo, c_lo = trace_ray(lo, t0=4.0, steps_per_halving=16, t_min=2e-9)
    t_hi, c_hi = trace_ray(hi, t0=4.0, steps_per_halving=16, t_min=2e-9)
    # polygon: down ray_lo (far->near), through the root, back up ray_hi.
    # Clip rays to a ~50/q^2 neighborhood of the root so the grid window
    # scales WITH the limb (Path auto-closes the far chord; the limb at
    # ~2.2/q^2 sits far inside it).
    R_clip = min(3.0, 50.0 / q ** 2)
    keep_lo = np.abs(c_lo - root) < R_clip
    keep_hi = np.abs(c_hi - root) < R_clip
    poly = np.concatenate([
        np.stack([c_lo[keep_lo].real, c_lo[keep_lo].imag], axis=1),
        np.array([[root.real, root.imag]]),
        np.stack([c_hi[keep_hi].real, c_hi[keep_hi].imag], axis=1)[::-1],
    ])
    path = Path(poly)
    # grid window: bounding box of the wake polygon + margin
    xmin, ymin = poly.min(axis=0)
    xmax, ymax = poly.max(axis=0)
    pad = 0.05 * max(xmax - xmin, ymax - ymin)
    cx, cy = (xmin + xmax) / 2, (ymin + ymax) / 2
    W = max(xmax - xmin, ymax - ymin) + 2 * pad
    maxiter = int(max(8000, 160 * q * q))
    C, dist, escaped = dem_grid(complex(cx, cy), W, grid, grid, maxiter)
    cell = W / grid
    near = (~escaped) | (dist < 1.0 * cell)
    pts = np.stack([C[near].real, C[near].imag], axis=1)
    inside = path.contains_points(pts)
    sel = pts[inside]
    if len(sel) == 0:
        return {"p": p, "q": q, "error": "no M points in wake"}
    z = sel[:, 0] + 1j * sel[:, 1]
    d = np.abs(z - root)
    limb_diam = float(d.max())
    tip = z[np.argmax(d)]
    return {
        "p": p, "q": q,
        "root": [root.real, root.imag],
        "wake_angles": [str(lo), str(hi)],
        "limb_diameter": limb_diam,
        "tip": [tip.real, tip.imag],
        "n_cells": int(inside.sum()),
        "window": W, "grid": grid, "maxiter": maxiter,
    }


if __name__ == "__main__":
    jobs = [(1, q) for q in range(2, 21)] + [(2, 5), (2, 7), (3, 7), (3, 8), (2, 9), (4, 9), (3, 10), (2, 11), (3, 11), (5, 11), (5, 12), (2, 13), (5, 13), (3, 14), (4, 15), (7, 15), (5, 16), (3, 17), (7, 16), (5, 17), (4, 17), (6, 17), (7, 18), (5, 18), (8, 19), (9, 19)]
    results = []
    for p, q in jobs:
        try:
            r = measure_limb(p, q)
        except Exception as e:
            r = {"p": p, "q": q, "error": repr(e)}
        results.append(r)
        print(f"p/q={p}/{q}: wake={r.get('wake_angles')}, limb={r.get('limb_diameter')}, err={r.get('error')}", flush=True)
    series = [(r["q"], r["limb_diameter"]) for r in results
              if r.get("limb_diameter") and r["p"] == 1 and r["q"] >= 5]
    fit = None
    if len(series) >= 4:
        lq = np.log([s[0] for s in series])
        ld = np.log([s[1] for s in series])
        A = np.vstack([lq, np.ones_like(lq)]).T
        (slope, intercept), *_ = np.linalg.lstsq(A, ld, rcond=None)
        fit = {"exponent": float(slope), "prefactor": float(np.exp(intercept)),
               "n_points": len(series),
               "note": "limb diameter ~ prefactor * q^exponent; Yoccoz proves O(1/q), conjectured optimal ~1/q^2"}
    # p-dependence at fixed q: sin(pi p / q) scaling check
    with open(OUT, "w") as f:
        json.dump({"measurements": results, "fit_p1": fit, "method": "wake-polygon"}, f, indent=2)
    print("FIT:", fit)
