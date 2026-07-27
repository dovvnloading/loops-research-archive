"""Experiment 1: Decay of p/q-limb diameters vs the Yoccoz inequality.

Yoccoz's inequality gives limb diameter <= C/q (proved). The conjecturally
optimal bound is ~ C/q^2 (open refinement). We measure both the full limb
(with filaments, via DEM proximity) and the satellite component itself for
p/q limbs of the main cardioid, then fit the decay exponent in q.

Method per (p,q): root point on cardioid; small window around it; DEM grid;
mark cells in-or-near M; delete a tiny disk at the root to detach the limb
from the cardioid; flood-fill from a seed inside the satellite component;
diameter = max distance from root over the filled component. Window adapts
(doubles) if the component touches the frame.
"""
import json
import numpy as np
import sys
sys.path.insert(0, r"..")
from mlc_common import cardioid_root, cardioid_outward, dem_grid, flood_component, nearest_cell, in_mandelbrot

OUT = r"..\results\exp1_limbs.json"

GRID = 420


def find_seed(root, outward, p, q):
    """Point well inside the p/q satellite component (near its center),
    at distance ~ component scale from the root, so it clears the root
    cut-disk and avoids near-parabolic false positives."""
    base = 2.4 * abs(np.sin(np.pi * p / q)) / q ** 2
    for f in (0.9, 0.7, 1.1, 0.5, 1.3, 0.35, 1.6):
        h = f * base
        s = root + h * outward
        mu = 1 - np.sqrt(1 - 4 * s)  # main-cardioid test: inside iff |mu| < 1
        if abs(mu) < 1:
            continue
        if in_mandelbrot(s, 30000):
            return s, h
    return None, None


def measure_limb(p, q, grid=GRID):
    root = cardioid_root(p, q)
    outward = cardioid_outward(p, q)
    maxiter = int(max(6000, 140 * q * q))
    seed, h = find_seed(root, outward, p, q)
    if seed is None:
        return {"p": p, "q": q, "error": "no seed found"}
    W = max(30.0 / q ** 2, 6.0 * h)
    for _attempt in range(6):
        center = root + 0.30 * W * outward
        C, dist, escaped = dem_grid(center, W, grid, grid, maxiter)
        cell = W / grid
        near = (~escaped) | (dist < 1.4 * cell)
        # detach limb from the cardioid: erase a small disk at the root,
        # strictly inside the seed radius so the seed survives
        r_cut = min(max(2.5 * cell, 0.4 * h), 0.7 * h)
        near[np.abs(C - root) < r_cut] = False
        comp, touches = flood_component(near, nearest_cell(C, seed))
        if not comp.any():
            return {"p": p, "q": q, "error": "seed cell not marked", "h": h}
        pts = C[comp]
        limb_diam = float(np.max(np.abs(pts - root)))
        # interior-only fill = the satellite component body
        interior = (~escaped).copy()
        interior[np.abs(C - root) < r_cut] = False
        comp_int, _ = flood_component(interior, nearest_cell(C, seed))
        comp_diam = float(np.max(np.abs(C[comp_int] - root))) if comp_int.any() else None
        if touches:
            W *= 2.0
            continue
        if limb_diam < 0.12 * W and W > 20 * cell:
            W = max(3.2 * limb_diam, 24 * cell)
            continue
        return {
            "p": p, "q": q,
            "root": [root.real, root.imag],
            "limb_diameter": limb_diam,
            "component_extent": comp_diam,
            "window": W, "grid": grid, "maxiter": maxiter,
            "cells_in_limb": int(comp.sum()),
        }
    return {"p": p, "q": q, "error": "window did not stabilize", "limb_diameter": limb_diam, "window": W}


if __name__ == "__main__":
    jobs = [(1, q) for q in range(3, 21)] + [(2, 5), (2, 7), (3, 7), (2, 9), (3, 8), (4, 9), (2, 11), (3, 11), (5, 11), (2, 13), (5, 13)]
    results = []
    for p, q in jobs:
        r = measure_limb(p, q)
        results.append(r)
        print(f"p/q={p}/{q}: limb={r.get('limb_diameter')}, comp={r.get('component_extent')}, err={r.get('error')}", flush=True)
    # fit exponents on the p=1 series, q>=5
    series = [(r["q"], r["limb_diameter"]) for r in results
              if r.get("limb_diameter") and r["p"] == 1 and r["q"] >= 5 and "error" not in r]
    fit = None
    if len(series) >= 4:
        lq = np.log([s[0] for s in series])
        ld = np.log([s[1] for s in series])
        A = np.vstack([lq, np.ones_like(lq)]).T
        (slope, intercept), res, *_ = np.linalg.lstsq(A, ld, rcond=None)
        fit = {"exponent": float(slope), "prefactor": float(np.exp(intercept)),
               "n_points": len(series),
               "note": "limb diameter ~ prefactor * q^exponent; Yoccoz proves exponent <= -1, conjectured optimal -2"}
    with open(OUT, "w") as f:
        json.dump({"measurements": results, "fit_p1": fit}, f, indent=2)
    print("FIT:", fit)
