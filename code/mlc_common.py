"""Shared numerics for the MLC experiment suite.

Distance-estimator (DEM/M) grids, cardioid geometry, and flood fill.
All complex-plane computations vectorized with numpy float64/complex128.
"""
import numpy as np
from collections import deque

ESCAPE_R = 1e10


def cardioid_root(p, q):
    """Root point of the p/q-limb on the main cardioid: c = mu/2 - mu^2/4, mu=e^{2 pi i p/q}."""
    mu = np.exp(2j * np.pi * p / q)
    return mu / 2 - mu * mu / 4


def cardioid_outward(p, q):
    """Unit outward direction at the p/q root (radial image direction d c(r mu)/dr at r=1)."""
    mu = np.exp(2j * np.pi * p / q)
    v = mu * (1 - mu) / 2
    return v / abs(v)


def dem_grid(center, width, nx, ny, maxiter):
    """Distance-estimator grid for the Mandelbrot set.

    Returns (C, dist, escaped): dist is the exterior distance estimate
    (np.inf where never escaped => in/near M), escaped is a bool mask.
    """
    x = np.linspace(center.real - width / 2, center.real + width / 2, nx)
    hy = width * ny / nx
    y = np.linspace(center.imag - hy / 2, center.imag + hy / 2, ny)
    C = x[None, :] + 1j * y[:, None]
    Z = np.zeros_like(C)
    W = np.zeros_like(C)  # dZ/dc
    dist = np.full(C.shape, np.inf)
    alive = np.ones(C.shape, dtype=bool)
    # active-set compaction
    idx = np.flatnonzero(alive.ravel())
    z = Z.ravel()[idx].copy()
    w = W.ravel()[idx].copy()
    c = C.ravel()[idx].copy()
    dist_flat = dist.ravel()
    for _ in range(maxiter):
        w = 2 * z * w + 1
        z = z * z + c
        esc = np.abs(z) > ESCAPE_R
        if esc.any():
            ze, we = z[esc], w[esc]
            az = np.abs(ze)
            d = az * np.log(az) / np.maximum(np.abs(we), 1e-300)
            dist_flat[idx[esc]] = d
            keep = ~esc
            idx, z, w, c = idx[keep], z[keep], w[keep], c[keep]
        if idx.size == 0:
            break
    dist = dist_flat.reshape(C.shape)
    escaped = np.isfinite(dist)
    return C, dist, escaped


def flood_component(mask, seed_rc):
    """8-connected flood fill on a boolean mask from seed (row, col). Returns component mask."""
    ny, nx = mask.shape
    comp = np.zeros_like(mask)
    r0, c0 = seed_rc
    if not mask[r0, c0]:
        return comp, False
    dq = deque([(r0, c0)])
    comp[r0, c0] = True
    while dq:
        r, c = dq.popleft()
        for dr in (-1, 0, 1):
            for dc in (-1, 0, 1):
                rr, cc = r + dr, c + dc
                if 0 <= rr < ny and 0 <= cc < nx and mask[rr, cc] and not comp[rr, cc]:
                    comp[rr, cc] = True
                    dq.append((rr, cc))
    touches_edge = comp[0, :].any() or comp[-1, :].any() or comp[:, 0].any() or comp[:, -1].any()
    return comp, touches_edge


def nearest_cell(C, point):
    k = np.argmin(np.abs(C.ravel() - point))
    return np.unravel_index(k, C.shape)


def in_mandelbrot(c, maxiter):
    """Scalar membership test by escape iteration."""
    z = 0j
    for _ in range(maxiter):
        z = z * z + c
        if abs(z) > 4.0:
            return False
    return True
