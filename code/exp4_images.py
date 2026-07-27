"""Experiment 4: DEM imagery of the geometric phenomena behind MLC.

  (a) overview of M;
  (b) Feigenbaum point at two zoom levels separated by factor delta —
      near-identical frames = renormalization self-similarity + Milnor
      hairiness (proved by Lyubich);
  (c) high-q satellite limb (1/9) — thin, decoration-dominated geometry,
      the degeneration that kills uniform a priori bounds for satellites;
  (d) primitive period-3 'airplane' copy — bounded geometry, the regime
      where Kahn-Lyubich a priori bounds hold.
"""
import numpy as np
import sys
sys.path.insert(0, r"..")
from mlc_common import dem_grid, cardioid_root
from matplotlib.colors import LinearSegmentedColormap
import matplotlib.pyplot as plt

FIGS = r"..\figs"

# palette: exterior far = near-white surface, approaching boundary = blue ramp -> deep navy; interior = near-black ink
CMAP = LinearSegmentedColormap.from_list(
    "mlcblue", ["#0d366b", "#1c5cab", "#3987e5", "#86b6ef", "#cde2fb", "#fcfcfb"])
INTERIOR = "#0b0b0b"


def render(name, center, width, maxiter, nx=1000, ny=750):
    C, dist, escaped = dem_grid(complex(*center), width, nx, ny, maxiter)
    cell = width / nx
    img = np.zeros(C.shape)
    d = np.where(escaped, dist, np.nan)
    with np.errstate(invalid="ignore", divide="ignore"):
        v = np.log(np.maximum(d, 1e-300) / cell)
    lo, hi = np.nanpercentile(v, 1), np.nanpercentile(v, 99.5)
    v = np.clip((v - lo) / max(hi - lo, 1e-9), 0, 1)
    rgba = CMAP(v)
    ink = np.array([11, 11, 11, 255]) / 255.0
    rgba[~escaped] = ink
    plt.imsave(rf"{FIGS}\{name}.png", rgba[::-1], dpi=150)
    print("saved", name, flush=True)


if __name__ == "__main__":
    delta = 4.669201609102990
    c_F = -1.4011551890920506
    render("m_overview", (-0.6, 0.0), 3.2, 4000)
    render("feig_zoom1", (c_F, 0.0), 0.012, 60000)
    render("feig_zoom2", (c_F, 0.0), 0.012 / delta, 120000)
    r9 = cardioid_root(1, 9)
    render("satellite_limb_1_9", (r9.real + 0.13 * 0.4, r9.imag + 0.10 * 0.4), 0.42, 30000)
    render("primitive_airplane", (-1.7590, 0.0), 0.055, 30000)
    # satellite cascade along the 1/2-limb: nested satellite structure near -1.4 tip region
    render("cascade_window", (-1.30, 0.0), 0.62, 20000)
