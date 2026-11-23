#!/usr/bin/env python3
"""Render the two distinct spectral-clock results from declared exact/data sources.

Requires matplotlib and numpy.  Rendering is a numerical illustration, not a
proof or certificate.  No fitted parameters or external imagery are used.
"""
from pathlib import Path
import json
import math

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figs/research/spectral_clocks_20261123"
DATA = ROOT / "results/clone_renewal_clock_20261123.json"


def main() -> None:
    report = json.loads(DATA.read_text())
    rows = report["numeric_diagnostics"]
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 10,
        "axes.spines.top": False, "axes.spines.right": False,
        "svg.hashsalt": "loops-spectral-clocks-20261123", "savefig.facecolor": "white",
    })
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(12, 6.3),
                                gridspec_kw={"width_ratios": [1, 1.1]})
    fig.subplots_adjust(left=.07, right=.97, bottom=.26, top=.79, wspace=.30)
    fig.suptitle("Return clocks carry information beyond leading growth",
                 fontsize=17, weight="bold", y=.97)
    fig.text(.5, .90, "Two different matrices, with separate proofs of their dynamical meaning",
             ha="center", fontsize=10, color="#495563")
    phi = (1 + math.sqrt(5)) / 2
    theta = np.linspace(0, 2 * np.pi, 361)
    colors = ["#0072B2", "#D55E00", "#009E73"]
    markers = ["o", "s", "^"]
    for s, color, marker in zip([1, 3, 9], colors, markers, strict=True):
        roots = []
        for sign in [1, -1]:
            radius = phi ** (sign / s)
            angles = (2 * np.pi * np.arange(s) + (0 if sign == 1 else np.pi)) / s
            roots.extend(radius * np.exp(1j * angles))
            ax.plot(radius * np.cos(theta), radius * np.sin(theta), color=color,
                    lw=.65, alpha=.3)
        roots = np.asarray(roots)
        ax.scatter(roots.real, roots.imag, s=46, c=color, marker=marker,
                   label=f"Clock {s}: {2*s} roots", edgecolors="white", linewidths=.55,
                   zorder=3)
    ax.plot(np.cos(theta), np.sin(theta), "--", color="#64748B", lw=.8, alpha=.7)
    ax.axhline(0, color="#CBD5E1", lw=.65)
    ax.axvline(0, color="#CBD5E1", lw=.65)
    ax.set(xlim=(-1.75, 1.85), ylim=(-1.75, 1.75), xlabel="Real part", ylabel="Imaginary part")
    ax.set_aspect("equal")
    ax.set_title("A. Actual period-27 quadratic interval matrix", fontsize=10, pad=12)
    ax.legend(loc="lower left", fontsize=8, framealpha=.95)
    ax.annotate(r"Leading root $\varphi$", (phi, 0), xytext=(.55, 1.55), fontsize=9,
                arrowprops={"arrowstyle": "->", "color": "#475569", "lw": .8})
    ax.text(.5, -.23,
            r"$\det(\lambda I-A)=\prod_{s\in\{1,3,9\}}(\lambda^{2s}-\lambda^s-1)$",
            transform=ax.transAxes, ha="center", fontsize=11)

    D = np.asarray([float(row["D"]) for row in rows])
    entropy_time = np.asarray([1 / float(row["log_entropy_rate"]) for row in rows])
    correlation_time = np.asarray([float(row["correlation_efolding_time"]) for row in rows])
    grid = np.geomspace(D.min(), D.max(), 200)
    bx.loglog(grid, grid / np.log(2), color="#0072B2", lw=1.1, ls="--", alpha=.75)
    bx.loglog(grid, 2 * grid**3 / np.pi**2, color="#D55E00", lw=1.1, ls="--", alpha=.75)
    bx.scatter(D, entropy_time, color="#0072B2", s=36, marker="o",
               label=r"Growth scale $1/\log t_n$", zorder=3)
    bx.scatter(D, correlation_time, color="#D55E00", s=40, marker="s",
               label=r"Correlation scale $1/\log(t_n/r_n)$", zorder=3)
    bx.set(xlabel=r"Centered cycle length $D=2n+9/2$", ylabel="Number of one-step iterations")
    bx.set_title("B. Primitive clone and its affine interval realization", fontsize=10, pad=12)
    bx.grid(which="major", color="#E2E8F0", lw=.7)
    bx.legend(loc="upper left", fontsize=8, frameon=False)
    bx.text(.5, -.23, r"Dashed guides: $D/\log 2$ and $2D^3/\pi^2$",
            transform=bx.transAxes, ha="center", fontsize=10)
    fig.text(.07, .035,
             "Left: numerical display of exact characteristic roots. Right: 90-digit diagnostic values.\n"
             "The determinant and asymptotic proofs are in the companion notes; the figure is not a proof or an empirical measurement.",
             fontsize=8, color="#495563", va="bottom")
    OUT.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUT.with_suffix(".svg"), metadata={"Date": None,
                 "Title": "Two distinct spectral clocks in the loops research archive",
                 "Description": "Exact quadratic Markov spectral factors and diagnostic clone correlation times; distinct matrices."})
    svg = OUT.with_suffix(".svg")
    svg.write_text("\n".join(line.rstrip() for line in svg.read_text().splitlines()) + "\n")
    fig.savefig(OUT.with_suffix(".png"), dpi=170)
    plt.close(fig)
    print(OUT.with_suffix(".svg").relative_to(ROOT))
    print(OUT.with_suffix(".png").relative_to(ROOT))


if __name__ == "__main__":
    main()
