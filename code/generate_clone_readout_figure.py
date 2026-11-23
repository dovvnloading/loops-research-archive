#!/usr/bin/env python3
"""Illustrate clone readout and clock formulas at the declared delay n=50.

Requires matplotlib and mpmath. All values are evaluated from the closed
formulas in research/independent_audits/clone_resonant_readout_20261123.md.
Roots and cancellation-sensitive variance expressions use 90 decimal digits.
This is a diagnostic illustration, not a proof or an empirical measurement.
"""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figs/research/clone_readout_20261123"
DELAY = 50


def main() -> None:
    with mp.workdps(90):
        d = 2 * DELAY + 5
        D = mp.mpf(d) - mp.mpf("0.5")

        def root_equation(w: object, k: int) -> object:
            return d * w - mp.log(1 + mp.exp(w)) - 2j * mp.pi * k

        w0 = mp.findroot(lambda w: root_equation(w, 0), mp.log(2) / D)
        w1 = mp.findroot(lambda w: root_equation(w, 1), (mp.log(2) + 2j * mp.pi) / D)
        assert max(abs(root_equation(w0, 0)), abs(root_equation(w1, 1))) < mp.mpf("1e-75")
        assert 2 * mp.pi / d < mp.im(w1) < 2 * mp.pi / (d - 1)
        lam = mp.exp(w1 - w0)
        rho = abs(lam)
        eta = (1 + lam) / 2

        # Integer lags/windows, including the exactly tuned N=2D=209.
        lags = list(range(4 * d - 1))
        windows = list(range(1, 4 * d - 1))
        x_lags = [float(q / D) for q in lags]
        original_covariance = [float(mp.re(lam**q)) for q in lags]
        rotating_covariance = [float(rho**q) for q in lags]

        def average_variance(mode: object, count: int) -> object:
            dc = (1 - abs(mode)**2) / abs(1 - mode)**2
            variance = count * dc - 2 * mp.re(mode * (1 - mode**count) / (1 - mode)**2)
            assert variance > 0
            return variance / count**2

        x_windows = [float(count / D) for count in windows]
        original_average = [float(average_variance(lam, count)) for count in windows]
        rotating_average = [float(average_variance(rho, count)) for count in windows]
        tuned_count = 2 * d - 1
        tuned_variance = float(average_variance(lam, tuned_count))

        # Mean genuine iteration count is exactly m for all three clocks:
        # deterministic m; Binomial(2m,1/2); independent Poisson(m).
        max_mean = int(mp.floor(mp.mpf("0.4") * D**2))
        means = sorted({k * max_mean // 400 for k in range(401)})
        x_means = [float(m / D**2) for m in means]
        deterministic_envelope = [float(rho**m) for m in means]
        bernoulli_envelope = [float(abs(eta)**(2*m)) for m in means]
        poisson_envelope = [float(mp.exp(m * (mp.re(lam)-1))) for m in means]

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 9,
        "axes.spines.top": False, "axes.spines.right": False,
        "svg.hashsalt": "loops-clone-readout-20261123",
        "savefig.facecolor": "white",
    })
    blue, orange, green = "#0072B2", "#D55E00", "#009E73"
    fig, (ax, bx, cx) = plt.subplots(1, 3, figsize=(12, 4))
    fig.subplots_adjust(left=.060, right=.985, bottom=.235, top=.755, wspace=.34)
    fig.suptitle("Same clone, different readouts and clocks", fontsize=16, weight="bold", y=.98)
    fig.text(.5, .885,
             r"Delay $n=50$  ·  $D=104.5$  ·  Unit-variance observables  ·  Closed formulas evaluated at 90 digits",
             ha="center", color="#475569", fontsize=9)

    ax.plot(x_lags, original_covariance, color=blue, lw=1.65, label="Original real readout")
    ax.plot(x_lags, rotating_covariance, color=orange, lw=1.85, label="Rotating reference")
    ax.axhline(0, color="#CBD5E1", lw=.7, zorder=0)
    ax.set(xlim=(0, 4), ylim=(-1.12, 1.17), xlabel=r"Iteration lag $q/D$",
           ylabel="Normalized covariance", xticks=[0, 1, 2, 3, 4])
    ax.set_title("A. Rotation persists inside the envelope", fontsize=10, pad=10)
    ax.legend(loc="lower left", fontsize=7.7, framealpha=.96, borderpad=.45)

    bx.semilogy(x_windows, original_average, color=blue, lw=1.65, label="Original real readout")
    bx.semilogy(x_windows, rotating_average, color=orange, lw=1.85, label="Rotating reference")
    bx.scatter([2], [tuned_variance], s=29, color=blue, edgecolors="white", lw=.65, zorder=5)
    bx.annotate(r"Tuned window" + "\n" + r"$N=2D=209$", xy=(2, tuned_variance),
                xytext=(.15, 1.3e-5), fontsize=8, color="#334155",
                arrowprops={"arrowstyle": "->", "lw": .8, "color": "#64748B"})
    bx.set(xlim=(0, 4), ylim=(7e-6, 1.8), xlabel=r"Averaging window $N/D$",
           ylabel="Variance of the average", xticks=[0, 1, 2, 3, 4])
    bx.set_title("B. Tuned averaging cancels rotations", fontsize=10, pad=10)
    bx.grid(axis="y", which="major", color="#E2E8F0", lw=.6)

    cx.plot(x_means, deterministic_envelope, color=blue, lw=1.8, label="Deterministic clock")
    cx.plot(x_means, bernoulli_envelope, color=orange, lw=1.8, label="Bernoulli holding")
    cx.plot(x_means, poisson_envelope, color=green, lw=1.8, label="Poisson clock")
    cx.set(xlim=(0, .4), ylim=(-.025, 1.06), xlabel=r"Equal mean iterations $m/D^2$",
           ylabel="Correlation envelope", xticks=[0, .1, .2, .3, .4])
    cx.set_title("C. Equal means give different decay", fontsize=10, pad=10)
    cx.legend(loc="center right", fontsize=7.7, frameon=False)
    cx.grid(axis="y", color="#E2E8F0", lw=.6)

    fig.text(.06, .058,
             "Diagnostic illustration of proved formulas for constructed affine-map systems; no empirical measurements.\n"
             "The rotating reference adds an independent uniform phase. Clock comparisons use exactly equal expected iteration counts.",
             fontsize=8, color="#475569", va="bottom")
    OUT.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUT.with_suffix(".svg"), metadata={
        "Date": None,
        "Title": "Clone readouts and independent clocks at delay n=50",
        "Description": "Diagnostic numerical illustration of explicit covariance, averaging variance, and equal-mean clock formulas.",
        "Creator": "loops-research-archive generate_clone_readout_figure.py",
    })
    svg = OUT.with_suffix(".svg")
    svg.write_text("\n".join(line.rstrip() for line in svg.read_text().splitlines()) + "\n")
    fig.savefig(OUT.with_suffix(".png"), dpi=180,
                metadata={"Software": "loops-research-archive generate_clone_readout_figure.py"})
    plt.close(fig)
    print(OUT.with_suffix(".svg").relative_to(ROOT))
    print(OUT.with_suffix(".png").relative_to(ROOT))


if __name__ == "__main__":
    main()
