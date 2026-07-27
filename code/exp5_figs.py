"""Publication figures from the experiment JSONs — light and dark variants.

Palette per the dataviz reference instance; single axis, thin marks, direct
labels, recessive grid. Charts:
  fig_rays   — distance-to-landing vs potential for four ray types (log-log)
  fig_delta  — convergence of cascade ratios to Feigenbaum delta (semilog)
  fig_limbs  — p/q-limb diameter vs q with q^-1 (Yoccoz) and q^-2 guides (log-log)
"""
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BASE = r".."
RES, FIGS = BASE + r"\results", BASE + r"\figs"

MODES = {
    "light": dict(surface="#fcfcfb", ink="#0b0b0b", ink2="#52514e", muted="#898781",
                  grid="#e1e0d9", axis="#c3c2b7",
                  s1="#2a78d6", s2="#eb6834", s3="#1baf7a", s4="#eda100"),
    "dark": dict(surface="#1a1a19", ink="#ffffff", ink2="#c3c2b7", muted="#898781",
                 grid="#2c2c2a", axis="#383835",
                 s1="#3987e5", s2="#d95926", s3="#199e70", s4="#c98500"),
}


def style_ax(ax, P):
    ax.set_facecolor(P["surface"])
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    for s in ("left", "bottom"):
        ax.spines[s].set_color(P["axis"])
    ax.tick_params(colors=P["muted"], labelsize=9)
    ax.grid(True, color=P["grid"], linewidth=0.7, alpha=1.0)
    ax.set_axisbelow(True)
    ax.xaxis.label.set_color(P["ink2"])
    ax.yaxis.label.set_color(P["ink2"])
    ax.title.set_color(P["ink"])


def new_fig(P, w=7.6, h=4.6):
    f, ax = plt.subplots(figsize=(w, h), dpi=160)
    f.patch.set_facecolor(P["surface"])
    return f, ax


def fig_rays(mode):
    P = MODES[mode]
    with open(RES + r"\exp2_rays.json") as f:
        rays = {r["label"]: r for r in json.load(f)}
    picks = [
        ("ray 1/4 (preperiodic)", "Misiurewicz (ray 1/4)", "s1", None, (-8, 10)),
        ("ray 1/3 (period-2 root)", "parabolic root (ray 1/3)", "s2", complex(-0.75, 0), (-8, 10)),
        ("ray 1/7 (1/3-satellite root)", "satellite root (ray 1/7)", "s3", None, (-8, -18)),
        ("Thue-Morse ray -> Feigenbaum point", "Feigenbaum (Thue–Morse ray)", "s4", complex(-1.4011551890920506, 0), (-8, -18)),
    ]
    f, ax = new_fig(P)
    for label, name, slot, known, off in picks:
        r = rays[label]
        path = np.array(r["path"])
        t, cr, ci = path[:, 0], path[:, 1], path[:, 2]
        c = cr + 1j * ci
        if known is None:
            if "known_landing_point" in r:
                ref = complex(*r["known_landing_point"])
            else:
                ref = c[-1]
                keep = t > t[-1] * 30  # self-referenced: drop the biased tail
                t, c = t[keep], c[keep]
        else:
            ref = known
        d = np.abs(c - ref)
        good = d > 1e-15
        ax.plot(t[good], d[good], color=P[slot], lw=2, label=name)
        ax.annotate(name, (t[good][-1], d[good][-1]),
                    textcoords="offset points", xytext=off,
                    color=P[slot], fontsize=9, ha="right")
    leg = ax.legend(frameon=False, fontsize=8.5, loc="lower left")
    for txt in leg.get_texts():
        txt.set_color(P["ink2"])
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.invert_xaxis()
    ax.set_xlabel("potential t along the ray  (→ landing as t → 0)")
    ax.set_ylabel("distance to landing point")
    ax.set_title("How external rays land: four regimes of convergence")
    style_ax(ax, P)
    f.tight_layout()
    f.savefig(FIGS + rf"\fig_rays_{mode}.png", facecolor=P["surface"])
    plt.close(f)


def fig_delta(mode):
    P = MODES[mode]
    with open(RES + r"\exp3_feigenbaum.json") as f:
        d = json.load(f)
    ratios = np.array([float(x) for x in d["delta_ratios"]])
    delta_ref = 4.669201609102990671853
    err = np.abs(ratios - delta_ref)
    n = np.arange(2, 2 + len(ratios))
    f_, ax = new_fig(P, w=7.0, h=4.2)
    ax.plot(n, err, color=P["s1"], lw=2, marker="o", ms=6,
            markerfacecolor=P["s1"], markeredgecolor=P["surface"])
    ax.set_yscale("log")
    ax.set_xlabel("cascade level n  (superstable period 2ⁿ)")
    ax.set_ylabel("|δₙ − δ|")
    ax.set_title("Feigenbaum δ from the cascade — geometric convergence")
    ax.annotate("δ = 4.6692016… (cascade)\nδ = 4.6692015… (operator spectrum)\nα² = 6.2645…  ⇒  α = 2.5029…",
                xy=(0.97, 0.95), xycoords="axes fraction", ha="right", va="top",
                color=P["ink2"], fontsize=9)
    style_ax(ax, P)
    f_.tight_layout()
    f_.savefig(FIGS + rf"\fig_delta_{mode}.png", facecolor=P["surface"])
    plt.close(f_)


def fig_limbs(mode):
    P = MODES[mode]
    with open(RES + r"\exp1_limbs.json") as f:
        data = json.load(f)
    runA = sorted((int(k), v) for k, v in data["runA_p1_coarse"].items())
    msB = [m for m in data["measurements"] if m.get("limb_diameter") and "error" not in m
           and "excluded" not in m]
    p1B = sorted((m["q"], m["limb_diameter"]) for m in msB if m["p"] == 1)
    px = [(m["q"], m["limb_diameter"]) for m in msB if m["p"] != 1]
    f, ax = new_fig(P)
    qA = np.array([x[0] for x in runA]); dA = np.array([x[1] for x in runA])
    qB = np.array([x[0] for x in p1B]); dB = np.array([x[1] for x in p1B])
    ax.plot(qA, dA, "o", color=P["s1"], ms=8, markeredgecolor=P["surface"],
            label="p = 1, run A (coarse grid — upper-biased)")
    ax.plot(qB, dB, "s", color=P["s3"], ms=6.5, markeredgecolor=P["surface"],
            label="p = 1, run B (fine grid — lower-biased at high q)")
    if px:
        qx = np.array([x[0] for x in px]); dx = np.array([x[1] for x in px])
        ax.plot(qx, dx, "D", color=P["s2"], ms=6, markeredgecolor=P["surface"], label="p ≠ 1 limbs")
    qq = np.linspace(2, max(qA), 60)
    anchor_q, anchor_d = 5, float(dA[qA == 5][0])
    ax.plot(qq, anchor_d * (qq / anchor_q) ** -1.0, "--", color=P["muted"], lw=1.5)
    ax.annotate("Yoccoz bound  ∝ 1/q", (qq[-1], anchor_d * (qq[-1] / anchor_q) ** -1.0),
                textcoords="offset points", xytext=(-2, 8), color=P["muted"], fontsize=9, ha="right")
    ax.plot(qq, anchor_d * (qq / anchor_q) ** -2.0, "--", color=P["ink2"], lw=1.5)
    ax.annotate("conjectured  ∝ 1/q²", (qq[-1], anchor_d * (qq[-1] / anchor_q) ** -2.0),
                textcoords="offset points", xytext=(-2, 8), color=P["ink2"], fontsize=9, ha="right")
    ax.annotate("measured slopes: q^−2.4 (A) · q^−2.8 (B)\nboth far below the proven 1/q line",
                xy=(0.03, 0.06), xycoords="axes fraction", color=P["ink"], fontsize=10)
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel("q  (limb rotation number p/q)")
    ax.set_ylabel("limb diameter")
    ax.set_title("Limb size decay: the data lives near the conjectured line, not the proven one")
    leg = ax.legend(frameon=False, fontsize=8.5, loc="lower left", bbox_to_anchor=(0.0, 0.14))
    for txt in leg.get_texts():
        txt.set_color(P["ink2"])
    style_ax(ax, P)
    f.tight_layout()
    f.savefig(FIGS + rf"\fig_limbs_{mode}.png", facecolor=P["surface"])
    plt.close(f)


if __name__ == "__main__":
    import sys
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    for mode in ("light", "dark"):
        if which in ("all", "rays"):
            fig_rays(mode)
        if which in ("all", "delta"):
            fig_delta(mode)
        if which in ("all", "limbs"):
            try:
                fig_limbs(mode)
            except FileNotFoundError:
                print("limb data not ready")
    print("figures done:", which)
