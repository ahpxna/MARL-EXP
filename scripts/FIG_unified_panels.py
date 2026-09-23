#!/usr/bin/env python3
"""Figures from saved JSON plus explicitly labelled algebraic illustrations.

No experiment is rerun. Historical JSON is preserved. Legacy claims about exact LP
certificates, measured stopping costs, and observed breakpoints must not be inferred
from these figures. Hypothetical scaling curves are labelled as proxies.
"""

import json
import math
import os
import sys
from fractions import Fraction

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SRC = "research/unified_20260919"
OUT = "research/papers/_figures"

plt.rcParams.update({
    "font.size": 8, "axes.labelsize": 8, "axes.titlesize": 8.5,
    "legend.fontsize": 7, "xtick.labelsize": 7, "ytick.labelsize": 7,
    "figure.dpi": 200, "savefig.dpi": 200, "axes.grid": True,
    "grid.alpha": 0.25, "grid.linewidth": 0.5, "lines.linewidth": 1.3,
})


def load(name):
    with open(os.path.join(SRC, name)) as f:
        data = json.load(f)
    if not data.get("all_passed", False):
        raise ValueError(f"Refusing failed or unvalidated experiment artifact: {name}")
    return data


def fig_support_decision():
    """Panel 1: the support reverses the ranking, and where the decision flips."""
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    # left: full cube vs support, on the fixed witness
    g = load("geometry_decision.json")["partA"]
    names = ["retain 1", "retain 2", "retain 3"]
    LX = [float(Fraction(g["L_X"][k])) for k in ["[0]", "[1]", "[2]"]]
    LK = [float(Fraction(g["L_K"][k])) for k in ["[0]", "[1]", "[2]"]]
    x = np.arange(3)
    ax[0].bar(x - 0.19, LX, 0.36, label="full cube $L_X$", color="#4C72B0")
    ax[0].bar(x + 0.19, LK, 0.36, label="support $L_K$", color="#DD8452")
    ax[0].set_xticks(x); ax[0].set_xticklabels(names)
    ax[0].set_ylabel("compression loss")
    ax[0].set_title(r"Top-C is optimal on $X$, worst on $K$  ($\delta_I=0$)")
    ax[0].legend(frameon=False)
    ax[0].annotate("Top-C", xy=(0 - 0.19, LX[0]), xytext=(0 - 0.55, LX[0] + 0.45),
                   arrowprops=dict(arrowstyle="->", lw=0.7), fontsize=7)

    # right: the theta family, the two loss curves and the flip point
    t = np.linspace(0, 1, 201)
    ax[1].plot(t, 2 - t, label=r"$L_\theta(\{1\}) = 2-\theta$")
    ax[1].plot(t, 0.5 + t, label=r"$L_\theta(\{2\}) = \frac{1}{2}+\theta$")
    ax[1].axvline(0.75, color="k", ls="--", lw=0.8)
    ax[1].annotate(r"$\theta_*=\frac{3}{4}$", xy=(0.75, 1.25), xytext=(0.40, 1.72),
                   arrowprops=dict(arrowstyle="->", lw=0.7), fontsize=7)
    ax[1].set_xlabel(r"$\theta$"); ax[1].set_ylabel("loss on $K$")
    ax[1].set_title("the decision flips at an exact point")
    ax[1].legend(frameon=False, loc="upper center")
    fig.tight_layout()
    fig.savefig(f"{OUT}/unified_support_decision.pdf")
    plt.close(fig)
    return "unified_support_decision.pdf"


def fig_calibration():
    """Panel 2: cost against theta, and the phase where nothing need be measured."""
    d = load("calibration_game.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    alpha = 0.01
    for eps, style in [(0.05, "-"), (0.2, "--"), (0.4, ":")]:
        ts = np.linspace(0, 1, 301)
        gam = 9 * (np.abs(ts - 0.75) + eps / 2) ** 2 / (2 * (1 + 1) ** 2)
        ax[0].plot(ts, math.log(1 / alpha) / gam, style,
                   label=rf"$\varepsilon={eps}$")
    ax[0].set_yscale("log")
    ax[0].axvline(0.75, color="k", ls="--", lw=0.8)
    ax[0].set_xlabel(r"$\theta$")
    ax[0].set_ylabel(r"$\log(1/\alpha)/\Gamma_{\rm comp}$")
    ax[0].set_title(r"information-based cost proxy (no stopping guarantee)")
    ax[0].legend(frameon=False)

    # right: numeric vs closed form, all cells
    rows = d["rows"]
    num = np.array([r["numeric"] for r in rows])
    cf = np.array([r["closed_form"] for r in rows])
    keep = cf > 0
    ax[1].loglog(cf[keep], num[keep], "o", ms=2.5, alpha=0.65)
    lo, hi = float(cf[keep].min()), float(cf[keep].max())
    ax[1].loglog([lo, hi], [lo, hi], "k--", lw=0.8)
    ax[1].set_xlabel(r"closed form $\Gamma_{\rm comp}$")
    ax[1].set_ylabel("blind optimiser")
    ax[1].set_title(f"agreement to {d['worst_rel_err']:.1e} over {len(rows)} cells")
    fig.tight_layout()
    fig.savefig(f"{OUT}/unified_calibration.pdf")
    plt.close(fig)
    return "unified_calibration.pdf"


def fig_oracle_gap():
    """Panel 3: what the certificate costs over the decision."""
    d = load("oracle_gap_corrected_v2.json")
    rows = d["rows"]
    fig, ax = plt.subplots(figsize=(3.4, 2.5))
    cs = [r["c"] for r in rows]
    finite = [(r["c"], r["cost_ratio"]) for r in rows
              if not isinstance(r["cost_ratio"], str)
              and r["cost_ratio"] != float("inf") and r["cost_ratio"] < 1e12]
    fc = [p[0] for p in finite]; fr = [p[1] for p in finite]
    ax.semilogy(fc, fr, "o-", ms=3.5, color="#C44E52")
    dead = min((r["c"] for r in rows
                if isinstance(r["cost_ratio"], str)
                or r["cost_ratio"] == float("inf")), default=None)
    if dead is not None:
        ax.axvline(dead, color="k", ls="--", lw=0.8)
        ax.annotate("certificate\nunattainable", xy=(dead, max(fr) * 0.25),
                    xytext=(dead - 0.55, max(fr) * 0.03), fontsize=7,
                    arrowprops=dict(arrowstyle="->", lw=0.7))
    ax.set_xlabel(r"interaction $c$  ($\delta_I = c$)")
    ax.set_ylabel("cost ratio  certificate / decision")
    ax.set_title("the margin certificate is the expensive part")
    fig.tight_layout()
    fig.savefig(f"{OUT}/unified_oracle_gap.pdf")
    plt.close(fig)
    return "unified_oracle_gap.pdf"


def fig_query_order():
    """Panel 4: the measured Hellinger order against the predicted 2s."""
    d = load("query_order_corrected_v2.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    for row in d["hellinger"]:
        h = np.array(row["h"]); H2 = np.array(row["H2"])
        ax[0].loglog(h, H2, "o-", ms=3,
                     label=fr"$n={row['n']},d={row['d']}$ ($s={row['s']}$)")
    ax[0].set_xlabel("$h$"); ax[0].set_ylabel(r"$H^2$")
    ax[0].set_title(r"measured slopes, within tolerance of $2s$")
    ax[0].legend(frameon=False, fontsize=6)

    s_pred = [2 * r["s"] for r in d["hellinger"]]
    s_meas = [r["slope"] for r in d["hellinger"]]
    ax[1].plot(s_pred, s_meas, "o", ms=5, color="#55A868")
    lim = [min(s_pred) - 0.6, max(s_pred) + 0.6]
    ax[1].plot(lim, lim, "k--", lw=0.8)
    ax[1].set_xlim(lim); ax[1].set_ylim(lim)
    ax[1].set_xlabel(r"predicted slope $2s=2\lceil n/d\rceil$")
    ax[1].set_ylabel("measured slope")
    ax[1].set_title("measured against predicted; quadrature error uncertified")
    for xp, yp, r in zip(s_pred, s_meas, d["hellinger"]):
        ax[1].annotate(fr"$d={r['d']}$", (xp, yp), textcoords="offset points",
                       xytext=(5, -7), fontsize=6)
    fig.tight_layout()
    fig.savefig(f"{OUT}/unified_query_order.pdf")
    plt.close(fig)
    return "unified_query_order.pdf"


def fig_obstruction():
    """Panel 5: deciding against identifying."""
    d = load("obstruction_order_corrected_v2.json")
    fig, ax = plt.subplots(figsize=(3.4, 2.5))
    h = np.array([r["h"] for r in d["cost"]])
    cd = np.array([r["cost_decide"] for r in d["cost"]])
    ci = np.array([r["cost_identify"] for r in d["cost"]])
    ax.loglog(h, cd, "o-", ms=3.5, label=fr"decide  ($r_{{\rm safe}}={d['r_safe']}$)")
    ax.loglog(h, ci, "s-", ms=3.5, label=fr"identify  ($r_{{\rm id}}={d['r_id']}$)")
    ax.invert_xaxis()
    ax.set_xlabel("$h$"); ax.set_ylabel("unit-constant exponent proxy")
    ax.set_title(f"{d['n_worlds']} assigned-order worlds; illustrative scaling")
    ax.legend(frameon=False)
    fig.tight_layout()
    fig.savefig(f"{OUT}/unified_obstruction.pdf")
    plt.close(fig)
    return "unified_obstruction.pdf"


def fig_structural_frontier():
    """Panel 6: the frontier in eta, and where the separation dies."""
    d = load("structural_frontier_corrected_v2.json")
    etas = d["etas"]
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    for m in sorted(d["frontier"], key=int):
        vals = d["frontier"][m]
        free = float(Fraction(d["V_free"][m]))
        ax[0].plot(etas, [v / free if v is not None else np.nan for v in vals],
                   "o-", ms=3, label=f"$m={m}$")
    ax[0].axhline(1.0, color="k", ls="--", lw=0.8)
    ax[0].set_xlabel(r"$\eta$")
    ax[0].set_ylabel(r"$V^{(\eta)}_{\rm avg}/V^{\rm free}_{\rm avg}$")
    ax[0].set_title("the relative price along the band")
    ax[0].legend(frameon=False, ncol=2, fontsize=6)

    # Plot only saved solver values. The previous panel hard-coded conjectured
    # breakpoints, including m=10,11 absent from the JSON; it was not measured data.
    for m in sorted(d["frontier"], key=int):
        free = float(Fraction(d["V_free"][m]))
        excess = [v - free if v is not None else np.nan for v in d["frontier"][m]]
        ax[1].plot(etas, excess, "o-", ms=3, label=f"$m={m}$")
    ax[1].axhline(0.0, color="k", ls="--", lw=0.8)
    ax[1].set_xlabel(r"$\eta$")
    ax[1].set_ylabel(r"$V^{(\eta)}-V^{\rm free}$")
    ax[1].set_title("saved floating-point LP values; no breakpoint certificate")
    ax[1].legend(frameon=False, ncol=2, fontsize=6)
    fig.tight_layout()
    fig.savefig(f"{OUT}/unified_structural_frontier.pdf")
    plt.close(fig)
    return "unified_structural_frontier.pdf"


def fig_geometry_kappa():
    """Panel 7: can the geometry-rate threshold ever fire?"""
    d = load("geometry_kappa.json")
    rows = d["threshold_by_support_size"]
    fig, ax = plt.subplots(figsize=(3.4, 2.5))
    for m in sorted({r["m"] for r in rows}):
        rs = [r for r in rows if r["m"] == m]
        x = [r["support_fraction"] for r in rs]
        ye = [100.0 * r["fired_exact"] / max(r["instances"], 1) for r in rs]
        yc = [100.0 * r["fired_cheap"] / max(r["instances"], 1) for r in rs]
        ax.plot(x, ye, "o-", ms=4, label=fr"exact, $m={m}$")
        ax.plot(x, yc, "s--", ms=4, label=fr"$O(m)$ bound, $m={m}$")
    ax.set_ylim(-4, 104)
    ax.set_xlabel(r"$|K|/|X|$")
    ax.set_ylabel("threshold fires (\% of instances)")
    ax.set_title("the measurable rate is sound but vacuous")
    ax.legend(frameon=False, fontsize=6, loc="center left")
    fig.tight_layout()
    fig.savefig(f"{OUT}/unified_geometry_kappa.pdf")
    plt.close(fig)
    return "unified_geometry_kappa.pdf"


def main():
    os.makedirs(OUT, exist_ok=True)
    made = []
    for fn in [fig_support_decision, fig_calibration, fig_oracle_gap,
               fig_query_order, fig_obstruction, fig_structural_frontier,
               fig_geometry_kappa]:
        try:
            made.append(fn())
            print(f"  wrote {made[-1]}")
        except Exception as e:
            print(f"  FAILED {fn.__name__}: {e}", file=sys.stderr)
            return 1
    print(f"\n{len(made)} figures written to {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
