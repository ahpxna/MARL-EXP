#!/usr/bin/env python3
"""Two panels for the artifacts added in the closing round.

Evidence classes are printed on every panel and mean what they say:

    EXACT        rational arithmetic or a verified certificate
    NUMERICAL    a solved value or a measured quantity, floating point
    MONTE CARLO  an estimate with its uncertainty shown

Neither panel plots a formula as if it were data, and where a run never stopped the point is
drawn as censored rather than placed at the budget.
"""

import json
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

IN = "research/unified_20260919"
OUT = "research/papers/_figures"
plt.rcParams.update({"font.size": 7, "axes.linewidth": 0.6,
                     "xtick.major.width": 0.6, "ytick.major.width": 0.6})


def load(name):
    with open(f"{IN}/{name}") as f:
        return json.load(f)


def tag(ax, text):
    ax.text(0.02, 0.98, text, transform=ax.transAxes, va="top", ha="left",
            fontsize=5.5, color="#444", bbox=dict(boxstyle="round,pad=0.2",
                                                  fc="white", ec="#bbb", lw=0.4))


def fig_swap():
    """Does the rule learn the answer, or only ever certify one of them?"""
    d = load("paperA_swap.json")
    rows = d["rows"]
    fig, axes = plt.subplots(1, 2, figsize=(6.6, 2.5))

    for ax, sym in zip(axes, (True, False)):
        sel = [r for r in rows if r["symmetric_certificate"] is sym
               and not r["reverse_tie_break"]]
        rules = ["proxy", "geometry", "uniform"]
        width = 0.35
        xs = np.arange(len(rules))
        for k, swapped in enumerate((False, True)):
            vals, cens, errs = [], [], []
            for rule in rules:
                m = [r for r in sel if r["rule"] == rule and r["swapped"] is swapped]
                vals.append(np.mean([r["restricted_mean_tau"] for r in m]) if m else 0)
                errs.append(np.mean([r["sem"] for r in m]) if m else 0)
                cens.append(sum(r["censored"] for r in m))
            bars = ax.bar(xs + (k - 0.5) * width, vals, width, yerr=errs, capsize=2,
                          label=("swapped world (answer B)" if swapped
                                 else "base world (answer A)"),
                          color=("#c0504d" if swapped else "#4f81bd"),
                          edgecolor="black", linewidth=0.4,
                          hatch=("///" if swapped and not sym else None))
            for b, c in zip(bars, cens):
                if c:
                    ax.text(b.get_x() + b.get_width() / 2, b.get_height(),
                            f"{c} censored", ha="center", va="bottom", fontsize=4.8,
                            color="#7b1f1f", rotation=90)
        ax.set_xticks(xs)
        ax.set_xticklabels(rules)
        ax.set_ylabel(r"restricted mean $\mathbb{E}[\min(\tau,B)]$")
        ax.set_title("certificate for each answer" if sym
                     else "certificate for A only", fontsize=7.5)
        ax.legend(fontsize=5.5, frameon=False)
        tag(ax, "MONTE CARLO\ncensoring shown, not absorbed")

    fig.suptitle("Reading the answer off the data, or naming it in advance", fontsize=8.5)
    fig.tight_layout(rect=(0, 0, 1, 0.94))
    fig.savefig(f"{OUT}/paperA_swap.pdf")
    plt.close(fig)
    return "paperA_swap.pdf"


def fig_decoder():
    """Decision and identification on the same channel, raw and rescaled."""
    d = load("paperB_decoder.json")
    res = d["results"]
    fig, axes = plt.subplots(1, 3, figsize=(7.2, 2.4))

    ms = sorted(set(r["m"] for r in res))
    m0 = ms[0]
    hs = sorted(set(r["h"] for r in res), reverse=True)
    cmap = plt.get_cmap("viridis")

    # (1) raw error against the total budget, safe decoder
    ax = axes[0]
    for i, h in enumerate(hs):
        sel = [r for r in res if r["decoder"] == "safe" and r["m"] == m0 and r["h"] == h]
        by = {}
        for r in sel:
            by.setdefault(r["total_budget"], []).append(r["err_upper95"])
        xs = sorted(by)
        ax.plot(xs, [max(by[x]) for x in xs], "o-", ms=2.5, lw=0.9,
                color=cmap(i / max(1, len(hs) - 1)), label=f"h={h}")
    ax.axhline(0.05, color="black", lw=0.6, ls="--")
    ax.text(ax.get_xlim()[1], 0.055, r"$\delta=0.05$", ha="right", fontsize=5.5)
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel("total budget"); ax.set_ylabel("worst-world error (95% upper)")
    ax.set_title(f"safe decoder, m={m0}", fontsize=7.5)
    ax.legend(fontsize=5, frameon=False)
    tag(ax, "MONTE CARLO\nClopper-Pearson upper bound")

    # (2) the same for identification
    ax = axes[1]
    for i, h in enumerate(hs):
        sel = [r for r in res if r["decoder"] == "identification"
               and r["m"] == m0 and r["h"] == h]
        by = {}
        for r in sel:
            by.setdefault(r["total_budget"], []).append(r["err_upper95"])
        xs = sorted(by)
        ax.plot(xs, [max(by[x]) for x in xs], "s-", ms=2.5, lw=0.9,
                color=cmap(i / max(1, len(hs) - 1)), label=f"h={h}")
    ax.axhline(0.05, color="black", lw=0.6, ls="--")
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel("total budget (sum over queries)")
    ax.set_title(f"identification decoder, m={m0}", fontsize=7.5)
    ax.legend(fontsize=5, frameon=False)
    tag(ax, "MONTE CARLO\nbudget is the SUM over tests")

    # (3) the gap's order, with the proved lower bound
    ax = axes[2]
    for row in d["order_rows"]:
        j = row["j"]
        ax.plot([0, 1], [row["slope_coarse_grid"], row["slope_fine_grid"]],
                "o-", ms=3, lw=1.0, label=f"j={j}")
        ax.axhline(j, color="#999", lw=0.5, ls=":")
    ax.set_xticks([0, 1]); ax.set_xticklabels(["coarse h", "fine h"])
    ax.set_ylabel("log-log slope of the mean gap")
    ax.set_title("the order converges to $j$", fontsize=7.5)
    ax.legend(fontsize=5, frameon=False)
    tag(ax, "EXACT\nslope of a closed form;\ndotted lines are the predicted orders")

    fig.suptitle("Deciding and identifying on one channel: two scales in the budget",
                 fontsize=8.5)
    fig.tight_layout(rect=(0, 0, 1, 0.92))
    fig.savefig(f"{OUT}/paperB_decoder.pdf")
    plt.close(fig)
    return "paperB_decoder.pdf"


def main():
    made = [fig_swap(), fig_decoder()]
    for f in made:
        print(f"  wrote {OUT}/{f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
