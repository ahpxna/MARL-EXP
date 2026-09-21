#!/usr/bin/env python3
"""Figures for papers A, B and C.

Every panel is drawn from a JSON written by a self-checking script, and each is labelled
with its evidence class, because the three classes must not be confused:

    EXACT      -- rational arithmetic or a verified certificate
    NUMERICAL  -- a solved value or a measured slope, floating point
    ILLUSTRATION -- a formula plotted, carrying no new evidence
"""

import json
import math
import os
import sys

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
        return json.load(f)


def tag(ax, kind):
    ax.text(0.99, 0.02, kind, transform=ax.transAxes, ha="right", va="bottom",
            fontsize=5.5, color="0.35",
            bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="0.8", lw=0.4))


# ------------------------------------------------------------------ Paper A

def figA_proxy():
    d = load("paperA_frozen_proxy.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    f1, f2 = d["family1"], d["family2"]

    c1 = [r["c"] if "c" in r else r["M"] for r in f1]
    M1 = [r["M"] for r in f1]
    rat1 = [r["ratio"] for r in f1]
    ax[0].loglog(M1, rat1, "o-", ms=4, color="#4C72B0", label=r"$J_{\rm full}/J_{\rm frozen}$")
    ax[0].loglog(M1, [r["bound_16_over_M"] for r in f1], "k--", lw=0.8,
                 label=r"$16/M$")
    ax[0].axhline(1.0, color="0.6", lw=0.7)
    ax[0].set_xlabel("$M$"); ax[0].set_ylabel("ratio")
    ax[0].set_title("Family 1: the proxy prices too high")
    ax[0].legend(frameon=False)
    tag(ax[0], "NUMERICAL, KKT-certified")

    M2 = [r["M"] for r in f2]
    rat2 = [r["ratio"] for r in f2]
    ax[1].loglog(M2, rat2, "s-", ms=4, color="#C44E52",
                 label=r"$J_{\rm full}/J_{\rm frozen}$")
    ax[1].loglog(M2, [r["pred_lower"] for r in f2], "k--", lw=0.8,
                 label=r"$(M+3)/24$")
    ax[1].axhline(1.0, color="0.6", lw=0.7)
    ax[1].set_xlabel("$M$"); ax[1].set_ylabel("ratio")
    ax[1].set_title("Family 2: the proxy prices too low")
    ax[1].legend(frameon=False)
    tag(ax[1], "NUMERICAL, KKT-certified")
    fig.tight_layout()
    fig.savefig(f"{OUT}/paperA_frozen_proxy.pdf")
    plt.close(fig)
    return "paperA_frozen_proxy.pdf"


def figA_oracle_gap():
    d = load("oracle_gap.json")
    rows = d["rows"]
    fig, ax = plt.subplots(figsize=(3.4, 2.5))
    fin = [(r["c"], r["cost_ratio"]) for r in rows
           if not isinstance(r["cost_ratio"], str) and r["cost_ratio"] != float("inf")
           and r["cost_ratio"] < 1e12]
    ax.semilogy([p[0] for p in fin], [p[1] for p in fin], "o-", ms=3.5,
                color="#C44E52")
    dead = min((r["c"] for r in rows
                if isinstance(r["cost_ratio"], str) or r["cost_ratio"] == float("inf")),
               default=None)
    if dead is not None:
        ax.axvline(dead, color="k", ls="--", lw=0.8)
        ax.annotate("certificate\nunattainable", xy=(dead, max(p[1] for p in fin) * 0.2),
                    xytext=(dead - 0.6, max(p[1] for p in fin) * 0.02), fontsize=7,
                    arrowprops=dict(arrowstyle="->", lw=0.7))
    ax.set_xlabel(r"interaction $c$"); ax.set_ylabel("certificate / decision cost")
    ax.set_title("certifying is the expensive part")
    tag(ax, "NUMERICAL")
    fig.tight_layout()
    fig.savefig(f"{OUT}/paperA_oracle_gap.pdf")
    plt.close(fig)
    return "paperA_oracle_gap.pdf"


# ------------------------------------------------------------------ Paper B

def figB_orders():
    d = load("query_order.json")
    b = load("paperB_construction.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    for row in d["hellinger"]:
        ax[0].loglog(row["h"], row["H2"], "o-", ms=3,
                     label=fr"$n={row['n']},d={row['d']}$ ($s={row['s']}$)")
    ax[0].set_xlabel("$h$"); ax[0].set_ylabel(r"$H^2$")
    ax[0].set_title("Hellinger falls at the predicted order")
    ax[0].legend(frameon=False, fontsize=6)
    tag(ax[0], "NUMERICAL quadrature")

    rs = [r["r"] for r in b["moment_identity"]]
    got = [float(eval(r["E_chi_g_r"])) for r in b["moment_identity"]]
    pred = [math.factorial(r) / r ** r for r in rs]
    ax[1].semilogy(rs, got, "o", ms=6, label="computed, exact")
    ax[1].semilogy(rs, pred, "k+", ms=9, label=r"$r!/r^r$")
    ax[1].set_xlabel("$r$"); ax[1].set_ylabel(r"$E[\chi_r g^r]$")
    ax[1].set_title("the attained leading coefficient")
    ax[1].legend(frameon=False)
    tag(ax[1], "EXACT rational")
    fig.tight_layout()
    fig.savefig(f"{OUT}/paperB_orders.pdf")
    plt.close(fig)
    return "paperB_orders.pdf"


def figB_two_scales():
    d = load("paperB_obstruction_law.json")
    fig, ax = plt.subplots(figsize=(3.4, 2.5))
    hs = np.array([0.3, 0.2, 0.1, 0.05, 0.02])
    rs, ri = d["r_safe"], d["r_id"]
    ax.loglog(hs, hs ** (-2 * rs), "o-", ms=4,
              label=fr"decide  ($r_{{\rm safe}}={rs}$)")
    ax.loglog(hs, hs ** (-2 * ri), "s-", ms=4,
              label=fr"identify  ($r_{{\rm id}}={ri}$)")
    ax.invert_xaxis()
    ax.set_xlabel("$h$"); ax.set_ylabel("sample cost")
    ax.set_title(f"two scales on one family ($r={d['r']}$)")
    ax.legend(frameon=False)
    # The exponents come from exact moment identities and a Chebyshev budget, which give
    # the UPPER side only.  No lower bound over the adaptive query class is proved, so
    # calling these "the proved orders" would overstate the status of the lower half.
    tag(ax, "ILLUSTRATION: curves are $h^{-2r}$, upper side only")
    fig.tight_layout()
    fig.savefig(f"{OUT}/paperB_two_scales.pdf")
    plt.close(fig)
    return "paperB_two_scales.pdf"


# ------------------------------------------------------------------ Paper C

def figC_frontier():
    d = load("structural_frontier.json")
    cert = load("paperC_breakpoint_certs.json")
    fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.5))
    etas = d["etas"]
    for m in sorted(d["frontier"], key=int):
        free = float(eval(d["V_free"][m]))
        ax[0].plot(etas, [v / free if v is not None else np.nan
                          for v in d["frontier"][m]], "o-", ms=3, label=f"$m={m}$")
    ax[0].axhline(1.0, color="k", ls="--", lw=0.8)
    ax[0].set_xlabel(r"$\eta$")
    ax[0].set_ylabel(r"$V^{(\eta)}/V^{\rm free}$")
    ax[0].set_title("the relative price along the band")
    ax[0].legend(frameon=False, ncol=2, fontsize=6)
    tag(ax[0], "NUMERICAL LP")

    rows = cert["O2_window"]
    ms = [r["m"] for r in rows]
    edge = [float(eval(r["proved_up_to"])) for r in rows]
    ax[1].plot(ms, edge, "o-", ms=4, color="#55A868",
               label=r"Lean bound: $\eta<\frac{m^2-3}{m^2-1}$")
    ax[1].axhline(1.0, color="k", ls="--", lw=0.8, label=r"$\eta_*=1$ (odd $m$)")
    # The Farkas certificates close the whole interval per size, so the window the Lean
    # bound leaves open is no longer open -- at the sizes where a certificate exists.
    try:
        fk = load("paperC_exact_dual.json")["rows"]
        fm = [r["m"] for r in fk if r.get("root_matches_conjecture")]
        if fm:
            ax[1].plot(fm, [1.0] * len(fm), "*", ms=9, color="#4C72B0",
                       label="Farkas root $=\eta_*$: interval closed")
    except Exception:
        pass
    ax[1].fill_between(ms, edge, 1.0, color="#C44E52", alpha=0.12,
                       label="window the Lean bound leaves")
    ax[1].set_ylim(0.85, 1.02)
    ax[1].set_xlabel("$m$"); ax[1].set_ylabel(r"$\eta$")
    ax[1].set_title("Lean bound, and where a certificate closes it")
    ax[1].legend(frameon=False, fontsize=5.5, loc="lower right")
    tag(ax[1], "EXACT (theorem + rational certificate)")
    fig.tight_layout()
    fig.savefig(f"{OUT}/paperC_frontier.pdf")
    plt.close(fig)
    return "paperC_frontier.pdf"


def figC_flow():
    d = load("paperC_flow_lp.json")
    fig, ax = plt.subplots(figsize=(3.4, 2.5))
    rows = d["breakpoints"]
    ms = [r["m"] for r in rows]
    star = [r["eta_star"] for r in rows]
    pred = [r["predicted"] for r in rows]
    odd = [(m, s) for m, s in zip(ms, star) if m % 2]
    even = [(m, s) for m, s in zip(ms, star) if m % 2 == 0]
    ax.plot([p[0] for p in odd], [p[1] for p in odd], "o", ms=4,
            label=r"odd $m$ (solved)")
    ax.plot([p[0] for p in even], [p[1] for p in even], "s", ms=4,
            label=r"even $m$ (solved)")
    ax.plot(ms, pred, "k--", lw=0.8, label="conjecture")
    ax.set_ylim(0, 1.1)
    ax.set_xlabel("$m$"); ax.set_ylabel(r"$\eta_*$")
    ax.set_title("breakpoints, reached by the flow LP")
    ax.legend(frameon=False, fontsize=6)
    tag(ax, "NUMERICAL bisection")
    fig.tight_layout()
    fig.savefig(f"{OUT}/paperC_flow.pdf")
    plt.close(fig)
    return "paperC_flow.pdf"


def main():
    os.makedirs(OUT, exist_ok=True)
    made = []
    for fn in [figA_proxy, figA_oracle_gap, figB_orders, figB_two_scales,
               figC_frontier, figC_flow]:
        try:
            made.append(fn())
            print(f"  wrote {made[-1]}")
        except Exception as e:
            print(f"  FAILED {fn.__name__}: {e}", file=sys.stderr)
            return 1
    print(f"\n{len(made)} figures written")
    return 0


if __name__ == "__main__":
    sys.exit(main())
