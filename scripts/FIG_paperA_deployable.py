#!/usr/bin/env python3
"""Paper A: figure A-F2 on DEPLOYABLE policies, from `paperA_deployable.json` (no resampling).

Panels: (a) certificate rate P(tau <= b) by budget b, base world (answer A), every rule and r;
(b) the same on the swapped world (answer B); (c) E[min(tau, B)] against r on both worlds.

SELF-CHECKS (refuse to draw on failure):
* the input records its producer and passed its own self-checks;
* restricted means and censored counts recomputed from the per-run times equal the stored ones;
* every stopped run's answer is recorded, and wrong answers among stopped runs are at most the
  stored count (so no wrong answer is hidden by the drawing);
* P(tau <= b) is nondecreasing in b and reaches (n - censored)/n at b = B.

Outputs (new files; refuse to overwrite):
    research/papers/_figures/paperA_deployable.pdf
    research/unified_20260919/paperA_deployable_figure.json
"""

import hashlib
import json
import pathlib
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D

SRC = pathlib.Path("research/unified_20260919")
FIG = pathlib.Path("research/papers/_figures/paperA_deployable.pdf")
REC = SRC / "paperA_deployable_figure.json"
INPUT = "paperA_deployable.json"

plt.rcParams.update({
    "font.size": 8, "axes.labelsize": 8, "axes.titlesize": 8.5,
    "legend.fontsize": 5.4, "xtick.labelsize": 7, "ytick.labelsize": 7,
    "figure.dpi": 200, "savefig.dpi": 200, "axes.grid": True,
    "grid.alpha": 0.25, "grid.linewidth": 0.5, "lines.linewidth": 1.1,
})
CHECKS = []
COLS = {"surrogate_at_estimate": "#C44E52", "geometry": "#55A868", "uniform": "#4C72B0"}
LABS = {"surrogate_at_estimate": "surrogate at estimate", "geometry": "geometry lower-certificate heuristic",
        "uniform": "uniform"}
STYLES = {1: "-", 2: "--", 4: "-.", 8: ":"}


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def tag(ax, text, x=0.03, y=0.97, ha="left", va="top"):
    ax.text(x, y, text, transform=ax.transAxes, ha=ha, va=va, fontsize=5.0, color="0.3",
            bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="0.8", lw=0.4))


def main():
    global FIG, REC
    if "--out" in sys.argv:
        d = pathlib.Path(sys.argv[sys.argv.index("--out") + 1])
        d.mkdir(parents=True, exist_ok=True)
        FIG, REC = d / FIG.name, d / REC.name
    src = SRC / INPUT
    if "--in" in sys.argv:
        src = pathlib.Path(sys.argv[sys.argv.index("--in") + 1])
    for p in (FIG, REC):
        if p.exists():
            print(f"refusing to overwrite existing {p}", file=sys.stderr)
            return 2
    d = json.load(open(src))
    rows = d["rows"]
    rs = d["r_values"]
    B = d["budget"]
    check("the input records its producer and passed its own self-checks",
          d.get("producer") == "scripts/EXP_paperA_deployable.py" and d["all_passed"],
          f"source_sha256 {d['source_sha256'][:12]}...")
    ok_store, ok_wrong, ok_mono = True, True, True
    grid = np.unique(np.concatenate([np.geomspace(50, B, 200).round(), [B]])).astype(int)
    curves = {}
    for row in rows:
        taus = np.array(row["tau_per_run"])
        cens = np.array(row["censored_per_run"])
        ok_store &= abs(taus.mean() - row["restricted_mean_tau"]) < 1e-9
        ok_store &= int(cens.sum()) == row["censored"]
        wrong = sum(1 for a, c in zip(row["answer_per_run"], cens)
                    if (not c) and a != row["correct_answer"])
        ok_wrong &= wrong == row["stopped_wrong"]
        cr = [float(np.mean((taus <= b) & ~cens)) for b in grid]
        ok_mono &= all(y2 >= y1 - 1e-12 for y1, y2 in zip(cr, cr[1:]))
        ok_mono &= abs(cr[-1] - (len(taus) - cens.sum()) / len(taus)) < 1e-12
        curves[(row["r"], row["swapped"], row["rule"])] = cr
    check("restricted means and censored counts recomputed from the per-run records equal the"
          " stored ones", ok_store)
    check("wrong answers among stopped runs, recomputed, equal the stored counts", ok_wrong,
          f"{sum(r['stopped_wrong'] for r in rows)} wrong of {sum(r['stopped'] for r in rows)} stopped")
    check("P(tau <= b) is nondecreasing and reaches (n - censored)/n at b = B", ok_mono)
    nfail = sum(1 for c in CHECKS if not c["ok"])
    print(f"\n{len(CHECKS) - nfail}/{len(CHECKS)} checks passed")
    if nfail:
        print("REFUSING to draw.", file=sys.stderr)
        return 1

    fig, ax = plt.subplots(1, 3, figsize=(6.9, 2.55))
    for k, swapped in enumerate((False, True)):
        a = ax[k]
        for rule in COLS:
            for r in rs:
                a.plot(grid, curves[(r, swapped, rule)], STYLES[r], color=COLS[rule])
        a.set_xscale("log")
        a.set_ylim(-0.03, 1.03)
        a.set_xlabel("budget $b$")
        a.set_title("base world, answer A" if not swapped else "swapped world, answer B")
        if k == 0:
            a.set_ylabel(r"certified by $b$: $P(\tau\leq b)$")
            a.legend(handles=[Line2D([], [], color=COLS[x], label=LABS[x]) for x in COLS],
                     frameon=False, loc="center left", bbox_to_anchor=(0.0, 0.66),
                     handlelength=1.2)
        else:
            a.legend(handles=[Line2D([], [], color="0.3", ls=STYLES[r], label=f"$r={r}$")
                              for r in rs], frameon=False, loc="center left",
                     bbox_to_anchor=(0.0, 0.62), handlelength=1.6, title="line style",
                     title_fontsize=5.0)
    a = ax[2]
    for rule in COLS:
        for swapped, mk in ((False, "o-"), (True, "s--")):
            ys = [next(x["restricted_mean_tau"] for x in rows
                       if x["r"] == r and x["swapped"] == swapped and x["rule"] == rule) for r in rs]
            a.plot(rs, ys, mk, color=COLS[rule], ms=3)
    a.axhline(B, color="k", ls=":", lw=0.8)
    a.set_xscale("log", base=2); a.set_yscale("log")
    a.set_xticks(rs); a.set_xticklabels([str(r) for r in rs])
    a.set_xlabel("$r$"); a.set_ylabel(r"$E[\min(\tau,B)]$")
    a.set_title("cost, one two-answer certificate")
    a.set_ylim(1.0e3, 1.2e5)
    a.legend(handles=[Line2D([], [], color="0.3", marker="o", ls="-", ms=3, label="base (A)"),
                      Line2D([], [], color="0.3", marker="s", ls="--", ms=3, label="swapped (B)")],
             frameon=False, loc="lower right")
    a.text(1.05, B * 1.12, "budget $B$", fontsize=5.0, color="0.3")
    fig.tight_layout()
    fig.savefig(FIG)
    plt.close(fig)
    rec = {"producer": "scripts/FIG_paperA_deployable.py", "producer_sha256": sha(__file__),
           "input": str(src), "input_sha256": sha(src), "input_source_sha256": d["source_sha256"],
           "resolved_or_resampled_anything": False, "figure": str(FIG),
           "scope": d["scope"], "checks": CHECKS, "all_passed": True}
    with open(REC, "w") as f:
        json.dump(rec, f, indent=2)
    print(f"wrote {FIG}, {REC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
