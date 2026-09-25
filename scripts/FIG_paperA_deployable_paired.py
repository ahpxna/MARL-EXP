#!/usr/bin/env python3
"""Paper A: the locked P-2 panel, from `paperA_deployable_paired.json` (no resampling of runs).

Three deployable rules under ONE two-answer certificate, 200 paired trajectories per cell
(common random numbers: run i of every rule in a cell uses the same seed), r in {1, 2, 4},
M in {1, 4}, base world (answer A) and swapped world (answer B), budget B = 60000.

Panels: (a) E[min(tau, B)] against r on the base world, every rule, M = 1 solid, M = 4 dashed;
(b) the same on the swapped world; (c) the certified fraction P(tau <= B) with exact
Clopper-Pearson 95% intervals.

Paired table (written to the record, not drawn): per cell, the mean paired difference of
min(tau, B) between the surrogate-at-estimate rule and each other rule, with a percentile
bootstrap 95% interval over the 200 pairs (10000 resamples, fixed seed; a numerical interval),
and the fraction of pairs in which the surrogate rule was slower.

SELF-CHECKS (refuse to draw on failure):
* the input records its producer and passed its own self-checks;
* stopped, censored, wrong and restricted-mean counts recomputed from the per-run records equal
  the stored ones;
* every censored run has tau = B and every stopped run tau <= B;
* PAIRING: within a cell the three rules carry the same seed for the same run index;
* every bootstrap interval contains its point estimate and every Clopper-Pearson interval
  lies in [0, 1] and contains the observed fraction;
* optional (`--launch2-log FILE`): every cell summary printed by launch 2 before it was killed
  is reproduced exactly by this artifact (seeds depend only on the cell and the run index).

Endpoint scope: min(tau, B) is a restricted mean; a censored run contributes B. The certificate
is a lower certificate and alpha = 0.05 lies far above delta_0 of the Omega(log^2) theorems, so
this is the behaviour of these rules, not a test of that theorem.

Outputs (new files; refuse to overwrite):
    research/papers/_figures/paperA_deployable_paired.pdf
    research/unified_20260919/paperA_deployable_paired_figure.json
"""

import hashlib
import json
import pathlib
import re
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D
from scipy.stats import beta

SRC = pathlib.Path("research/unified_20260919")
FIG = pathlib.Path("research/papers/_figures/paperA_deployable_paired.pdf")
REC = SRC / "paperA_deployable_paired_figure.json"
INPUT = "paperA_deployable_paired.json"

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
MSTY = {1.0: ("o", "-"), 4.0: ("s", "--")}
BOOT = 10000
BOOT_SEED = 20260925


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def clopper_pearson(k, n, level=0.95):
    a = (1 - level) / 2
    lo = 0.0 if k == 0 else float(beta.ppf(a, k, n - k + 1))
    hi = 1.0 if k == n else float(beta.ppf(1 - a, k + 1, n - k))
    return lo, hi


def main():
    global FIG, REC
    if "--out" in sys.argv:
        d = pathlib.Path(sys.argv[sys.argv.index("--out") + 1])
        d.mkdir(parents=True, exist_ok=True)
        FIG, REC = d / FIG.name, d / REC.name
    src = SRC / INPUT
    if "--in" in sys.argv:
        src = pathlib.Path(sys.argv[sys.argv.index("--in") + 1])
    log2 = None
    if "--launch2-log" in sys.argv:
        log2 = pathlib.Path(sys.argv[sys.argv.index("--launch2-log") + 1])
    for p in (FIG, REC):
        if p.exists():
            print(f"refusing to overwrite existing {p}", file=sys.stderr)
            return 2
    d = json.load(open(src))
    cfg = d["config"]
    rows = d["rows"]
    B = cfg["budget"]
    n_runs = cfg["n_runs"]
    rs, Ms, rules = cfg["r_values"], cfg["M_values"], cfg["rules"]
    check("the input records its producer and passed its own self-checks",
          d.get("producer") == "scripts/EXP_paperA_deployable_paired.py" and d["all_passed"],
          f"source_sha256 {d['source_sha256'][:12]}..., smoke={d['smoke']}")

    cell = {(x["r"], x["M"], x["swapped"], x["rule"]): x for x in rows}
    ok_store, ok_cens, ok_pair = True, True, True
    for x in rows:
        runs = x["runs"]
        cens = [q["censored"] for q in runs]
        stopped = [q for q in runs if not q["censored"]]
        ok_store &= len(runs) == n_runs
        ok_store &= x["stopped"] == len(stopped) and x["censored"] == sum(cens)
        ok_store &= x["stopped_wrong"] == sum(1 for q in stopped if q["answer"] != x["correct_answer"])
        ok_store &= abs(float(np.mean([q["tau"] for q in runs])) - x["restricted_mean_tau"]) < 1e-9
        ok_cens &= all((q["tau"] == B) if q["censored"] else (q["tau"] <= B) for q in runs)
    for r in rs:
        for M in Ms:
            for sw in cfg["worlds"]:
                seeds = [[q["seed"] for q in cell[(r, M, sw, rule)]["runs"]] for rule in rules]
                ok_pair &= all(s == seeds[0] for s in seeds)
    check("stopped, censored, wrong and restricted-mean counts recomputed from the runs equal the"
          " stored ones", ok_store,
          f"{sum(x['stopped_wrong'] for x in rows)} wrong of {sum(x['stopped'] for x in rows)} stopped")
    check("every censored run has tau = B and every stopped run tau <= B", ok_cens)
    check("PAIRING: within a cell the three rules carry the same seed for the same run", ok_pair)

    rng = np.random.default_rng(BOOT_SEED)
    table, ok_ci = [], True
    for r in rs:
        for M in Ms:
            for sw in cfg["worlds"]:
                s = np.array([q["tau"] for q in cell[(r, M, sw, "surrogate_at_estimate")]["runs"]],
                             dtype=float)
                for other in [x for x in rules if x != "surrogate_at_estimate"]:
                    o = np.array([q["tau"] for q in cell[(r, M, sw, other)]["runs"]], dtype=float)
                    diff = s - o
                    idx = rng.integers(0, len(diff), size=(BOOT, len(diff)))
                    boots = diff[idx].mean(axis=1)
                    lo, hi = np.percentile(boots, [2.5, 97.5])
                    est = float(diff.mean())
                    ok_ci &= lo - 1e-9 <= est <= hi + 1e-9
                    table.append({"r": r, "M": M, "swapped": sw, "against": other,
                                  "mean_paired_difference": est,
                                  "bootstrap95": [float(lo), float(hi)],
                                  "fraction_surrogate_slower": float(np.mean(diff > 0)),
                                  "fraction_tied": float(np.mean(diff == 0)),
                                  "restricted_mean_surrogate": float(s.mean()),
                                  "restricted_mean_other": float(o.mean())})
    cp, ok_cp = {}, True
    for key, x in cell.items():
        k = x["stopped"]
        lo, hi = clopper_pearson(k, n_runs)
        ok_cp &= 0.0 <= lo <= k / n_runs <= hi <= 1.0
        cp[key] = (k / n_runs, lo, hi)
    check("every bootstrap interval contains its point estimate", ok_ci,
          f"{BOOT} resamples, seed {BOOT_SEED}")
    check("every Clopper-Pearson interval lies in [0,1] and contains the observed fraction", ok_cp)

    repro = None
    if log2 is not None:
        pat = re.compile(r"r=(\d+) M=([\d.]+) swapped=(True|False)\s+(\S+)\s+E\[min\(tau,B\)\]=\s*(\d+)"
                         r" stopped=\s*(\d+) wrong=(\d+) censored=\s*(\d+)")
        seen, ok_rep = 0, True
        for line in log2.read_text().splitlines():
            m = pat.search(line)
            if not m:
                continue
            r, M, sw, rule = int(m.group(1)), float(m.group(2)), m.group(3) == "True", m.group(4)
            x = cell[(r, M, sw, rule)]
            same = (round(x["restricted_mean_tau"]) == int(m.group(5)) and x["stopped"] == int(m.group(6))
                    and x["stopped_wrong"] == int(m.group(7)) and x["censored"] == int(m.group(8)))
            ok_rep &= same
            seen += 1
        check("every cell summary printed by launch 2 is reproduced exactly", ok_rep and seen > 0,
              f"{seen} cells compared, log sha256 {sha(log2)[:12]}...")
        repro = {"launch2_log": str(log2), "launch2_log_sha256": sha(log2), "cells_compared": seen}

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print(f"\n{len(CHECKS) - nfail}/{len(CHECKS)} checks passed")
    if nfail:
        print("REFUSING to draw.", file=sys.stderr)
        return 1

    fig, ax = plt.subplots(1, 3, figsize=(6.9, 2.55))
    for k, sw in enumerate((False, True)):
        a = ax[k]
        for rule in rules:
            for M in Ms:
                mk, ls = MSTY[M]
                ys = [cell[(r, M, sw, rule)]["restricted_mean_tau"] for r in rs]
                a.plot(rs, ys, marker=mk, ls=ls, color=COLS[rule], ms=3)
        a.axhline(B, color="k", ls=":", lw=0.8)
        a.set_xscale("log", base=2)
        a.set_yscale("log")
        a.set_xticks(rs)
        a.set_xticklabels([str(r) for r in rs])
        a.set_ylim(5.0e2, 1.2e5)
        a.set_xlabel("$r$")
        a.set_title("base world, answer A" if not sw else "swapped world, answer B")
        if k == 0:
            a.set_ylabel(r"$E[\min(\tau,B)]$, " + f"{n_runs} paired runs")
            a.legend(handles=[Line2D([], [], color=COLS[x], label=LABS[x]) for x in rules],
                     frameon=False, loc="center left", bbox_to_anchor=(0.0, 0.62),
                     handlelength=1.2)
        else:
            a.legend(handles=[Line2D([], [], color="0.3", marker=MSTY[M][0], ls=MSTY[M][1],
                                     ms=3, label=f"$M={M:g}$") for M in Ms],
                     frameon=False, loc="center left", bbox_to_anchor=(0.0, 0.62))
        a.text(1.05, B * 1.12, "budget $B$", fontsize=5.0, color="0.3")
    a = ax[2]
    xs = []
    lab = []
    pos = 0
    for M in Ms:
        for sw in cfg["worlds"]:
            for r in rs:
                for j, rule in enumerate(rules):
                    f, lo, hi = cp[(r, M, sw, rule)]
                    x = pos + (j - 1) * 0.22
                    a.errorbar([x], [f], yerr=[[f - lo], [hi - f]], fmt=MSTY[M][0], ms=2.5,
                               color=COLS[rule], elinewidth=0.7, capsize=1.2)
                xs.append(pos)
                lab.append(f"{r}{'B' if sw else 'A'}")
                pos += 1
            pos += 0.5
    a.set_xticks(xs)
    a.set_xticklabels(lab, fontsize=4.6)
    a.set_ylim(-0.05, 1.05)
    a.set_xlabel(r"$r$ and world; $M=1$ left, $M=4$ right")
    a.set_ylabel(r"certified by $B$: $P(\tau\leq B)$")
    a.set_title("certified fraction, exact 95% CI")
    fig.tight_layout()
    fig.savefig(FIG)
    plt.close(fig)
    rec = {"producer": "scripts/FIG_paperA_deployable_paired.py", "producer_sha256": sha(__file__),
           "input": str(src), "input_sha256": sha(src), "input_source_sha256": d["source_sha256"],
           "input_locked_config_sha256": d["locked_config_sha256"],
           "resolved_or_resampled_anything": False,
           "bootstrap": {"resamples": BOOT, "seed": BOOT_SEED, "class": "numerical interval"},
           "figure": str(FIG), "scope": d["scope"], "paired_table": table,
           "certified_fraction": [{"r": k[0], "M": k[1], "swapped": k[2], "rule": k[3],
                                   "fraction": v[0], "clopper_pearson95": [v[1], v[2]]}
                                  for k, v in cp.items()],
           "reproduction": repro, "checks": CHECKS, "all_passed": True}
    with open(REC, "w") as f:
        json.dump(rec, f, indent=2)
    print(f"wrote {FIG}, {REC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
