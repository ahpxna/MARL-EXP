#!/usr/bin/env python3
"""Paper A: figure A-F2 on the axis the spec asks for -- certificate rate and restricted mean
by BUDGET -- and the middle-cell share as a trajectory.

NOTHING IS RE-SOLVED OR RE-SAMPLED.  Every number drawn is read from
`research/unified_20260919/paperA_mechanism.json` (launch source sha256 66b6507a..., commit
51a3364): `tau_per_run` gives P(tau <= b) and E[min(tau, b)] at every budget b <= B = 60000
exactly (a run censored at B has min(tau, b) = b for every b <= B), and `traces` gives
N_mid(t)/t every 1500 rounds for the FIRST replicate of each rule only.

WHAT THE RULES ARE (read from the launch source, `git show 51a3364:scripts/EXP_paperA_mechanism.py`):

* `proxy` -- the design `w_proxy` = 1/4 on each of the four anchor cells, which is the Lean
  `wUnifC r`, an exact optimum of the frozen surrogate game (`surrogate_optimum_exists`),
  mixed toward uniform with weight min(1, 1/sqrt(t)) (t = samples so far), tracked by the
  first argmax of W - N after a warm start of one query per cell.  That is the Lean
  `fixLearner (wUnifC r)` of `LeanPaperA6FixedDesignV1` up to the forcing offset (Lean uses
  1/sqrt(s+1)).  ORACLE ALLOCATION: the design is the surrogate optimum at the true world.
* `uniform` -- the uniform design, no forcing.  `geometry` -- a Nelder-Mead ascent of the
  A-certificate at the estimate.
* THE STOP IS NOT THE LEAN STOP.  Every rule stops when a relaxed LOWER certificate for the
  alternatives of answer A exceeds the threshold, checked every 50 rounds.  So these runs are
  an ALLOCATION DIAGNOSTIC under one shared certificate, not delta-correct learners, and the
  proxy runs are not a test of `uniform_surrogate_cost`: that theorem uses the GLR stop
  `tauG` and holds for delta < delta_0 = min(1/32, exp(-4(2K+1)/(KM))), about 1.7e-4 at r = 1,
  M = 1, while the panel is at alpha = 0.05.

SELF-CHECKS (the script refuses to draw if any fails):

* the input is the launch record; restricted means, censored counts and the certified
  fraction at b = B recomputed from `tau_per_run` equal the stored ones;
* P(tau <= b) and E[min(tau, b)] are monotone in b, E[min(tau, b)] <= b, and its increments
  are at most the budget increments (a property of min(tau, b), which a bookkeeping error
  would break);
* each stored trace belongs to replicate 0: its last time is <= tau_per_run[0] and within one
  trace period of it (unless censored);
* THE THEOREM CHECK: along the proxy trace the middle count N_mid(t) = t * share stays below
  2r * (2 + q(t)), where q(t) = sum_{n <= s < t} s^{-1/2} / n is the forcing quota of one
  middle cell under the code's forcing, the pathwise bound of `fCount_le_quota` /
  `fCount_le_sqrt` (N_e <= 2 + quota on a cell the design ignores) transcribed for 1/sqrt(t).
  A leak of the tracked design onto the middles would break it.

Outputs (new files; refuses to overwrite):
    research/papers/_figures/paperA_budget.pdf
    research/unified_20260919/paperA_budget_figure.json
"""

import hashlib
import json
import math
import pathlib
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SRC = pathlib.Path("research/unified_20260919")
FIG = pathlib.Path("research/papers/_figures/paperA_budget.pdf")
REC = SRC / "paperA_budget_figure.json"
INPUT = "paperA_mechanism.json"
LAUNCH_SHA = "66b6507ad061eb43e7de37040748a3ab0694258d5436679c1c80a62f7a2a390e"

plt.rcParams.update({
    "font.size": 8, "axes.labelsize": 8, "axes.titlesize": 8.5,
    "legend.fontsize": 6.0, "xtick.labelsize": 7, "ytick.labelsize": 7,
    "figure.dpi": 200, "savefig.dpi": 200, "axes.grid": True,
    "grid.alpha": 0.25, "grid.linewidth": 0.5, "lines.linewidth": 1.1,
})

CHECKS = []
COLS = {"geometry": "#55A868", "uniform": "#4C72B0", "proxy": "#C44E52"}
LABS = {"geometry": "geometry certificate", "uniform": "uniform",
        "proxy": "surrogate optimum + forcing"}
STYLES = {1: "-", 2: "--", 4: "-.", 8: ":"}


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def tag(ax, text, x=0.99, y=0.02, ha="right", va="bottom"):
    ax.text(x, y, text, transform=ax.transAxes, ha=ha, va=va, fontsize=5.0,
            color="0.3", bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="0.8", lw=0.4))


def cert_rate(taus, b, B):
    """P(tau <= b) for b < B; at b = B a run is certified iff it was not censored."""
    taus = np.asarray(taus)
    if b < B:
        return float(np.mean(taus <= b))
    return float(np.mean(taus < B))


def rmst(taus, b):
    return float(np.mean(np.minimum(np.asarray(taus), b)))


def forcing_quota(t, n):
    """Forcing mass on ONE cell through `t` samples: sum_{n <= s < t} s^{-1/2} / n."""
    if t <= n:
        return 0.0
    s = np.arange(n, t, dtype=float)
    return float(np.sum(1.0 / np.sqrt(s)) / n)


def main():
    global FIG, REC
    if "--out" in sys.argv:
        d = pathlib.Path(sys.argv[sys.argv.index("--out") + 1])
        d.mkdir(parents=True, exist_ok=True)
        FIG, REC = d / FIG.name, d / REC.name
    for p in (FIG, REC):
        if p.exists():
            print(f"refusing to overwrite existing {p}", file=sys.stderr)
            return 2
    print("Paper A figure A-F2 by budget: stored runs, no resampling")
    with open(SRC / INPUT) as f:
        d = json.load(f)
    rows = d["rows"]
    rs = [row["r"] for row in rows]
    B = d["budget"]

    check("the artifact is the launch record described by its provenance note",
          d["source_sha256"] == LAUNCH_SHA and d["all_passed"],
          f"source_sha256 {d['source_sha256'][:12]}...")

    grid = np.unique(np.concatenate([np.geomspace(50, B, 200).round(), [B]])).astype(int)
    ok_store, ok_mono, worst = True, True, 0.0
    curves = {}
    for row in rows:
        for name, run in row["runs"].items():
            taus = run["tau_per_run"]
            ok_store &= len(taus) == run["n"] and all(t <= B for t in taus)
            worst = max(worst, abs(rmst(taus, B) - run["restricted_mean_tau"]))
            ok_store &= sum(1 for t in taus if t >= B) == run["censored"]
            ok_store &= abs(cert_rate(taus, B, B) - (run["n"] - run["censored"]) / run["n"]) < 1e-12
            cr = [cert_rate(taus, int(b), B) for b in grid]
            rm = [rmst(taus, int(b)) for b in grid]
            ok_mono &= all(y2 >= y1 - 1e-12 for y1, y2 in zip(cr, cr[1:]))
            ok_mono &= all(y2 >= y1 - 1e-9 for y1, y2 in zip(rm, rm[1:]))
            ok_mono &= all(y <= b + 1e-9 for y, b in zip(rm, grid))
            ok_mono &= all(y2 - y1 <= b2 - b1 + 1e-9
                           for y1, y2, b1, b2 in zip(rm, rm[1:], grid, grid[1:]))
            curves[(row["r"], name)] = (cr, rm)
    check("restricted means, censored counts and the certified fraction at b = B recomputed"
          " from tau_per_run equal the stored ones", ok_store and worst < 1e-9,
          f"worst restricted-mean deviation {worst:.1e}")
    check("P(tau <= b) and E[min(tau,b)] are nondecreasing in b, E[min(tau,b)] <= b, and"
          " E[min(tau,b)] grows by at most the budget increment", ok_mono)

    ok_tr, det = True, []
    for row in rows:
        for name, tr in row["traces"].items():
            run = row["runs"][name]
            t0 = run["tau_per_run"][0]
            ts = [p["t"] for p in tr]
            period = max(1, B // 40)
            ok_tr &= all(0.0 <= p["middle_share"] <= 1.0 for p in tr)
            ok_tr &= all(b > a for a, b in zip(ts, ts[1:]))
            ok_tr &= ts[-1] <= t0 and (t0 >= B or t0 - ts[-1] < period)
            det.append(f"r={row['r']} {name}: last {ts[-1]} vs tau_0 {t0}")
    check("each stored trace belongs to replicate 0 (ends at or before its tau, within one"
          " trace period of it unless censored)", ok_tr, "; ".join(det[:3]) + "; ...")

    ok_thm, slack = True, []
    for row in rows:
        r = row["r"]
        n = 4 + 2 * r
        tight = math.inf
        for p in row["traces"]["proxy"]:
            t = p["t"]
            nmid = p["middle_share"] * t
            bound = 2 * r * (2.0 + forcing_quota(t, n))
            ok_thm &= nmid <= bound + 1e-6
            ok_thm &= bound <= 2 * r * (2.0 + 2.0 * math.sqrt(t) / n) + 1e-9
            tight = min(tight, bound - nmid)
        slack.append(f"r={r}: min slack {tight:.1f} queries")
    check("THEOREM (fCount_le_quota / fCount_le_sqrt, transcribed for the code's forcing): along"
          " the proxy trace N_mid(t) <= 2r(2 + q(t)) <= 2r(2 + 2 sqrt(t)/n) -- forcing is the"
          " only source of middle queries", ok_thm, "; ".join(slack))

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print(f"\n{len(CHECKS) - nfail}/{len(CHECKS)} checks passed")
    if nfail:
        print("REFUSING to draw: a stored number disagrees with its definition or a proved bound.",
              file=sys.stderr)
        return 1

    from matplotlib.lines import Line2D
    short = {"geometry": "geometry", "uniform": "uniform", "proxy": "surrogate opt."}
    fig, ax = plt.subplots(1, 3, figsize=(6.9, 2.55))
    a = ax[0]
    for name in ("geometry", "uniform"):
        for r in rs:
            a.plot(grid, curves[(r, name)][0], STYLES[r], color=COLS[name])
    a.plot(grid, curves[(rs[0], "proxy")][0], "-", color=COLS["proxy"], lw=1.6)
    a.text(58, 0.07, "0/24 certified,\nevery $b$ and $r$", fontsize=5.0, color=COLS["proxy"])
    a.legend(handles=[Line2D([], [], color=COLS[nm], label=short[nm])
                      for nm in ("geometry", "uniform", "proxy")],
             frameon=False, loc="center left", bbox_to_anchor=(0.0, 0.72), fontsize=5.0,
             handlelength=1.2)
    a.set_xscale("log")
    a.set_ylim(-0.03, 1.03)
    a.set_xlabel("budget $b$")
    a.set_ylabel(r"certificate rate $P(\tau\leq b)$")
    a.set_title("A-F2: certified by budget $b$")

    a = ax[1]
    for name in ("geometry", "uniform", "proxy"):
        for r in rs:
            a.plot(grid, curves[(r, name)][1], STYLES[r], color=COLS[name])
    a.plot(grid, grid, color="0.5", lw=0.6)
    a.set_xscale("log"); a.set_yscale("log")
    a.set_xlabel("budget $b$")
    a.set_ylabel(r"$E[\min(\tau,b)]$")
    a.set_title("restricted mean by budget")
    a.legend(handles=[Line2D([], [], color="0.3", ls=STYLES[r], label=f"$r={r}$") for r in rs],
             frameon=False, loc="lower right", fontsize=5.0, title="line style",
             title_fontsize=5.0)
    tag(a, "stop = A-certificate only:\nallocation diagnostic, $\\alpha=0.05$;\n"
           "surrogate optimum on $E=b$", x=0.03, y=0.97, ha="left", va="top")

    a = ax[2]
    for name in ("geometry", "uniform", "proxy"):
        for r in (rs[0], rs[-1]):
            tr = rows[rs.index(r)]["traces"][name]
            a.plot([p["t"] for p in tr], [p["middle_share"] for p in tr], STYLES[r] + "o",
                   color=COLS[name], ms=1.8)
    for r in (rs[0], rs[-1]):
        n = 4 + 2 * r
        tt = np.geomspace(1500, B, 60)
        a.plot(tt, [2 * r * (2.0 + forcing_quota(int(t), n)) / t for t in tt], STYLES[r],
               color="k", lw=0.7)
    a.set_xscale("log"); a.set_yscale("log")
    a.set_ylim(1.5e-3, 3.0)
    a.set_xlabel("$t$")
    a.set_ylabel(r"$N_{\rm mid}(t)/t$")
    a.set_title("middle share (one run)")
    a.text(0.30, 0.62, "black: proved forcing bound\nsolid $r=1$, dotted $r=8$",
           transform=a.transAxes, fontsize=5.0, color="0.25", va="center")
    fig.tight_layout()
    fig.savefig(FIG)
    plt.close(fig)

    rec = {"producer": "scripts/FIG_paperA_budget.py", "producer_sha256": sha(__file__),
           "input": INPUT, "input_sha256": sha(SRC / INPUT),
           "input_launch_source_sha256": d["source_sha256"],
           "resolved_or_resampled_anything": False, "figure": str(FIG),
           "scope": "allocation diagnostic under one fixed A-certificate, alpha = 0.05; the proxy"
                    " rule is fixLearner (wUnifC r) up to the forcing offset, with a different"
                    " stop; outside the delta range of uniform_surrogate_cost; traces are"
                    " replicate 0 only",
           "checks": CHECKS, "all_passed": True}
    with open(REC, "w") as f:
        json.dump(rec, f, indent=2)
    print(f"wrote {FIG}, {REC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
