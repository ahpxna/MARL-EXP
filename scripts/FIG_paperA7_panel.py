#!/usr/bin/env python3
"""Paper A, figure A-F3: the shipped learner on the finite panel, from `paperA7_panel.json`
(no resampling).

Panels: (a) E[min(tau, B)] per cell and arm, censored runs counted; (b) information
accumulation -- the offline certified lower value of the true game at the empirical design
`N/tau`, divided by the true game's value (1 means the run spent its samples as well as the
optimal design); (c) selection -- for the learner, the share of refreshes whose kept set is a
single answer, and the share that selected the true answer.

SELF-CHECKS (refuse to draw on failure): the input passed its own checks; restricted means
recomputed from the runs equal the stored ones; THEOREM: no empirical design exceeds the game
value, `J_true(N/tau) <= Gamma_upper` (Gamma is the supremum over designs), up to 1e-6
relative; every stopped learner run recorded at least one selection snapshot.

Outputs (new files; refuse to overwrite):
    research/papers/_figures/paperA7_panel.pdf
    research/unified_20260919/paperA7_panel_figure.json
"""

import hashlib
import json
import pathlib
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SRC = pathlib.Path("research/unified_20260919")
FIG = pathlib.Path("research/papers/_figures/paperA7_panel.pdf")
REC = SRC / "paperA7_panel_figure.json"
INPUT = "paperA7_panel.json"
plt.rcParams.update({"font.size": 8, "axes.labelsize": 8, "axes.titlesize": 8.5,
                     "legend.fontsize": 5.6, "xtick.labelsize": 6.2, "ytick.labelsize": 7,
                     "figure.dpi": 200, "savefig.dpi": 200, "axes.grid": True,
                     "grid.alpha": 0.25, "grid.linewidth": 0.5})
COLS = {"learner": "#55A868", "oracle": "#8172B2", "uniform": "#4C72B0"}
LABS = {"learner": "learner (oracle at estimate)", "oracle": "oracle design (diagnostic)",
        "uniform": "uniform"}
SHORT = {"base_M16_gap4": "base\nM=16", "swapped_M16_gap4": "swapped\nM=16",
         "base_M16_gap2": "small gap\nM=16", "base_M64_gap4": "base\nM=64"}
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


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
    cells = d["cells"]
    check("the input passed its own self-checks and names its producer",
          d["all_passed"] and d["producer"] == "scripts/EXP_paperA7_panel.py")
    ok_mean, ok_thm, ok_sel, worst = True, True, True, 0.0
    for c in cells:
        for arm, a in c["arms"].items():
            taus = [x["tau"] for x in a["runs"]]
            ok_mean &= abs(np.mean(taus) - a["restricted_mean_tau"]) < 1e-9
            for x in a["runs"]:
                ratio = x["offline_J_true_lower_at_empirical_design"] / c["Gamma_upper_at_truth"]
                worst = max(worst, ratio)
                ok_thm &= ratio <= 1.0 + 1e-6
                if arm == "learner" and not x["censored"]:
                    ok_sel &= len(x["selection_trace"]) > 0 or x["tau"] <= d["config"]["oracle_every"]
    check("restricted means recomputed from the runs equal the stored ones", ok_mean)
    check("THEOREM: no empirical design exceeds the game value, J_true(N/tau) <= Gamma_upper",
          ok_thm, f"largest ratio {worst:.4f}")
    check("every stopped learner run past the first refresh recorded a selection snapshot", ok_sel)
    if not all(x["ok"] for x in CHECKS):
        print("REFUSING to draw.", file=sys.stderr)
        return 1

    names = [c["name"] for c in cells]
    xs = np.arange(len(cells))
    fig, ax = plt.subplots(1, 3, figsize=(6.9, 2.6))
    a = ax[0]
    for k, arm in enumerate(COLS):
        ys = [c["arms"][arm]["restricted_mean_tau"] for c in cells]
        a.plot(xs + (k - 1) * 0.18, ys, "o", color=COLS[arm], ms=3.5, label=LABS[arm])
        for x0, c in zip(xs, cells):
            ce = c["arms"][arm]["censored"]
            if ce:
                a.text(x0 + (k - 1) * 0.18, c["arms"][arm]["restricted_mean_tau"] * 1.25,
                       f"{ce}c", fontsize=4.6, color=COLS[arm], ha="center")
    a.set_yscale("log")
    a.set_xticks(xs); a.set_xticklabels([SHORT.get(n, n) for n in names])
    a.set_ylabel(r"$E[\min(\tau,B)]$")
    a.set_title("cost per cell")
    a.legend(frameon=False, loc="upper left", fontsize=5.0)
    a = ax[1]
    for k, arm in enumerate(COLS):
        for x0, c in zip(xs, cells):
            vals = [x["offline_J_true_lower_at_empirical_design"] / c["Gamma_upper_at_truth"]
                    for x in c["arms"][arm]["runs"]]
            jit = (np.arange(len(vals)) % 7 - 3) * 0.012
            a.plot(np.full(len(vals), x0 + (k - 1) * 0.18) + jit, vals, ".", color=COLS[arm],
                   ms=1.6, alpha=0.6)
            a.plot([x0 + (k - 1) * 0.18 - 0.07, x0 + (k - 1) * 0.18 + 0.07],
                   [np.median(vals)] * 2, color=COLS[arm], lw=1.4)
    a.axhline(1.0, color="k", ls=":", lw=0.8)
    a.set_ylim(0, 1.08)
    a.set_xticks(xs); a.set_xticklabels([SHORT.get(n, n) for n in names])
    a.set_ylabel(r"$J_{\rm true}(N/\tau)\,/\,\Gamma$ at the stop")
    a.set_title("information accumulation (offline)")
    a = ax[2]
    single, correct = [], []
    for c in cells:
        snaps = [s for x in c["arms"]["learner"]["runs"] for s in x["selection_trace"]]
        single.append(np.mean([len(s["kept"]) == 1 for s in snaps]) if snaps else np.nan)
        correct.append(np.mean([s["selected"] == c["truth"] for s in snaps]) if snaps else np.nan)
    a.bar(xs - 0.17, single, width=0.32, color="#DD8452", label="kept set is one answer")
    a.bar(xs + 0.17, correct, width=0.32, color="#55A868", label="selected answer is the truth")
    a.set_ylim(0, 1.08)
    a.set_xticks(xs); a.set_xticklabels([SHORT.get(n, n) for n in names])
    a.set_ylabel("share of refreshes (learner)")
    a.set_title("selection")
    a.legend(frameon=False, loc="lower right", fontsize=5.0)
    fig.tight_layout()
    fig.savefig(FIG)
    plt.close(fig)
    rec = {"producer": "scripts/FIG_paperA7_panel.py", "producer_sha256": sha(__file__),
           "input": str(src), "input_sha256": sha(src), "input_source_sha256": d["source_sha256"],
           "resolved_or_resampled_anything": False, "figure": str(FIG),
           "selection_single_share": dict(zip(names, map(float, single))),
           "selection_correct_share": dict(zip(names, map(float, correct))),
           "scope": d["scope"], "checks": CHECKS, "all_passed": True}
    with open(REC, "w") as f:
        json.dump(rec, f, indent=2)
    print(f"wrote {FIG}, {REC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
