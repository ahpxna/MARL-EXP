#!/usr/bin/env python3
"""Paper A: figures A-F1 (the centred separation, as an interval) and A-F2 (the mechanism).

NOTHING IS RE-SOLVED OR RE-SAMPLED.  Every number drawn is read from
`research/unified_20260919/paperA_mechanism.json` or is a closed formula transcribed from a
Lean theorem, and every stored number is checked against the proved formula beside it before
anything is drawn.

THE LEAN FORMULAS (the centred family `thetaC`, 4 + 2r cells, middle variance M):

    Gamma_proxy = 9/512                                  frozenGameC0_eq
    9/(128(4+2rM)) <= Gamma_true <= 1/(8rM)              trueGameC0_ge, trueGameC0_le
    the frozen optimum carries zero true information     frozen_optimum_trueValueC0_zero
    9b/(128(4+2rM)) <= J at (1-b) w_proxy + b w_cert <= b/(8rM)     frontier_two_sided

WHAT THE STORED NUMBERS ARE (read from `scripts/EXP_paperA_mechanism.py`):

* `J_true_lower_at_*` and `frontier[*].J_true` come from `value_at`: a LOWER certificate on the
  true value at a design.  The strict centred alternative set is relaxed to a union of
  polyhedra (the centring constraint is dropped, which ENLARGES the set) and each polyhedron
  is bounded below by the larger of its two exact half-space minima.  Both relaxations lower
  the infimum, so the certificate is conservative.  It is floating point.
* Hence an interval for Gamma_true/Gamma_proxy: the LOWER end is the best attained
  certificate, the UPPER end is the theorem.  No numerical upper bound is claimed.
* THE RUNS ARE AN ALLOCATION DIAGNOSTIC, NOT A LEARNER.  The stopping test is
  `value_at(...) > threshold and answer == "A"`, with the certificate built from the
  alternatives of answer A only, and the geometry rule optimises the same A-certificate.  The
  answer at the truth is therefore fixed in advance; a run cannot stop with B.  The three
  rules are compared under the SAME stopping certificate, which is what the diagnostic is for.
  That a rule which certifies only A never stops when the answer is B is shown by the swap
  panel (`paperA_swap.json`), not here.
* `restricted_mean_tau` is E[min(tau, B)] with B = 60000; a run censored at B has NOT been
  shown never to terminate.

Outputs (new files; refuses to overwrite):
    research/papers/_figures/paperA_mechanism.pdf
    research/unified_20260919/paperA_mechanism_figure.json
"""

import hashlib
import json
import pathlib
import sys
from fractions import Fraction as Fr

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SRC = pathlib.Path("research/unified_20260919")
FIG = pathlib.Path("research/papers/_figures/paperA_mechanism.pdf")
REC = SRC / "paperA_mechanism_figure.json"
INPUT = "paperA_mechanism.json"
LAUNCH_SHA = "66b6507ad061eb43e7de37040748a3ab0694258d5436679c1c80a62f7a2a390e"

plt.rcParams.update({
    "font.size": 8, "axes.labelsize": 8, "axes.titlesize": 8.5,
    "legend.fontsize": 6.2, "xtick.labelsize": 7, "ytick.labelsize": 7,
    "figure.dpi": 200, "savefig.dpi": 200, "axes.grid": True,
    "grid.alpha": 0.25, "grid.linewidth": 0.5, "lines.linewidth": 1.2,
})

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def tag(ax, text, x=0.99, y=0.02, ha="right"):
    ax.text(x, y, text, transform=ax.transAxes, ha=ha, va="bottom", fontsize=5.0,
            color="0.3", bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="0.8", lw=0.4))


def g_proxy():
    return Fr(9, 512)


def g_lower(r, M):
    return Fr(9) / (128 * (4 + 2 * r * M))


def g_upper(r, M):
    return Fr(1) / (8 * r * M)


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
    print("Paper A figure A-F1/A-F2: stored artifact checked against the Lean formulas")
    with open(SRC / INPUT) as f:
        d = json.load(f)
    M = Fr(d["M"]).limit_denominator(1000)
    rows = d["rows"]
    rs = [row["r"] for row in rows]

    check("the artifact is the launch record described by its provenance note",
          d["source_sha256"] == LAUNCH_SHA and d["all_passed"],
          f"source_sha256 {d['source_sha256'][:12]}..., stored self-checks all passed")

    ok_thm, worst = True, 0.0
    for row in rows:
        r = row["r"]
        for key, val in (("Gamma_frozen_theorem", g_proxy()),
                         ("Gamma_true_lower_theorem", g_lower(r, M)),
                         ("Gamma_true_upper_theorem", g_upper(r, M))):
            worst = max(worst, abs(row[key] - float(val)))
    ok_thm = worst < 1e-12
    check("the stored theorem values equal 9/512, 9/(128(4+2rM)) and 1/(8rM) at every r",
          ok_thm, f"r = {rs}, M = {M}, worst deviation {worst:.1e}")
    check("every attained lower certificate is at most the proved upper bound 1/(8rM) -- a"
          " certificate above it would refute trueGameC0_le",
          all(row["Gamma_true_attained_lower"] <= float(g_upper(row["r"], M)) + 1e-12
              for row in rows),
          "; ".join(f"r={row['r']}: {row['Gamma_true_attained_lower']:.5f} <="
                    f" {float(g_upper(row['r'], M)):.5f}" for row in rows))
    check("the frozen surrogate's optimum certifies exactly zero, as"
          " frozen_optimum_trueValueC0_zero requires of any valid lower certificate",
          all(row["J_true_lower_at_proxy_optimum"] == 0.0 for row in rows))
    check("along the sacrifice frontier every certificate is at most b/(8rM), the upper half"
          " of frontier_two_sided",
          all(fr["J_true"] <= fr["beta"] / (8 * row["r"] * float(M)) + 1e-12
              for row in rows for fr in row["frontier"]))
    ok_runs = True
    for row in rows:
        for name, run in row["runs"].items():
            taus = run["tau_per_run"]
            B = run["budget"]
            ok_runs &= abs(np.mean(taus) - run["restricted_mean_tau"]) < 1e-9
            ok_runs &= sum(1 for t in taus if t >= B) == run["censored"]
            ok_runs &= len(taus) == run["n"] and all(t <= B for t in taus)
            ok_runs &= run["correct"] + run["censored"] == run["n"]
    check("the restricted means are the means of the stored per-run times, the censored counts"
          " are the runs at the budget, and every uncensored run stopped with answer A (the"
          " only answer its certificate can return)", ok_runs)
    check("the answer at the truth is A: rangeA = 1 > rangeB = 1/4 on thetaC",
          all(row["answer_at_truth"] == "A" and row["rangeA"] == 1.0 and row["rangeB"] == 0.25
              for row in rows))

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print(f"\n{len(CHECKS) - nfail}/{len(CHECKS)} checks passed")
    if nfail:
        print("REFUSING to draw: a stored number disagrees with a proved formula.",
              file=sys.stderr)
        return 1

    fig, ax = plt.subplots(1, 3, figsize=(6.9, 2.5))
    a = ax[0]
    rg = np.arange(1, 9)
    lo_t = [float(g_lower(r, M) / g_proxy()) for r in rg]
    hi_t = [float(g_upper(r, M) / g_proxy()) for r in rg]
    a.fill_between(rg, lo_t, hi_t, color="#4C72B0", alpha=0.12, label="proved bracket")
    a.plot(rg, lo_t, "-", color="#4C72B0", lw=0.9)
    a.plot(rg, hi_t, "-", color="#4C72B0", lw=0.9)
    lo_c = [row["Gamma_true_attained_lower"] / float(g_proxy()) for row in rows]
    hi_c = [float(g_upper(row["r"], M) / g_proxy()) for row in rows]
    a.errorbar(rs, [(l + h) / 2 for l, h in zip(lo_c, hi_c)],
               yerr=[[(h - l) / 2 for l, h in zip(lo_c, hi_c)]] * 2, fmt="none",
               ecolor="k", elinewidth=1.3, capsize=3, label="certified interval")
    a.plot(rs, lo_c, "v", color="k", ms=4)
    a.axhline(1.0, color="#C44E52", ls="--", lw=0.8, label=r"$\Gamma_{\rm true}=\Gamma_{\rm proxy}$")
    a.set_yscale("log"); a.set_xscale("log", base=2)
    a.set_xticks(rs); a.set_xticklabels([str(r) for r in rs])
    a.set_xlabel("$r$ (pairs of middle cells), $M=1$")
    a.set_ylabel(r"$\Gamma_{\rm true}/\Gamma_{\rm proxy}$")
    a.set_title("A-F1: the centred separation")
    a.legend(frameon=False, loc="upper right")
    tag(a, "band: THEOREM; interval: attained LOWER\ncertificate (float) to theorem upper")

    cols = {"geometry": "#55A868", "uniform": "#4C72B0", "proxy": "#C44E52"}
    labs = {"geometry": "geometry certificate", "uniform": "uniform",
            "proxy": "frozen proxy + forced exploration"}
    a = ax[1]
    for name in ("geometry", "uniform", "proxy"):
        a.plot(rs, [row["runs"][name]["mean_middle_share"] for row in rows], "o-",
               color=cols[name], ms=3.5, label=labs[name])
    a.set_xscale("log", base=2); a.set_yscale("log")
    a.set_xticks(rs); a.set_xticklabels([str(r) for r in rs])
    a.set_xlabel("$r$"); a.set_ylabel("share of queries on middle cells")
    a.set_ylim(1e-3, 20)
    a.set_title("where the queries go")
    a.legend(frameon=False, loc="center right", bbox_to_anchor=(1.0, 0.47), fontsize=5.6)
    tag(a, "NUMERICAL, 24 runs per rule and r", x=0.02, y=0.90, ha="left")

    a = ax[2]
    B = rows[0]["runs"]["proxy"]["budget"]
    for name in ("geometry", "uniform", "proxy"):
        ys = [row["runs"][name]["restricted_mean_tau"] for row in rows]
        es = [row["runs"][name]["sem"] for row in rows]
        cens = [row["runs"][name]["censored"] for row in rows]
        a.errorbar(rs, ys, yerr=es, fmt="o-", color=cols[name], ms=3.5, capsize=2,
                   label=labs[name])
        if any(cens):
            a.text(2.83, 1.2e5, f"proxy: {min(cens)}/24 censored at $B$, every $r$",
                   ha="center", fontsize=5.2, color=cols[name])
    a.axhline(B, color="k", ls=":", lw=0.8)
    a.set_xscale("log", base=2); a.set_yscale("log")
    a.set_ylim(3e2, 3e5)
    a.set_xticks(rs); a.set_xticklabels([str(r) for r in rs])
    a.set_xlabel("$r$"); a.set_ylabel(r"$E[\min(\tau,B)]$, $B=6\times10^4$")
    a.set_title("cost, one certificate")
    tag(a, "stop = A-certificate only: an allocation\n"
           "diagnostic, not a learner; censored at B is\nnot shown never to stop")
    fig.tight_layout()
    fig.savefig(FIG)
    plt.close(fig)

    rec = {"producer": "scripts/FIG_paperA_mechanism.py", "producer_sha256": sha(__file__),
           "input": INPUT, "input_sha256": sha(SRC / INPUT),
           "input_launch_source_sha256": d["source_sha256"],
           "input_current_producer_sha256": sha("scripts/EXP_paperA_mechanism.py"),
           "resolved_or_resampled_anything": False, "figure": str(FIG),
           "scope": "allocation diagnostic under one fixed A-certificate; not a delta-correct"
                    " learner; interval lower ends are float lower certificates",
           "checks": CHECKS, "all_passed": True}
    with open(REC, "w") as f:
        json.dump(rec, f, indent=2)
    print(f"wrote {FIG}, {REC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
