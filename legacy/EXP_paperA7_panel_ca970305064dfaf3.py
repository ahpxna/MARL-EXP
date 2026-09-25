#!/usr/bin/env python3
"""Paper A, figure A-F3: the shipped learner on a finite panel -- swapped truths, two gap
regimes, and an active-region transition.

The learner is `run` of `scripts/EXP_paperA7_learner.py`, imported UNCHANGED.  It receives a
sampler closure, never the world: the truth is read only by `make_sampler` and by the OFFLINE
diagnostics below, which never feed back into a run.

THE PANEL (frozen after the smoke run; the configuration is hashed into the artifact):

    cell               truth   M    scale   budget
    base_M16_gap4      A       16   4       20000     the learner's own world
    swapped_M16_gap4   B       16   4       20000     the arms exchanged: truth second in tie-break
    base_M16_gap2      A       16   2       80000     the small-gap regime (gaps halved)
    base_M64_gap4      A       64   4       20000     the other side of the active-region switch

`M` is the variance of arm B's two cheap cells.  At a FIXED design (the uniform one) the
region of the union realising the minimum energy is `(1, 0)` for every `M <= 16` and switches
to `(2, 0)`/`(3, 0)` at `M = 64` (development sweep, 2026-09-24).  At the OPTIMAL design all
three regions tie -- a maximin design equalises them -- so "the active region at the optimum"
is not well defined and only its tie set is recorded.  The uniform-design region is computed
offline and checked to differ between the two `M` cells.

ARMS: `learner` (the shipped oracle at the estimate); `oracle` (the design computed from the
TRUE world -- an ORACLE-ALLOCATION DIAGNOSTIC, labelled as such); `uniform`.  One alpha,
0.05.  50 replicates per cell and arm, seeds `[20260925, cell, arm, run]`.

RECORDED per run: tau, answer, censored, counts, the stop certificate (statistic `Zlo`, the
threshold, the margin), the selection trace (selected answer and ALL kept answers at every
refresh), the oracle bracket gaps, and -- offline -- a certified lower value of the true game
at the empirical design `N/t`.

SELF-CHECKS (refuse to report on failure): `run` takes no world argument; every run is
accounted for once as stopped or censored; every stop has a positive certificate margin; the
wrong-answer rate among stopped runs is consistent with alpha (binomial tail); the truths are
A on base cells and B on the swapped cell; the uniform-design active region differs between
`M = 16` and `M = 64`.  No ordering learner < oracle < uniform is required.

Output (new file; refuses to overwrite): research/unified_20260919/paperA7_panel.json.
Smoke: `--smoke --out DIR`.
"""

import hashlib
import inspect
import json
import math
import pathlib
import sys
import time

import numpy as np

sys.path.insert(0, "scripts")
import EXP_paperA7_learner as L7  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "research/unified_20260919/paperA7_panel.json"
CHECKS = []

CELLS = [
    {"name": "base_M16_gap4", "swapped": False, "M": 16.0, "scale": 4.0, "budget": 20000},
    {"name": "swapped_M16_gap4", "swapped": True, "M": 16.0, "scale": 4.0, "budget": 20000},
    {"name": "base_M16_gap2", "swapped": False, "M": 16.0, "scale": 2.0, "budget": 80000},
    {"name": "base_M64_gap4", "swapped": False, "M": 64.0, "scale": 4.0, "budget": 20000},
]
ARMS = ["learner", "oracle", "uniform"]
ALPHA = 0.05
N_RUNS = 50
ORACLE_EVERY, CHECK_EVERY = 200, 50


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""), flush=True)
    return ok


def world(cell):
    theta, var = L7.family_low(cell["M"])
    theta = L7.center_world(cell["scale"] * theta)
    if cell["swapped"]:
        theta = np.concatenate([theta[4:8], theta[0:4]])
        var = np.concatenate([var[4:8], var[0:4]])
    return theta, var


def region_values(theta, var, T, w):
    """Offline: every region's minimum energy at design `w`, sorted."""
    H = np.maximum(w, L7.EPS_W) / var
    out = []
    for Amat, bvec, tg in L7.alt_regions_for(T):
        res = L7.solve_region(theta, H, Amat, bvec, starts=2)
        if res is None or L7.region_violation(Amat, bvec, res.x) > L7.FEAS_TOL:
            continue
        out.append((float(res.fun), str(tg)))
    out.sort()
    return out


def binom_tail(k, n, p):
    return float(sum(math.comb(n, j) * p ** j * (1 - p) ** (n - j) for j in range(k, n + 1)))


def main():
    global OUT
    smoke = "--smoke" in sys.argv
    if "--out" in sys.argv:
        d = pathlib.Path(sys.argv[sys.argv.index("--out") + 1])
        d.mkdir(parents=True, exist_ok=True)
        OUT = d / OUT.name
    if OUT.exists():
        print(f"refusing to overwrite existing {OUT}", file=sys.stderr)
        return 2
    n_runs = 2 if smoke else N_RUNS
    budget_scale = 0.2 if smoke else 1.0
    config = {"cells": CELLS, "arms": ARMS, "alpha": ALPHA, "n_runs": N_RUNS,
              "oracle_every": ORACLE_EVERY, "check_every": CHECK_EVERY}
    config_sha = hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()
    t0 = time.time()
    print("Paper A, A-F3: the shipped learner on a finite panel", flush=True)
    params = list(inspect.signature(L7.run).parameters)
    check("the learner's `run` takes no world argument (it sees a sampler closure only)",
          not any(p in ("theta", "world", "truth") for p in params), f"parameters {params}")

    cells_out = []
    for ci, cell in enumerate(CELLS):
        theta, var = world(cell)
        truth = L7.best_answer(theta)
        lo, up, w_or = L7.oracle_bracket(theta, var, L7.alt_regions_for(truth), iters=40)
        vu = region_values(theta, var, truth, np.ones(8) / 8.0)
        vo = region_values(theta, var, truth, w_or)
        tag = vu[0][1]
        within1 = [tg for v, tg in vu if v <= vu[0][0] * 1.01]
        ties = [tg for v, tg in vo if v <= vo[0][0] * (1 + 1e-4)]
        budget = int(cell["budget"] * budget_scale)
        print(f"  cell {cell['name']}: truth {truth}, Gamma in [{lo:.4e}, {up:.4e}],"
              f" uniform-design region {within1}, optimum tie set {ties}, budget {budget}",
              flush=True)
        arms_out = {}
        for ai, arm in enumerate(ARMS):
            runs = []
            for ix in range(n_runs):
                rng = np.random.default_rng([20260925, ci, ai, ix])
                sampler = L7.make_sampler(theta, var)
                t, ans, N, c, sel, br, cert = L7.run(rng, sampler, var, ALPHA, budget, arm,
                                                     ORACLE_EVERY, CHECK_EVERY,
                                                     w_oracle=w_or)
                w_emp = N / N.sum()
                j_lo = L7.J_at_lower(w_emp, theta, var, L7.alt_regions_for(truth))
                runs.append({
                    "tau": int(t), "answer": ans, "censored": bool(c),
                    "counts": [float(x) for x in N],
                    "stop_certificate": cert,
                    "selection_trace": sel,
                    "max_oracle_gap_per_refresh": [b.get("max_gap") for b in br],
                    "offline_J_true_lower_at_empirical_design":
                        float(j_lo[0] if isinstance(j_lo, tuple) else j_lo)})
                print(f"    [{time.time() - t0:7.0f}s] {cell['name']} {arm} run {ix + 1}/{n_runs}:"
                      f" tau={t} ans={ans} cens={c}", flush=True)
            stopped = [x for x in runs if not x["censored"]]
            arms_out[arm] = {
                "runs": runs, "stopped": len(stopped),
                "stopped_wrong": sum(1 for x in stopped if x["answer"] != truth),
                "censored": sum(1 for x in runs if x["censored"]),
                "restricted_mean_tau": float(np.mean([x["tau"] for x in runs])),
                "label": "ORACLE-ALLOCATION DIAGNOSTIC (design from the true world)"
                         if arm == "oracle" else "deployable"}
        cells_out.append({**cell, "budget_used": budget, "truth": truth,
                          "Gamma_lower_at_truth": float(lo), "Gamma_upper_at_truth": float(up),
                          "active_region_at_uniform_design": tag,
                          "regions_within_1pct_at_uniform_design": within1,
                          "optimum_tie_set": ties,
                          "region_values_at_uniform_design": vu,
                          "arms": arms_out})

    all_runs = [x for c in cells_out for a in c["arms"].values() for x in a["runs"]]
    ok_count = all(a["stopped"] + a["censored"] == len(a["runs"])
                   for c in cells_out for a in c["arms"].values())
    check("every run is accounted for once as stopped or censored", ok_count)
    margins = [x["stop_certificate"]["margin"] for x in all_runs
               if not x["censored"] and x["stop_certificate"]]
    check("every stop carries a positive certificate margin (statistic above threshold)",
          all(m > 0 for m in margins) and len(margins) == sum(1 for x in all_runs
                                                               if not x["censored"]),
          f"{len(margins)} stops, smallest margin {min(margins, default=float('nan')):.3e}")
    n_stop = sum(a["stopped"] for c in cells_out for a in c["arms"].values())
    n_wrong = sum(a["stopped_wrong"] for c in cells_out for a in c["arms"].values())
    tail = binom_tail(n_wrong, n_stop, ALPHA) if n_stop else 1.0
    check("wrong answers among stopped runs are consistent with alpha", tail >= 1e-3,
          f"{n_wrong} wrong of {n_stop} stopped, tail {tail:.3f}")
    check("the truths are A on the base cells and B on the swapped cell",
          all(c["truth"] == ("B" if c["swapped"] else "A") for c in cells_out))
    reg = {c["name"]: c["regions_within_1pct_at_uniform_design"] for c in cells_out}
    check("at the uniform design the active region changes between M = 16 and M = 64 (the"
          " transition is present in the panel): M = 16's argmin is not within 1% at M = 64",
          len(reg["base_M16_gap4"]) >= 1 and reg["base_M16_gap4"][0] not in reg["base_M64_gap4"],
          f"M=16: {reg['base_M16_gap4']}, M=64: {reg['base_M64_gap4']}")

    out = {"producer": "scripts/EXP_paperA7_panel.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "learner_source_sha256": hashlib.sha256(
               pathlib.Path("scripts/EXP_paperA7_learner.py").read_bytes()).hexdigest(),
           "config": config, "config_sha256": config_sha, "smoke": smoke,
           "cells": cells_out, "failures": dict(L7.FAILURES),
           "scope": "shipped learner, finite panel; oracle arm is an oracle-allocation"
                    " diagnostic; cost estimation, not error certification",
           "wall_seconds": time.time() - t0,
           "checks": CHECKS, "all_passed": all(c["ok"] for c in CHECKS)}
    if not out["all_passed"]:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    OUT.write_text(json.dumps(out, indent=1))
    print(f"\n{sum(c['ok'] for c in CHECKS)}/{len(CHECKS)} self-checks passed; wrote {OUT}",
          flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
