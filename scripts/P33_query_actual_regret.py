#!/usr/bin/env python3
"""P33 -- harness contract E-Q: the ACTUAL regret of the likelihood-ratio decision.

`P21` measured the LRT's equal-prior ERROR.  The contract asks for the regret of a real
decision: per world, the LRT selects a world and plays THAT world's optimal action, and
the loss actually paid is recorded -- per world, with a confidence interval, not only
the equal-prior average.

The loss geometry comes from `P16`, which computed it on the corpus's own decisions at
budget 1:

    gamma = 13983/32768 = 0.4267    -- every decision outside a world's good set costs
                                       at least this much in that world;
    L_max = 2401/4096   = 0.5862    -- the cross-world cost of playing the OTHER
                                       world's optimal action;

with the two good sets DISJOINT and of size 1 each.  So the regret of the induced rule
is exactly `L(a_other) * 1{label wrong}` in each world, and the theory window is

    gamma * rho^{2N}/4  <=  R  <=  L_max * rho^N/2.

This file measures `R` by simulation and checks it lands inside that window.  It
reports per-world regret and a bootstrap CI, not merely the equal-prior mean.
"""
from __future__ import annotations
import argparse, importlib.util, json, math, time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[1]
SQ2PI = math.sqrt(2 * math.pi)
SIG = 1.0


def load(name):
    spec = importlib.util.spec_from_file_location(name, REPO / "scripts" / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def phi(u):
    return np.exp(-0.5 * (u / SIG) ** 2) / (SIG * SQ2PI)


def dens(Y, p, FW, gv, h):
    out = np.zeros_like(Y)
    for k in range(len(p)):
        out += p[k] * phi(Y - FW[k] - h * gv[k])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--reps", type=int, default=4000)
    ap.add_argument("--h", type=float, default=0.6)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    out = Path(args.out or (REPO / "research/worker_P33_query_regret_20260915"
                            / "P33_query_actual_regret.json"))
    if out.exists():
        raise SystemExit(f"Refusing to overwrite {out}")
    t0 = time.time()

    geom = json.load(open(REPO / "research/worker_P16_query_20260915"
                          / "P16_query_regret_chain.json"))
    b1 = [b for b in geom["budgets"] if str(b["budget"]) == "1"][0]
    gamma = float(F(b1["gamma"]))
    Lmax = float(F(b1["L_max"]))
    assert b1["disjoint"] in (True, "True")

    P5 = load("P5_query_h4_robustness")
    cfg, m, cube, pdict, FAd, FBd, levels, _ = P5.setup()
    p = np.array([float(pdict[x]) for x in cube])
    FA = np.array([float(FAd[x]) for x in cube])
    FB = np.array([float(FBd[x]) for x in cube])
    g0map, _gap, _c = P5.find_g0(m, cube, pdict, FAd, FBd, levels)
    umap, _ug, uname = P5.pick_u(m, cube, pdict, FAd, FBd, levels)
    norm = lambda v: v / math.sqrt(float(np.dot(p, v ** 2)))
    g0 = norm(np.array([float(g0map[x]) for x in cube]))
    un = norm(np.array([float(umap[x]) for x in cube]))

    lo = float(min(FA.min(), FB.min())) - 9.0
    hi = float(max(FA.max(), FB.max())) + 9.0
    Yq = np.linspace(lo, hi, 200001)

    rng = np.random.default_rng(20260915)
    rows = []
    for name, gv in (("g0_normalised_order2", g0), ("u_normalised_order1", un)):
        h = args.h
        pa = dens(Yq, p, FA, gv, h)
        pb = dens(Yq, p, FB, gv, h)
        H2 = float(np.trapezoid(0.5 * (np.sqrt(pa) - np.sqrt(pb)) ** 2, Yq))
        rho = 1.0 - H2
        L = -math.log1p(-H2)
        N = max(1, math.ceil(math.log(1 / (2 * 0.05)) / L))
        if N > 60000:
            N = 60000
        K = len(p)
        per_world = {}
        losses = {}
        for w, FW in ((0, FA), (1, FB)):
            loss = np.zeros(args.reps)
            for t in range(args.reps):
                sel = rng.choice(K, size=N, p=p)
                Y = FW[sel] + h * gv[sel] + rng.normal(0.0, SIG, size=N)
                la = np.log(dens(Y, p, FA, gv, h) + 1e-300).sum()
                lb = np.log(dens(Y, p, FB, gv, h) + 1e-300).sum()
                pick = 0 if la >= lb else 1
                # play the SELECTED world's own optimal action; pay 0 if right,
                # the cross-world cost L_max if wrong
                loss[t] = 0.0 if pick == w else Lmax
            losses[w] = loss
            per_world[f"world_{w}"] = {
                "error_rate": float((loss > 0).mean()),
                "mean_regret": float(loss.mean()),
                "se": float(loss.std(ddof=1) / math.sqrt(args.reps)),
            }
        allloss = np.concatenate([losses[0], losses[1]])
        mean_R = float(allloss.mean())
        boot = np.array([allloss[rng.integers(0, len(allloss), len(allloss))].mean()
                         for _ in range(2000)])
        ci = [float(np.percentile(boot, 2.5)), float(np.percentile(boot, 97.5))]
        lower = gamma * rho ** (2 * N) / 4
        upper = Lmax * rho ** N / 2
        inside = (lower <= ci[1]) and (mean_R <= upper * 1.05)
        rows.append({
            "measurement": name, "h": h, "H2": H2, "L": L, "N": N,
            "reps_per_world": args.reps,
            "gamma": gamma, "L_max": Lmax,
            "per_world": per_world,
            "equal_prior_mean_regret": mean_R,
            "bootstrap_ci95": ci, "bootstrap_resamples": 2000,
            "theory_lower_gamma_rho2N_over_4": lower,
            "theory_upper_Lmax_rhoN_over_2": upper,
            "inside_window": bool(inside),
        })
        print(f"  {name:24s} h={h} H2={H2:.4e} N={N}: "
              f"regret={mean_R:.5f} CI[{ci[0]:.5f},{ci[1]:.5f}]  "
              f"per-world {per_world['world_0']['mean_regret']:.5f}/"
              f"{per_world['world_1']['mean_regret']:.5f}  "
              f"window [{lower:.4e},{upper:.4e}]  inside={inside}", flush=True)

    out_obj = {
        "script": "P33_query_actual_regret.py", "contract": "E-Q",
        "loss_geometry_source": "research/worker_P16_query_20260915/"
                                "P16_query_regret_chain.json, budget 1",
        "gamma": gamma, "L_max": Lmax,
        "decision_rule": "likelihood-ratio test on the true mixture densities, then "
                         "play the SELECTED world's own optimal action; loss 0 when the "
                         "label is right, L_max when it is wrong",
        "rows": rows, "wall_seconds": round(time.time() - t0, 1),
        "not_established": [
            "MONTE CARLO with a bootstrap CI.  The window it is checked against is a "
            "THEOREM (QueryRegretBridge + AffinityTesting); the measurement is not.",
            "The prior is equal: this is Bayes regret, not worst-case minimax.",
            "h = 0.6 sits ABOVE the crossover h* = 0.1133 found in P21, so these sample "
            "counts must not be read as evidence about the leakage ORDER.",
            "The loss table is the corpus's own at budget 1; a different budget gives "
            "different gamma and L_max.",
        ],
        "lean": "LeanQueryRegretBridgeV1 (regret_ge_gamma_error, lrt_regret_le, "
                "bayes_regret_window); LeanQueryAffinityTestingV1 (the bracket)",
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("x") as f:
        json.dump(out_obj, f, indent=1)
        f.write("\n")
    print(f"\nartifact: {out}")


if __name__ == "__main__":
    main()
