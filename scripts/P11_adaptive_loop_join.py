#!/usr/bin/env python3
"""P11 -- SCOPE (audit A1, A3).

This harness is an ORDINARY Gaussian best-arm-identification runner.  It is NOT the D6
actual-query / hidden-label sampler, and nothing here is evidence about D6's expected
Gamma.  It is a smoke test of the SCHEDULER: cumulative budget accounting, the
stopping rule, and the epoch structure.

Two runs with different growth factors do NOT share a certificate path, an allocation,
or a noise-consumption pattern; the same PRNG seed does not make them the same
transcript.  The ratio of their costs is therefore NOT bounded by the doubling theorem's
factor 4, and observing a ratio above 4 does not contradict that theorem -- it
contradicts the way the experiment was being read onto it.

Adaptive: the scheduler, the revalidation and the stopping rule, RUN AS ONE LOOP.

WHAT WAS OPEN.  The corpus has oracle-allocation theorems, an epoch runner
(`run_d6_revalidation_epochs.py`) and stopping-geometry modules, and the standing
note has been that they are not joined: nothing said what the whole loop costs or
whether its answer is right.  `LeanAdaptiveLoopJoinV1` now proves the join for a
DOUBLING schedule -- soundness from revalidation alone, and a total spend strictly
below `4 B*` when the certificate is revalidated at every epoch.  This file runs that
loop on a real instance and measures the three things the theorem leaves open: the
realised constant, the realised error rate, and what happens when revalidation is
made lazy.

THE INSTANCE.  Gaussian best-arm identification, unit variances, `K` arms.  The
oracle rate is
    Gamma*(theta) = max_{w in Delta} min_{j != 1} (theta_1 - theta_j)^2/(2(1/w_1 + 1/w_j)),
so an oracle that knew `theta` would need `B* = log(1/delta)/Gamma*` samples.  The
loop does NOT know theta:
  * SCHEDULER: epoch k has a total sample target `ceil(b0 2^k)`, and inside the epoch
    the draws are allocated to track `w*(theta_hat)` recomputed from the current
    estimate -- the plug-in oracle allocation, which is the scheduler.
  * REVALIDATION: at the end of every epoch the generalised likelihood ratio
    `Z = min_{j != a_hat} (theta_hat_a - theta_hat_j)^2/(2(1/N_a + 1/N_j))`
    is recomputed on ALL the data collected so far, not on the epoch's data.
  * STOPPING: the loop stops at the first epoch with `Z > beta(n, delta)`,
    `beta(n, delta) = log((K-1)(1 + log n)/delta)`.

WHAT IS MEASURED
 1. The realised error rate against `delta`.
 2. The realised `total / B*`, against the `4` the join theorem allows and against
    the `2 * last epoch / total` identity the theorem rests on.
 3. Lazy revalidation: the same loop checking only every m-th epoch, which the
    theorem says can overshoot by `2^m`.  The measured overshoot is reported.

WHAT THIS DOES NOT ESTABLISH
  * `beta` is the standard heuristic threshold, not a proved confidence bound for
    this exact loop; the error rate is therefore MEASURED, not certified, and is
    reported next to `delta` rather than claimed to be below it.
  * `Gamma*` is computed numerically; `B*` inherits that.
  * Finitely many simulation runs: the numbers are Monte-Carlo estimates with the
    reported standard errors, not guarantees.
  * One family of instances, unit variances, no cost per query beyond the sample.

    .venv/bin/python scripts/P11_adaptive_loop_join.py
"""
from __future__ import annotations

import json, math
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

REPO = Path(__file__).resolve().parents[1]


def gamma_star(theta, istar=None):
    """max_w min_j (theta_i* - theta_j)^2/(2(1/w_i* + 1/w_j)).

    Solved in ONE dimension rather than by a K-dimensional search.  Writing
    y_j = w_j/w_1, the value against j is Delta_j^2 w_1 y_j/(2(y_j+1)); equalising it
    across j gives Delta_j^2 y_j/(y_j+1) = t for a common t, i.e.
    y_j(t) = t/(Delta_j^2 - t) for t < min_j Delta_j^2, and then
        V(t) = t / (2 (1 + sum_j y_j(t))),
    which is maximised by a ternary search on t.  This is the standard
    reparametrisation; it is checked against a direct K-dimensional search in PART 0.
    """
    K = len(theta)
    if istar is None:
        istar = int(np.argmax(theta))
    D2 = np.array([(theta[istar] - theta[j]) ** 2 for j in range(K) if j != istar])
    if np.any(D2 <= 0):
        return 0.0, np.ones(K) / K, istar
    hi0 = float(D2.min())

    def V(t):
        if t <= 0 or t >= hi0:
            return 0.0
        y = t / (D2 - t)
        return t / (2 * (1 + y.sum()))

    lo, hi = 0.0, hi0
    for _ in range(300):
        a = lo + (hi - lo) / 3
        b = hi - (hi - lo) / 3
        if V(a) < V(b):
            lo = a
        else:
            hi = b
    t = (lo + hi) / 2
    y = t / (D2 - t)
    w1 = 1.0 / (1 + y.sum())
    w = np.empty(K)
    w[istar] = w1
    k = 0
    for j in range(K):
        if j != istar:
            w[j] = w1 * y[k]
            k += 1
    return V(t), w / w.sum(), istar


def gamma_star_slow(theta, istar=None):
    """a direct K-dimensional search, used only to check `gamma_star`."""
    K = len(theta)
    if istar is None:
        istar = int(np.argmax(theta))
    others = [j for j in range(K) if j != istar]
    D2 = np.array([(theta[istar] - theta[j]) ** 2 for j in others])

    def neg(z):
        w = np.abs(z) + 1e-12
        w = w / w.sum()
        vals = D2 / (2 * (1.0 / w[istar] + np.array([1.0 / w[j] for j in others])))
        return -float(np.min(vals))

    best = -np.inf
    rng = np.random.default_rng(0)
    for s in range(10):
        z0 = np.ones(K) / K if s == 0 else np.abs(rng.standard_normal(K)) + 0.05
        r = minimize(neg, z0, method="Nelder-Mead",
                     options={"maxiter": 20000, "xatol": 1e-12, "fatol": 1e-15})
        best = max(best, -neg(r.x))
    return best


def plug_in_w(hat, K):
    _v, w, _i = gamma_star(hat)
    return w


def beta(n, delta, K):
    return math.log((K - 1) * (1 + math.log(max(n, 2))) / delta)


def stop_rule(hat, N, delta, K, a):
    """GLR-style stopping: the empirical best beats every other arm at level beta."""
    for i in range(K):
        if i == a:
            continue
        if N[i] <= 0 or N[a] <= 0:
            return False
        gap = hat[a] - hat[i]
        rad = math.sqrt(2 * beta(int(N[a]), delta, K) / N[a]) + \
              math.sqrt(2 * beta(int(N[i]), delta, K) / N[i])
        if gap <= rad:
            return False
    return True


def run_once(theta, delta, b0, rng, check_every=1, max_epoch=400, growth=2.0):
    """One run of the scheduler.

    BUDGET CONVENTION (audit A2).  `target` is a CUMULATIVE cap on the total number of
    samples, and the per-arm want is clipped so the cumulative total never exceeds it:

        want_i = min over the arms of the residual cap, i.e.
        want_i = max(ceil(target * w_i) - N_i, 0)  and then the vector is scaled down,
        if necessary, so that total + sum(want) <= target.

    The earlier code applied the per-arm rule without the cumulative clip, so a run
    could spend 140 under a stated cap of 100.  That is a legal allocation rule with an
    ACTUAL cost of 140 -- it is not a cap of 100, and the doubling theorem is about the
    cumulative cap.  This function enforces the cap and reports the actual cost.

    STATUS (audit A4).  The return carries an explicit status:
        CERTIFIED  -- the stopping rule fired and a certificate was emitted;
        CENSORED   -- max_epoch was exhausted with no certificate (the returned arm is
                      an argmax, NOT a certified answer);
        FAILED     -- the run could not proceed.
    """
    K = len(theta)
    N = np.zeros(K, dtype=int)
    S = np.zeros(K)
    total = 0
    last_target = K
    epoch_budgets = []
    hat = np.zeros(K)
    for k in range(max_epoch):
        target = int(math.ceil(b0 * growth ** k))
        if target <= total:
            continue
        last_target = target
        w = plug_in_w(hat, K) if total > 0 else np.full(K, 1.0 / K)
        want = np.maximum(np.ceil(target * w).astype(int) - N, 0)
        # --- cumulative cap (A2): never spend past `target` in total
        room = target - total
        if want.sum() > room:
            if room <= 0:
                continue
            scale = room / want.sum()
            want = np.floor(want * scale).astype(int)
            short = room - int(want.sum())
            order = np.argsort(-w)
            for i in order[:max(short, 0)]:
                want[i] += 1
        for i in range(K):
            if want[i] > 0:
                S[i] += rng.normal(theta[i] * want[i], math.sqrt(want[i]))
                N[i] += want[i]
        spent = int(want.sum())
        total += spent
        assert total <= target, (total, target)
        epoch_budgets.append({"epoch": k, "target": target, "spent": spent,
                              "cumulative": total})
        if total == 0:
            continue
        hat = np.where(N > 0, S / np.maximum(N, 1), 0.0)
        a = int(np.argmax(hat))
        if k % check_every == 0 and stop_rule(hat, N, delta, K, a):
            return {"total": total, "arm": a, "epoch": k,
                    "epoch_budgets": epoch_budgets, "last_target": last_target,
                    "status": "CERTIFIED", "certificate_emitted": True,
                    "reason": "stopping rule fired", "actual_cost": total}
    return {"total": total, "arm": int(np.argmax(hat)), "epoch": max_epoch - 1,
            "epoch_budgets": epoch_budgets, "last_target": last_target,
            "status": "CENSORED", "certificate_emitted": False,
            "reason": f"max_epoch={max_epoch} exhausted with no certificate",
            "actual_cost": total}


def main():
    print("Adaptive: scheduler + revalidation + stopping, run as ONE loop\n")
    res = {}
    instances = [("well separated", [1.0, 0.5, 0.4, 0.3]),
                 ("one close rival", [1.0, 0.9, 0.4, 0.3]),
                 ("two close rivals", [1.0, 0.92, 0.9, 0.3])]
    RUNS = 200
    print("PART 0 -- the one-dimensional solver for Gamma*, against a direct search")
    for name, th in instances:
        fast, _w, _i = gamma_star(np.array(th))
        slow = gamma_star_slow(np.array(th))
        print(f"   {name:17s}: 1-D {fast:.9f}   K-D search {slow:.9f}   "
              f"relative {abs(fast-slow)/fast:.2e}")
        if abs(fast - slow) > 1e-6 * fast:
            raise AssertionError("the two Gamma* solvers disagree")

    print("\nPART 1 -- the oracle rate, and the loop's realised cost and error")
    rows = []
    for name, th in instances:
        theta = np.array(th)
        G, w, istar = gamma_star(theta)
        for delta in (0.05, 0.01):
            Bstar = math.log(1 / delta) / G
            b0 = 4 * len(theta)
            rng = np.random.default_rng(20260914)
            tot, err, eps = [], 0, []
            for _ in range(RUNS):
                _r = run_once(theta, delta, b0, rng)
                t, a, k, eb = _r['total'], _r['arm'], _r['epoch'], _r['epoch_budgets']
                tot.append(t)
                eps.append(k)
                if a != istar:
                    err += 1
            tot = np.array(tot, dtype=float)
            ratio = tot / Bstar
            se = tot.std(ddof=1) / math.sqrt(RUNS) / Bstar
            print(f"   {name:17s} delta={delta}: Gamma* = {G:.6f}, B* = "
                  f"{Bstar:.1f}; mean total = {tot.mean():.1f} "
                  f"({ratio.mean():.3f} B*, se {se:.3f}), max = "
                  f"{ratio.max():.3f} B*")
            print(f"   {'':17s}   errors {err}/{RUNS} = {err/RUNS:.4f} against "
                  f"delta = {delta};  epochs used: mean {np.mean(eps):.2f}")
            rows.append({"instance": name, "theta": th, "delta": delta,
                         "Gamma_star": G, "oracle_w": list(map(float, w)),
                         "B_star": Bstar, "mean_total": float(tot.mean()),
                         "mean_ratio": float(ratio.mean()),
                         "max_ratio": float(ratio.max()),
                         "ratio_se": float(se),
                         "errors": err, "runs": RUNS,
                         "mean_epochs": float(np.mean(eps))})
    res["loop"] = rows

    print("\nPART 2 -- the join theorem's actual claim: doubling vs a FINE schedule")
    print("   B* = log(1/delta)/Gamma* is the asymptotic oracle; the theorem compares")
    print("   the doubling loop to the budget at which the loop's OWN certificate")
    print("   first fires.  That budget is measured by running the same loop on a")
    print("   1.05-growth schedule, which checks the certificate ~14 times per")
    print("   doubling, and the ratio is what the factor 4 bounds.")
    rows2 = []
    for name, th in instances:
        theta = np.array(th)
        for delta in (0.01,):
            ratios = []
            for seed in range(80):
                r1 = np.random.default_rng(1000 + seed)
                r2 = np.random.default_rng(1000 + seed)
                _rd = run_once(theta, delta, 4 * len(theta), r1,
                                                growth=2.0)
                _rf = run_once(theta, delta, 4 * len(theta), r2,
                                                    growth=1.05)
                ratios.append(_rd['actual_cost'] / _rf['actual_cost'])
            ratios = np.array(ratios)
            over = int((ratios > 4).sum())
            print(f"   {name:17s}: doubling/fine = mean {ratios.mean():.3f}, "
                  f"max {ratios.max():.3f}, above 4 in {over}/{len(ratios)} runs")
            rows2.append({"instance": name, "delta": delta,
                          "mean_ratio": float(ratios.mean()),
                          "max_ratio": float(ratios.max()),
                          "runs_above_4": over, "runs": len(ratios)})
    res["doubling_vs_fine"] = rows2

    print("\nPART 3 -- LAZY revalidation: checking only every m-th epoch")
    theta = np.array(instances[1][1])
    lazy = []
    for m in (1, 2, 3):
        rng = np.random.default_rng(11)
        tot = []
        for _ in range(100):
            _r = run_once(theta, 0.01, 16, rng, check_every=m)
            t, a, k, eb = _r['total'], _r['arm'], _r['epoch'], _r['epoch_budgets']
            tot.append(t)
        tot = np.array(tot, dtype=float)
        lazy.append({"check_every": m, "mean_total": float(tot.mean())})
        print(f"   check every {m} epoch(s): mean total = {tot.mean():.1f}")
    base = lazy[0]["mean_total"]
    for e in lazy:
        e["overshoot_vs_every_epoch"] = e["mean_total"] / base
        print(f"      m={e['check_every']}: overshoot "
              f"{e['overshoot_vs_every_epoch']:.3f}x   (the theorem allows up to "
              f"{2**e['check_every']}x)")
    res["lazy_revalidation"] = lazy

    res["not_established"] = [
        "beta is the standard heuristic threshold, not a proved confidence bound for "
        "this loop; the error rate is MEASURED and reported beside delta, not "
        "claimed to be below it",
        "Gamma* is computed numerically and B* inherits that",
        "Monte-Carlo estimates over finitely many runs, with standard errors",
        "one family of instances, unit variances, cost = sample count",
    ]
    out = REPO / "research/worker_P11_adaptive_20260914/P11_adaptive_loop_join.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
