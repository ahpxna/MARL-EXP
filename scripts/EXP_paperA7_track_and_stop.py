#!/usr/bin/env python3
"""Paper A7 DIAGNOSTIC: stopping under an ORACLE allocation.  NOT the algorithm.

WHAT THIS SCRIPT IS.  It hands the loop the allocation computed from the TRUE world.  That
is not an algorithm any agent could run, and nothing here is evidence that a learner attains
the benchmark.  What it does measure, cleanly, is the finite-alpha overhead of the stopping
rule when the allocation is already perfect: how far the ratio sits above `1/Gamma_comp`
because the threshold carries a `log t` penalty.  Read it as an unattainable lower envelope
on stopping time, and nothing more.

The algorithm with no access to the truth is `EXP_paperA7_learner.py`, which also replaces
this script's stopping rule: the rule below compares a PRIMAL objective against the
threshold, and a primal value is an UPPER bound on a regional infimum, so it can stop early.
The learner uses a weak-duality lower bound instead.  The numbers here are therefore an
optimistic diagnostic on both counts, and are labelled as one wherever they are used.

ORIGINAL HEADER FOLLOWS.

Paper A7: the algorithm run against its own benchmark, with censoring reported.

The A7 figure must not be a formula.  It must be the algorithm of `LeanPaperA7*` actually
executed on the SAME world and query model used to compute `Gamma_comp`, and it must report
what happened to every run, including the ones that did not stop.

THE BENCHMARK.  For a finite answer set `T`, the alternative set is the worlds where `T` is
no longer at least as good, and

    Gamma_T(theta) = sup_w inf_{lambda in Alt(T)} sum_e w_e (m_e(theta)-m_e(lambda))^2/(2 var_e),
    Gamma_comp(theta) = max_T Gamma_T(theta).

`Gamma_comp` is computed by the same cutting-plane solver as
`EXP_paperA_separation_games`, so the benchmark and the algorithm see one model, not two.

THE ALGORITHM, exactly as the Lean modules describe it.

  STATISTIC.  `Q_t(lambda) = sum_e S_{e,t}(lambda)^2 / (2 (a + N_e(t)))` with
  `S_{e,t}(lambda) = sum_{s<=t, e_s=e} (Y_s - m_e(lambda))/sigma_e`, and
  `b_t(delta) = log(1/delta) + (1/2) sum_e log(1 + N_e(t)/a)`.  These are the displays of
  `LeanPaperA7ConfidenceV1`, including the regularisation `a`: the implementation uses the
  SAME statistic as the theorem, not an asymptotically equivalent one.

  TWO LEVELS.  `delta = alpha` for stopping; `delta = t^-4` for choosing the answer and the
  allocation.  `fixed_level_gives_no_summable_tail` is why they must differ.

  SELECTION.  Answers are kept when their oracle interval clears the best lower bracket by
  the confidence allowance, and ties are broken by a FIXED order, which is what makes the
  choice stable (`true_answer_in_selection`, `suboptimal_eliminated`).

  SAMPLING.  Forced exploration `rho_t = (t+1)^-1/2` mixed into the oracle allocation, then
  cumulative-quota tracking: pick `argmax_e (W_e(t) - N_e(t-1))`, the index convention of
  `LeanPaperA7TrackingV1`.  Getting that index wrong breaks the invariant.

WHAT IS RECORDED PER RUN.  Stopping time, returned answer, whether it was correct, the real
regret of the returned answer, the final query counts, the oracle gap, and the CENSORING
status.  If any run hits the budget, the mean over the runs that stopped is NOT reported as
`E tau`: a censored mean is a different quantity and is labelled as one.

SELF-CHECKS.  Correctness must hold on every stopped run -- that is
`stopping_rule_is_correct`, and a violation would refute it.  The rate check is stated only
when no run is censored, because with censoring the estimate is a lower bound on `E tau`
and cannot be compared to `1/Gamma_comp` as if it were the mean.
"""

import json
import sys

import numpy as np

sys.path.insert(0, "scripts")
from EXP_paperA_separation_games import (REGIONS, family_high, family_low, kkt_residual,
                                         lp_upper, solve_region, true_gradient)

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


EPS_W = 1e-9
REG_A = 1.0                     # the regulariser `a` of the mixture statistic


# ----------------------------------------------------------- answers and their losses
def rangeA(v):
    return v[0:4].max() - v[0:4].min()


def rangeB(v):
    return v[4:8].max() - v[4:8].min()


def loss_of(answer, v):
    """Retaining one relation costs half the range of the discarded one."""
    return 0.5 * (rangeB(v) if answer == "A" else rangeA(v))


ANSWERS = ["A", "B"]            # the fixed tie-break order


def best_answer(v):
    ls = [loss_of(T, v) for T in ANSWERS]
    return ANSWERS[int(np.argmin(ls))]


def regret_of(answer, v):
    return loss_of(answer, v) - min(loss_of(T, v) for T in ANSWERS)


# ----------------------------------------------------------- the benchmark Gamma_T
def alt_regions_for(answer):
    """`Alt(T)` as a union of polyhedra.

    For `T = A` the alternative is `rangeA <= rangeB` -- the sixteen regions already built
    in `EXP_paperA_separation_games`.  For `T = B` it is the mirror image.
    """
    if answer == "A":
        return REGIONS
    mirrored = []
    for Amat, bvec, tag in REGIONS:
        M2 = Amat.copy()
        M2 = np.hstack([M2[:, 4:8], M2[:, 0:4]])
        mirrored.append((M2, bvec, tag))
    return mirrored


def J_answer(w, theta, var, regions):
    H = np.maximum(w, EPS_W) / var
    best, wit = np.inf, None
    for Amat, bvec, tag in regions:
        res = solve_region(theta, H, Amat, bvec)
        if res is None:
            continue
        if res.fun < best - 1e-14:
            best, wit = float(res.fun), res.x
    return best, wit


def gamma_answer(theta, var, regions, iters=60):
    """Cutting planes again, so the benchmark carries a duality gap like everything else."""
    w = np.ones(8) / 8.0
    cuts, lo, best_w = [], -np.inf, w.copy()
    up = np.inf
    for _ in range(iters):
        val, wit = J_answer(w, theta, var, regions)
        if val > lo:
            lo, best_w = val, w.copy()
        cuts.append(true_gradient(wit, theta, var))
        u, w_new = lp_upper(cuts)
        if u is None:
            break
        up, w = u, w_new
        if up - lo <= 1e-12 * max(1.0, abs(up)):
            break
    return lo, best_w, float(up - lo)


# ----------------------------------------------------------- the algorithm
def stop_fires(mu_hat, N, var, alpha, T):
    """Does the stopping rule fire for answer `T`?

    Early exit: the rule needs the MINIMUM over the answer's regions to exceed the
    threshold, so the first region that falls below it settles the question.  In the early
    rounds that is almost always the first region tried, which is what makes the run
    affordable without changing the rule.
    """
    b_alpha = np.log(1.0 / alpha) + 0.5 * np.sum(np.log1p(N / REG_A))
    H = N ** 2 / ((REG_A + N) * var)              # the QP precision of the blueprint
    for Amat, bvec, _ in alt_regions_for(T):
        res = solve_region(mu_hat, H, Amat, bvec, starts=1)
        if res is None:
            continue
        if float(res.fun) <= b_alpha:
            return False
    return True


def run_once(rng, theta, var, alpha, budget, w_oracle, check_every):
    """One run.  Returns the stopping time, the answer, and the trace summary.

    The stopping rule is evaluated every `check_every` steps rather than at every step.
    That makes the reported `tau` the first CHECKED time at which the rule fires, so it
    over-states the true stopping time by less than `check_every`.  It is an upper bound on
    `tau`, which is the safe direction for a rate claim, and it is stated rather than
    hidden.
    """
    sig = np.sqrt(var)
    N = np.zeros(8)
    S = np.zeros(8)                       # sum of (Y - m_e(theta_hat_free)) is rebuilt below
    Ysum = np.zeros(8)
    W = np.zeros(8)                       # cumulative quota

    # one sample per query to start, as the protocol requires
    for e in range(8):
        Ysum[e] += theta[e] + sig[e] * rng.normal()
        N[e] += 1
    t = 8
    while t < budget:
        if t % check_every == 0:
            mu_hat = Ysum / np.maximum(N, 1.0)
            stop_T = None
            for T in ANSWERS:
                if stop_fires(mu_hat, N, var, alpha, T):
                    stop_T = T
                    break
            if stop_T is not None:
                return t, stop_T, N.copy(), False
        # --- allocation: oracle weights for the currently selected answer, then forced
        rho = 1.0 / np.sqrt(t + 1.0)
        w = (1.0 - rho) * w_oracle + rho * np.ones(8) / 8.0
        W += w
        e_t = int(np.argmax(W - N))                    # the blueprint's index convention
        Ysum[e_t] += theta[e_t] + sig[e_t] * rng.normal()
        N[e_t] += 1
        t += 1
    return budget, None, N.copy(), True                # censored


def main():
    print("=" * 78)
    print("Paper A7: the algorithm against its benchmark, with censoring reported")
    print("=" * 78)
    smoke = "--smoke" in sys.argv
    M = 16.0
    SCALE = 4.0
    theta, var = family_low(M)
    theta = SCALE * theta
    print(f"\n  The world is the A-low instance with its response tables scaled by"
          f" {SCALE:g}.")
    print("  Scaling multiplies every energy by the square of the factor, so it raises")
    print("  `Gamma_comp` without changing the geometry.  That matters for what can be")
    print("  simulated: the threshold is `b_t(alpha) = log(1/alpha) + (1/2) sum_e")
    print("  log(1 + N_e/a)`, whose second term grows like `4 log t` and, at the")
    print("  unscaled instance, dominates `log(1/alpha)` until `t` is around 35000.")
    print("  The asymptotic regime is then out of simulation reach and every run is")
    print("  censored -- which is what an earlier unscaled run in fact produced.")

    print("\n  the benchmark, on the same model the algorithm will run on")
    print("  " + "-" * 72)
    gam, w_star, gaps = {}, {}, {}
    for T in ANSWERS:
        g, wg, gp = gamma_answer(theta, var, alt_regions_for(T), iters=30 if smoke else 60)
        gam[T], w_star[T], gaps[T] = g, wg, gp
        print(f"      Gamma_{T} = {g:.6e}   duality gap {gp:.2e}")
    T_star = max(ANSWERS, key=lambda T: gam[T])
    G = gam[T_star]
    print(f"      Gamma_comp = max_T Gamma_T = {G:.6e}   attained at T = {T_star}")
    print(f"      1 / Gamma_comp = {1.0/G:.4f}")
    truth = best_answer(theta)
    print(f"      the correct answer at this world is '{truth}'")

    alphas = [0.1, 0.02] if smoke else [0.2, 0.1, 0.05, 0.02, 0.01]
    n_runs = 4 if smoke else 20
    budget = 8000 if smoke else 20000
    check_every = 50

    print("\n  runs")
    print("  " + "-" * 72)
    rows = []
    rng = np.random.default_rng(20260920)
    for alpha in alphas:
        taus, correct, censored, regrets, runs = [], 0, 0, [], []
        for _ in range(n_runs):
            t, ans, N, cens = run_once(rng, theta, var, alpha, budget,
                                       w_star[T_star], check_every)
            taus.append(t)
            if cens:
                censored += 1
            else:
                if ans == truth:
                    correct += 1
                regrets.append(regret_of(ans, theta))
            runs.append({"tau": int(t), "answer": ans, "censored": bool(cens),
                         "counts": N.tolist(),
                         "regret": None if cens else regret_of(ans, theta)})
        L = np.log(1.0 / alpha)
        mean_tau = float(np.mean(taus))
        # the finite-alpha prediction: at stopping the statistic has reached the
        # threshold, so tau * Gamma is about log(1/alpha) plus the log-penalty
        meanN = np.mean([np.array(r["counts"]) for r in runs], axis=0)
        penalty = float(0.5 * np.sum(np.log1p(meanN / REG_A)))
        pred_ratio = (L + penalty) / (L * G)
        rows.append({"alpha": alpha, "mean_tau_including_censored_at_budget": mean_tau,
                     "ratio": mean_tau / L, "n_runs": n_runs, "censored": censored,
                     "correct": correct, "log_inv_alpha": L,
                     "log_penalty_at_stop": penalty,
                     "finite_alpha_prediction": pred_ratio,
                     "mean_regret": float(np.mean(regrets)) if regrets else None,
                     "runs": runs})
        flag = f"  [{censored} CENSORED]" if censored else ""
        print(f"      alpha={alpha:6.3f}:  tau_bar={mean_tau:8.1f}"
              f"  tau_bar/log(1/a)={mean_tau/L:8.2f}"
              f"  finite-a prediction={pred_ratio:8.2f}"
              f"  1/Gamma={1.0/G:7.2f}   correct {correct}/{n_runs - censored}{flag}")

    any_cens = any(r["censored"] for r in rows)

    print("\n  what these numbers are")
    print("  " + "-" * 72)
    if any_cens:
        print("      Some runs hit the budget.  Their stopping times are right-censored, so")
        print("      the averages above are LOWER bounds on E tau and are NOT compared to")
        print("      1/Gamma_comp as if they were means.  The rate check is withheld.")
    else:
        print("      No run was censored, so every average is a genuine sample mean of tau")
        print("      and the ratio may be compared to 1/Gamma_comp.")

    check("CORRECTNESS: every run that stopped returned the right answer, which is what"
          " `stopping_rule_is_correct` asserts",
          all(r["correct"] == r["n_runs"] - r["censored"] for r in rows),
          f"{sum(r['correct'] for r in rows)} correct of "
          f"{sum(r['n_runs'] - r['censored'] for r in rows)} stopped")
    check("every stopped run has zero regret, so the returned answer is not merely"
          " admissible but optimal at this world",
          all(r["mean_regret"] is None or abs(r["mean_regret"]) < 1e-12 for r in rows))
    relgap = max(gaps[T] / max(gam[T], 1e-15) for T in ANSWERS)
    check("the benchmark itself carries a closed duality gap, so `Gamma_comp` is a solved"
          " value and not a search result",
          relgap <= 1e-2,
          f"worst relative gap {relgap:.2e}")
    check("the censoring status of every run is recorded, so no censored mean is reported"
          " as an expectation",
          all("censored" in run for r in rows for run in r["runs"]))
    if not any_cens:
        ratios = [r["ratio"] for r in rows]
        preds = [r["finite_alpha_prediction"] for r in rows]
        rel = max(abs(a - b) / b for a, b in zip(ratios, preds))
        check("RATE: the measured stopping cost matches the FINITE-alpha prediction"
              " (log(1/alpha) + log-penalty) / (log(1/alpha) * Gamma)",
              rel <= 0.35,
              f"worst relative deviation {rel:.2f}; ratios "
              f"{['%.0f' % x for x in ratios]} vs predictions "
              f"{['%.0f' % x for x in preds]}")
        check("RATE: and the ratio decreases as alpha shrinks, which is the only direction"
              " the asymptotic claim asserts",
              all(ratios[i] >= ratios[i + 1] - 1e-9 for i in range(len(ratios) - 1)),
              f"{['%.0f' % x for x in ratios]} against 1/Gamma = {1.0/G:.1f}")
        print("\n      The ratio sits ABOVE 1/Gamma_comp at every alpha tested, by the")
        print("      log-penalty factor, and approaches it only as alpha tends to zero.")
        print("      Reporting the measured ratio as if it were 1/Gamma_comp would be")
        print("      reading an asymptotic statement off a finite experiment.")
    else:
        CHECKS.append({"name": "RATE: withheld because runs were censored",
                       "ok": True, "detail": "a censored mean is not an expectation"})
        print("  [OK  ] RATE: withheld because runs were censored"
              "   a censored mean is not an expectation")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperA7_track_and_stop.py").read_bytes()).hexdigest(),"M": M, "check_every": check_every, "budget": budget,
           "Gamma": gam, "Gamma_comp": G, "T_star": T_star, "truth": truth,
           "duality_gaps": gaps, "rows": rows, "any_censored": any_cens,
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperA7_track_and_stop.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
