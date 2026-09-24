#!/usr/bin/env python3
"""Paper B: the two decoders on the parity-mask channel, measured.

THE CHANNEL IS THE ONE THE THEOREM IS ABOUT.  World `w` in `1..m` has `K_w = {0, tip_w}`, so
`tip_j in K_w` exactly when `j = w` and the mask value is

    v(j, w) = -1 if j == w else +1      (`maskVal`, LeanPaperBParityV1).

Query `j` returns

    Y_j = v(j,w) * prod_{l<=j} Z_l + (h/j) * sum_{l<=j} Z_l + xi,    xi ~ N(0, sigma^2),

with `Z` a latent uniform sign cube the learner never sees.

WHY A BOUNDED STATISTIC.  `cube_difference` / `parity_cf_difference` (LeanPaperBParityV1)
give an UNNORMALISED sum over the `2^j` cube points,

    2^{j+1} * sinh(i t) * sinh(i t h / j)^j,

which is NOT yet a characteristic function: the cube is uniform, so each point carries
probability `2^{-j}`, and the independent Gaussian noise contributes its own factor.  The
characteristic-function difference of the two OBSERVATION laws is therefore

    phi_{+,j}(t) - phi_{-,j}(t) = 2 i^{j+1} sin(t) sin(t h / j)^j exp(-sigma^2 t^2 / 2),

magnitude `2 |sin t| |sin(th/j)|^j exp(-sigma^2 t^2/2)` -- order `h^j`.  The factor is `2`,
not `2^{j+1}`: the `2^{-j}` normalisation cancels all but one power of two.  `closed_form_gap`
below implements the normalised form, so the measured numbers are unaffected; it is the
Lean statement and the manuscript that state the unnormalised sum and owe the link.  The
`v`-dependent term is REAL when `j` is odd and IMAGINARY when `j` is even, so the statistic
is `cos(t0 Y)` or `sin(t0 Y)` by parity.  Both are bounded by one, which is the whole point:
the `Y^{j+1}` moment estimator has a variance that explodes with `j`, and this one does not.

THE TWO DECODERS.
  * SAFE.  `A_w = [m] \\ {w}`, so it suffices to know whether `w = 1`: answer `2` if it is,
    `1` otherwise.  One query, of order `1`.
  * IDENTIFICATION.  Must name the world, so it runs queries `1..m-1` and the budget is the
    SUM, not the per-test sample size.

WHAT IS MEASURED AND HOW.  Per world, equal repetitions, Clopper-Pearson bounds.  A budget
is only reported as achieving error `<= delta` when the worst-world UPPER bound clears
`delta`.  Points that do not clear within the ladder are reported as censored rather than
dropped.  Errors are plotted against `N` first and only then against `N h^2` and
`N h^{2(m-1)}`.

A CERTIFIED BUDGET IS AN UPPER BOUND, AND NOTHING ELSE UNTIL THE LOWER SIDE ALSO CERTIFIES.
A rung that failed to certify is a rung whose upper bound came out above `delta`; that is
not evidence its true error EXCEEDS `delta`.  So "the grid has ratio two, therefore the
minimal budget is known within a factor of two" does not follow, and no slope tolerance may
be derived from it.  A budget is bracketed only when a CP LOWER bound at some smaller rung
also exceeds `delta`, and only a CONTIGUOUS PREFIX of proved-failing rungs excludes anything
-- a fixed decoder's error is not known to be monotone in `N`, so one failing rung below a
success excludes nothing between them.  `failed_prefix`, `grid_min_lower_inclusive` and
`bracketed` record this.  The resulting interval brackets the first SUCCESSFUL TESTED
budget on this grid; it bounds neither the untested integers nor the minimum over all
decoders, and a slope read across such intervals is not a confidence interval for an
asymptotic exponent.  Both CP tails are budgeted, at `0.05/(2J)` each.

THE ZERO-QUERY FLOOR, WHICH IS NOT THE SAME NUMBER FOR THE TWO TASKS.  For the SAFE
decision, `A_w = [m] \\ {w}`, so a uniform guess made without any query is unsafe exactly
when it names the true world: probability `1/m`.  That is the floor the Lean theorem
`zero_query_floor` is about, and no positive sample requirement can hold for `delta >= 1/m`.
For IDENTIFICATION the decoder must NAME the world, so a uniform guess is CORRECT with
probability `1/m` and therefore WRONG with probability `1 - 1/m`; the floor is `1 - 1/m`.
Recording `1/m` on an identification cell would attach the safe decision's floor to a task
that does not have it, so the floor is stored per decoder and the task it belongs to is
stored beside it.

SELF-CHECKS.  The exact means are recomputed by enumerating the cube and matched against the
closed form; the measured gap order is matched against `j`; the floor is checked; and the
script refuses to report if any check fails.
"""

import hashlib
import itertools
import json
import math
import pathlib
import sys

import numpy as np
from scipy import stats

CHECKS = []
SIGMA = 1.0
T0 = 1.0


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def mask_val(j, w):
    """`maskVal j w`: -1 exactly when the query names the world."""
    return -1.0 if j == w else 1.0


def exact_mean(j, v, h, use_cos):
    """E[cos(t0 Y)] or E[sin(t0 Y)], by enumerating the 2^j cube exactly."""
    tot = 0.0 + 0.0j
    for z in itertools.product((-1.0, 1.0), repeat=j):
        prod = 1.0
        for zz in z:
            prod *= zz
        s = sum(z)
        mean = v * prod + (h / j) * s
        # E[exp(i t0 (mean + xi))] = exp(i t0 mean) * exp(-sigma^2 t0^2 / 2)
        tot += np.exp(1j * T0 * mean)
    tot = tot / (2 ** j) * math.exp(-(SIGMA ** 2) * (T0 ** 2) / 2)
    return tot.real if use_cos else tot.imag


def closed_form_gap(j, h):
    """|2 * sin(t0) * sin(t0 h / j)^j| * exp(-sigma^2 t0^2/2): the CF difference magnitude."""
    return abs(2.0 * math.sin(T0) * (math.sin(T0 * h / j) ** j)
               * math.exp(-(SIGMA ** 2) * (T0 ** 2) / 2))


def sample_stat(rng, j, w, h, N, use_cos):
    """N draws of the bounded statistic at query j under world w."""
    Z = rng.choice((-1.0, 1.0), size=(N, j))
    prod = Z.prod(axis=1)
    ssum = Z.sum(axis=1)
    xi = rng.normal(0.0, SIGMA, size=N)
    Y = mask_val(j, w) * prod + (h / j) * ssum + xi
    return np.cos(T0 * Y) if use_cos else np.sin(T0 * Y)


def query_decides_named(rng, j, w, h, N):
    """Run query j and decide whether the world is named by it (i.e. w == j)."""
    use_cos = (j % 2 == 1)
    mu_named = exact_mean(j, -1.0, h, use_cos)     # v = -1  <=>  w == j
    mu_other = exact_mean(j, +1.0, h, use_cos)
    thr = (mu_named + mu_other) / 2.0
    x = sample_stat(rng, j, w, h, N, use_cos).mean()
    if mu_named < mu_other:
        return x < thr
    return x > thr


def safe_decoder_unsafe(rng, m, w, h, N):
    """Answer 2 if the world looks like 1, else 1.  Unsafe exactly when the answer is w."""
    looks_one = query_decides_named(rng, 1, w, h, N)
    ans = 2 if looks_one else 1
    return ans == w


def id_decoder_wrong(rng, m, w, h, N):
    """Queries 1..m-1; the world is the one that fires, else m.  Budget is (m-1)*N."""
    named = [j for j in range(1, m) if query_decides_named(rng, j, w, h, N)]
    guess = named[0] if len(named) == 1 else (m if len(named) == 0 else -1)
    return guess != w


def cp_upper(k, n, conf=0.95):
    if n == 0:
        return 1.0
    if k >= n:
        return 1.0
    return float(stats.beta.ppf(conf, k + 1, n - k))


def cp_lower(k, n, conf=0.95):
    """Clopper-Pearson LOWER confidence bound on the error probability.

    This is the half a one-sided ladder does not give you.  A rung that failed to CERTIFY
    `error <= delta` has only an upper bound that came out too big; that is not evidence
    that its true error EXCEEDS `delta`.  Concluding "the minimal budget is above the
    previous rung, so it is located within a factor of two" from a failure to certify is
    invalid.  To bracket a budget from below one needs THIS bound at the lower rung to sit
    strictly above the target."""
    if n == 0:
        return 0.0
    if k <= 0:
        return 0.0
    return float(stats.beta.ppf(1.0 - conf, k, n - k + 1))


def main():
    rng = np.random.default_rng(20260922)
    ms = [3, 4]
    hs = [0.6, 0.45, 0.32, 0.22]
    reps = 400
    delta_target = 0.05

    # ---- self-check 1: the closed-form gap matches the enumerated means -------------
    gap_rows, ok_gap = [], True
    for j in (1, 2, 3):
        for h in hs:
            use_cos = (j % 2 == 1)
            g = abs(exact_mean(j, -1.0, h, use_cos) - exact_mean(j, +1.0, h, use_cos))
            gc = closed_form_gap(j, h)
            ok_gap &= abs(g - gc) < 1e-12
            gap_rows.append({"j": j, "h": h, "gap_enumerated": g, "gap_closed_form": gc})
    check("the enumerated mean gap equals the closed form 2|sin t0||sin(t0 h/j)|^j e^{-s^2t0^2/2}"
          " -- the characteristic-function identity, not a fit", ok_gap,
          f"{len(gap_rows)} (j,h) cells, worst |difference| "
          f"{max(abs(r['gap_enumerated']-r['gap_closed_form']) for r in gap_rows):.2e}")

    # ---- self-check 2: the order, stated the way the theorem states it ------------
    # `gap_at_scale` (LeanPaperBAttainV1) proves  (3x/4)^j <= sin(x)^j  for 0 < x <= 1,
    # so the gap is bounded BELOW by a constant times h^j.  That is the Theta(h^j)
    # statement.  A log-log slope at finite h is NOT the order: sin(x) = x(1 - x^2/6 + ...)
    # drags it below j, and the drag is what the coarse grid shows.
    ok_lower, lower_rows = True, []
    for j in (1, 2, 3):
        for h in hs:
            x = T0 * h / j
            lhs = (3 * x / 4) ** j
            rhs = math.sin(x) ** j
            ok_lower &= (x <= 1.0) and (lhs <= rhs + 1e-15)
            lower_rows.append({"j": j, "h": h, "x": x, "three_quarter_power": lhs,
                               "sin_power": rhs})
    check("the proved lower bound (3x/4)^j <= sin(x)^j holds at every cell, so the gap is"
          " bounded below by a constant times h^j -- this is the Theta(h^j) claim, and it is"
          " a theorem (gap_at_scale), not a fit", ok_lower,
          f"{len(lower_rows)} cells, all with x = t0 h / j <= 1")

    ok_order, order_rows = True, []
    fine = [0.08, 0.06, 0.04, 0.03, 0.02]
    for j in (1, 2, 3):
        slope_coarse = float(np.polyfit([math.log(h) for h in hs],
                                        [math.log(closed_form_gap(j, h)) for h in hs], 1)[0])
        slope_fine = float(np.polyfit([math.log(h) for h in fine],
                                      [math.log(closed_form_gap(j, h)) for h in fine], 1)[0])
        ok_order &= abs(slope_fine - j) < 0.01
        order_rows.append({"j": j, "slope_coarse_grid": slope_coarse,
                           "slope_fine_grid": slope_fine, "predicted": j})
    check("the log-log slope CONVERGES to j as h shrinks: on the fine grid it is within 0.01"
          " of j, while the coarse grid sits below it -- the finite-h drag is the sine's"
          " cubic term and is reported, not hidden", ok_order,
          "; ".join(f"j={r['j']}: coarse {r['slope_coarse_grid']:.3f} -> fine"
                    f" {r['slope_fine_grid']:.4f}" for r in order_rows))

    # ---- the two decoders, per world, equal repetitions -----------------------------
    results = []
    for m in ms:
        # The safe decision's zero-query error is `1/m` (a uniform guess is unsafe only if
        # it names the true world); identification's is `1 - 1/m` (a uniform guess is right
        # only if it names the true world).  They are different numbers and are kept apart.
        floor_safe = 1.0 / m
        floor_id = 1.0 - 1.0 / m
        for h in hs:
            for w in range(1, m + 1):
                # The ladder is extended to 25600 so the identification decoder has rungs
                # where it can actually certify: at 1600 seven of the eight identification
                # cells were censored, which left no measured rate curve at all.
                for N in (25, 50, 100, 200, 400, 800, 1600, 3200, 6400, 12800, 25600):
                    bad_safe = sum(safe_decoder_unsafe(rng, m, w, h, N) for _ in range(reps))
                    results.append({
                        "decoder": "safe", "m": m, "h": h, "world": w, "N_per_query": N,
                        "total_budget": N, "reps": reps,
                        "bad": int(bad_safe),
                        "err": bad_safe / reps, "err_upper95": cp_upper(bad_safe, reps),
                        "rescaled": N * h ** 2, "zero_query_floor": floor_safe,
                        "floor_task": "safe decision: uniform guess unsafe w.p. 1/m"})
                    bad_id = sum(id_decoder_wrong(rng, m, w, h, N) for _ in range(reps))
                    results.append({
                        "decoder": "identification", "m": m, "h": h, "world": w,
                        "N_per_query": N, "total_budget": (m - 1) * N, "reps": reps,
                        "bad": int(bad_id),
                        "err": bad_id / reps, "err_upper95": cp_upper(bad_id, reps),
                        "rescaled": N * h ** (2 * (m - 1)), "zero_query_floor": floor_id,
                        "floor_task": "identification: uniform guess wrong w.p. 1 - 1/m"})

    # ---- self-check 3: certified budgets use a FAMILY-WISE upper bound --------------
    #
    # The budget reported for a panel is the SMALLEST rung of a 7-rung ladder whose
    # worst-world Clopper-Pearson upper bound clears the target.  Scanning a ladder and
    # reporting the first rung that clears is a selection, and a 95% interval per rung does
    # not survive it.  Every interval computed anywhere in this run is therefore treated as
    # one member of a single family and each is taken at level 1 - 0.05/J, so the reported
    # budgets hold simultaneously at 95%.  Three multiplicities are recorded so the cost of
    # the correction is visible rather than asserted:
    #   J = 1        the old, unadjusted reading (kept only for comparison);
    #   J = 7 * m    the ladder inside one panel, over the m worlds;
    #   J = len(results)  every interval in the run -- the one the report uses.
    #
    # TWO TAILS, ONE BUDGET.  Once BOTH a lower and an upper Clopper-Pearson bound are used,
    # each interval spends error on TWO tails.  Giving each tail `0.05/J` spends `0.10` in
    # total by Bonferroni, not `0.05`.  The per-tail budget is therefore `0.05/(2J)`, so the
    # family-wise statement over both tails of all J intervals holds at 95%.
    family_global = len(results)
    tail_fw = (1.0 - 0.95) / (2.0 * family_global)
    conf_fw = 1.0 - tail_fw
    for r in results:
        r["err_upper_fw"] = cp_upper(r["bad"], r["reps"], conf_fw)
        r["err_lower_fw"] = cp_lower(r["bad"], r["reps"], conf_fw)

    rungs = 11

    def ladder(conf_of_panel):
        cert, cens = [], []
        for m in ms:
            for h in hs:
                for dec in ("safe", "identification"):
                    conf = conf_of_panel(m)
                    worst = {}
                    best = {}
                    for r in results:
                        if r["m"] == m and r["h"] == h and r["decoder"] == dec:
                            worst.setdefault(r["N_per_query"], []).append(
                                cp_upper(r["bad"], r["reps"], conf))
                            best.setdefault(r["N_per_query"], []).append(
                                cp_lower(r["bad"], r["reps"], conf))
                    hit = None
                    for N in sorted(worst):
                        if max(worst[N]) <= delta_target:
                            hit = N
                            break
                    # The lower side, which a ladder does NOT give for free, and which an
                    # earlier version of this code got wrong in two ways.
                    #
                    # (1) A rung that merely failed to certify is not a rung proved too
                    #     small; only a CP LOWER bound above delta proves failure.
                    # (2) A fixed decoder's true error is NOT known to be monotone in N, so
                    #     ONE proved-failing rung below `hit` excludes nothing about the
                    #     rungs between them.  Taking the largest such rung -- as the first
                    #     repair did -- is invalid.  What is excluded is a CONTIGUOUS
                    #     PREFIX of the tested grid, all of whose rungs are proved to fail.
                    #     The first rung after that prefix is then a lower bound on the
                    #     first SUCCESSFUL TESTED budget.  It bounds neither the untested
                    #     integers between rungs nor the minimum over all decoders.
                    ns = sorted(best)
                    failed_prefix = []
                    for N in ns:
                        if max(best[N]) > delta_target:
                            failed_prefix.append(N)
                        else:
                            break
                    grid_low = (ns[len(failed_prefix)]
                                if len(failed_prefix) < len(ns) else None)
                    row = {"m": m, "h": h, "decoder": dec, "certified_N": hit,
                           "failed_prefix": failed_prefix,
                           "grid_min_lower_inclusive": grid_low,
                           "bracketed": bool(hit is not None and failed_prefix),
                           "total_budget": None if hit is None else
                           (hit if dec == "safe" else (m - 1) * hit)}
                    (cert if hit is not None else cens).append(row)
        return cert, cens

    cert_raw, cens_raw = ladder(lambda m: 0.95)
    cert_panel, cens_panel = ladder(lambda m: 1.0 - 0.05 / (rungs * m))
    certified, censored = ladder(lambda m: conf_fw)

    moved = [(c["m"], c["h"], c["decoder"], r0["certified_N"], c["certified_N"])
             for c in certified
             for r0 in cert_raw
             if (r0["m"], r0["h"], r0["decoder"]) == (c["m"], c["h"], c["decoder"])
             and r0["certified_N"] != c["certified_N"]]
    ok_fw = (all(r["err_upper_fw"] >= r["err_upper95"] for r in results)
             and len(certified) + len(censored) == len(cert_raw) + len(cens_raw))
    check("the reported budget of every panel is the first rung of a ladder that clears the"
          " target, so the intervals are corrected for that selection: every Clopper-Pearson"
          " bound in the run is taken at level 1 - 0.05/J with J the number of intervals in"
          " the run, and the corrected bound is never tighter than the uncorrected one",
          ok_fw,
          f"J={family_global}, per-interval level {conf_fw:.6f};"
          f" certified cells: {len(cert_raw)} uncorrected, {len(cert_panel)} panel-corrected,"
          f" {len(certified)} family-corrected; budgets that moved under the correction:"
          f" {moved if moved else 'none'}")

    # ---- self-check 3b: the measured identification-rate curve ---------------------
    #
    # WHAT A ONE-SIDED LADDER DOES AND DOES NOT GIVE.
    #
    # A certified rung `N` is an UPPER bound on the minimal budget: the decoder provably
    # reaches error <= delta there.  It is NOT a two-sided localisation.  The earlier
    # reading here -- "the grid has ratio 2, so the budget is known to within a factor of
    # two, hence the slope is known to within a computable tolerance" -- rests on
    # `N* > N/2`, i.e. on the previous rung being TOO SMALL.  But the previous rung merely
    # FAILED TO CERTIFY: its CP upper bound came out above delta.  Failure to certify is
    # not evidence that the true error exceeds delta, so `N* > N/2` does not follow and
    # neither does any slope tolerance derived from it.
    #
    # A budget is localised only when BOTH sides certify:
    #     upper: worst-world CP upper at N_high <= delta
    #     lower: worst-world CP LOWER at N_low  >  delta
    # Only `bracketed` points carry a factor-(N_high/N_low) localisation, and only those
    # are used for a slope.  Points certified on one side are reported as upper bounds and
    # are NOT called sample complexity.
    rate_rows = []
    for m in ms:
        pts = [(r["h"], r["certified_N"], r["grid_min_lower_inclusive"]) for r in certified
               if r["m"] == m and r["decoder"] == "identification" and r["bracketed"]]
        pts = sorted(p for p in pts if p[1] is not None and p[2] is not None)
        if len(pts) >= 2:
            xs = [math.log(h) for h, _, _ in pts]
            ys = [math.log(N) for _, N, _ in pts]
            # The localisation width is the ACTUAL bracket at each point, log(N_hi/N_lo),
            # not a constant log 2: the ruled-out rung need not be the one immediately
            # below, so the widths differ between points and are used as they are.
            widths = [math.log(N / Nlo) for _, N, Nlo in pts]
            n = len(xs)
            mx, my = sum(xs) / n, sum(ys) / n
            den = sum((x - mx) ** 2 for x in xs)
            slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / den if den else None
            grid_tol = (sum(abs(x - mx) * w for x, w in zip(xs, widths)) / den
                        if den else None)
            predicted = -2.0 * (m - 1)
            # The substantive claim is that identification is dearer than the safe
            # decision, whose exponent is -2.  Whether the grid can see that separation at
            # all is recorded rather than assumed.
            separates = (slope is not None and grid_tol is not None
                         and abs(slope - (-2.0)) > grid_tol)
            rate_rows.append({"m": m,
                              "points_h_Nhigh_Nlow": pts,
                              "measured_slope": slope,
                              "predicted_slope": predicted,
                              "bracket_log_widths": widths,
                              "grid_slope_tolerance": grid_tol,
                              "separates_from_safe_exponent": bool(separates)})
    n_bracketed = sum(1 for r in certified if r["bracketed"])
    n_upper_only = sum(1 for r in certified if not r["bracketed"])
    ok_rate = all(
        r["measured_slope"] is not None and r["grid_slope_tolerance"] is not None and
        abs(r["measured_slope"] - r["predicted_slope"]) <= r["grid_slope_tolerance"]
        for r in rate_rows)
    check("no rate slope is read off budgets that are certified on ONE side only.  A rung"
          " that failed to certify is not a rung proved too small, so it cannot bound the"
          " minimal budget from below and cannot justify a factor-2 localisation.  A slope"
          " is reported only where both a CP upper bound at the high rung and a CP LOWER"
          " bound at a lower rung bracket the budget; where no such bracket exists the"
          " budget is reported as an upper bound and NOT as sample complexity",
          ok_rate,
          f"{n_bracketed} two-sided bracketed, {n_upper_only} upper-bound-only; "
          + ("; ".join(f"m={r['m']}: points {r['points_h_Nhigh_Nlow']},"
                       f" slope {r['measured_slope']:.2f}"
                       f" vs predicted {r['predicted_slope']:.1f}, grid tolerance"
                       f" +/-{r['grid_slope_tolerance']:.2f},"
                       f" separates from -2: {r['separates_from_safe_exponent']}"
                       for r in rate_rows)
             or "no slope claimed: no m has two or more BRACKETED identification budgets"))

    # ---- self-check 4: safe is cheaper than identification, and by a growing factor --
    ok_sep, sep_rows = True, []
    for m in ms:
        for h in hs:
            cs = next((r for r in certified if r["m"] == m and r["h"] == h
                       and r["decoder"] == "safe"), None)
            ci = next((r for r in certified if r["m"] == m and r["h"] == h
                       and r["decoder"] == "identification"), None)
            if cs and ci:
                ok_sep &= cs["total_budget"] <= ci["total_budget"]
                sep_rows.append({"m": m, "h": h, "safe": cs["total_budget"],
                                 "identification": ci["total_budget"],
                                 "ratio": ci["total_budget"] / cs["total_budget"]})
    check("where both decoders certify, the safe budget never exceeds the identification"
          " budget -- the decision is not harder than naming the world", ok_sep,
          f"{len(sep_rows)} comparable cells" if sep_rows else "no comparable cell")

    # ---- self-check 5: the zero-query floor is respected, per TASK ------------------
    #
    # The two decoders do not share a floor.  Uniform guessing is unsafe with probability
    # 1/m but names the world correctly with probability 1/m, so its identification error
    # is 1 - 1/m.  Recording 1/m on an identification cell would import the safe decision's
    # floor into a task that does not have it.
    ok_floor = all(
        r["zero_query_floor"] == (1.0 / r["m"] if r["decoder"] == "safe"
                                  else 1.0 - 1.0 / r["m"])
        for r in results)
    # The target must sit strictly under the floor of the task it is used on, otherwise the
    # certified budget for that task is not evidence of anything.
    ok_target = all(delta_target < r["zero_query_floor"] for r in results)
    check("the zero-query floor is recorded PER TASK -- 1/m for the safe decision, 1 - 1/m"
          " for identification -- and the target delta sits strictly below both, so neither"
          " certified budget is reporting an error a query-free guess already achieves",
          ok_floor and ok_target,
          "safe floors "
          f"{sorted(set(round(r['zero_query_floor'], 4) for r in results if r['decoder'] == 'safe'))},"
          " identification floors "
          f"{sorted(set(round(r['zero_query_floor'], 4) for r in results if r['decoder'] != 'safe'))},"
          f" target {delta_target}")

    # ---- self-check 6: the statistic is bounded ------------------------------------
    probe = sample_stat(rng, 3, 1, 0.3, 4000, True)
    ok_bounded = bool(np.all(np.abs(probe) <= 1.0))
    check("the statistic is bounded by one whatever the query order, which is what avoids"
          " the variance blow-up of the Y^{r+1} moment estimator", ok_bounded,
          f"max |cos(t0 Y)| = {float(np.abs(probe).max()):.6f}, sample variance "
          f"{float(probe.var()):.4f}")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {"source_sha256": hashlib.sha256(
               pathlib.Path("scripts/EXP_paperB_decoder.py").read_bytes()).hexdigest(),
           "sigma": SIGMA, "t0": T0, "reps": reps, "delta_target": delta_target,
           "gap_rows": gap_rows, "order_rows": order_rows, "lower_bound_rows": lower_rows,
           "results": results, "certified": certified, "censored": censored,
           "confidence_family_size": family_global,
           "per_interval_confidence": conf_fw,
           "certified_uncorrected": cert_raw, "censored_uncorrected": cens_raw,
           "certified_panel_corrected": cert_panel, "censored_panel_corrected": cens_panel,
           "budgets_moved_by_correction": moved,
           "identification_rate_curve": rate_rows,
           "separation": sep_rows,
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperB_decoder.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
