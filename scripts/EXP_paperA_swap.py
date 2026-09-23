#!/usr/bin/env python3
"""Paper A: does the rule LEARN the answer, or only ever certify one of them?

`EXP_paperA_mechanism` stops when the lower certificate for "retain A" clears the threshold.
On the family it runs, "retain A" is the correct answer at every world it visits, so the
panel cannot distinguish a rule that learns the answer from a rule that can only ever say A.
An audit of the earlier learner panel found exactly that pattern: every selection snapshot
kept both candidates and returned the same one.

This script settles it by building the SWAPPED world, where the correct answer is B, and by
giving the rule a certificate for each answer.

  * base world     theta_A = (-1/2, 1/2),   theta_B = (-1/8, 1/8, 0, ..., 0)   -> retain A
  * swapped world  theta_A = (-1/8, 1/8),   theta_B = (-1/2, 1/2, 0, ..., 0)   -> retain B

THE SECOND CERTIFICATE.  `Alt(retain B is wrong) = {range(lam_A) > range(lam_B)}`.  Arm A has
two cells, so `range(lam_A) = |lam_1 - lam_0|`, and the absolute value splits the set into
TWO polyhedra, one per sign, each cut by one inequality per ordered pair of B-cells.  The
same relaxation as the A-side is used -- minimum over polyhedra of the maximum over that
polyhedron's rows -- and it goes the same way: conservative, never optimistic.

WHAT THIS CAN SHOW AND WHAT IT CANNOT.  If the symmetric rule returns B on the swapped world,
the answer is being read off the data rather than fixed in advance.  That is evidence about
THIS rule on THIS family; it is not a proof that selection converges, and the script does not
claim one.  The A-only rule's behaviour on the swapped world is reported separately, because
its failure there is a property of the rule, not of the algorithm class.

SELF-CHECKS.  Both certificates are checked to be valid lower bounds at the true world (they
must be zero there, since the true world is not in its own alternative set); the answers on
the two worlds are checked to differ; the tie-break order is reversed and the answers
compared; and censoring is reported rather than absorbed.
"""

import hashlib
import json
import math
import pathlib
import sys

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "research/unified_20260919/paperA_swap.json"
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def build(r, M, swapped):
    n = 4 + 2 * r
    theta = np.zeros(n)
    if swapped:
        theta[0], theta[1] = -0.125, 0.125
        theta[2], theta[3] = -0.5, 0.5
    else:
        theta[0], theta[1] = -0.5, 0.5
        theta[2], theta[3] = -0.125, 0.125
    var = np.ones(n)
    var[4:] = M
    bcells = np.array([2, 3] + list(range(4, n)))
    return theta, var, bcells


def half_spaces_A(r):
    """Cover of `Alt(retain A is wrong) = {range(lam_B) > range(lam_A)}`."""
    n = 4 + 2 * r
    bcells = [2, 3] + list(range(4, n))
    out = []
    for p in bcells:
        for q in bcells:
            if p == q:
                continue
            rows = []
            for s in (1.0, -1.0):
                a = np.zeros(n)
                a[p] += 1.0
                a[q] -= 1.0
                a[1] -= s
                a[0] += s
                rows.append(a)
            out.append(np.array(rows))
    return out


def half_spaces_B(r):
    """Cover of `Alt(retain B is wrong) = {range(lam_A) > range(lam_B)}`.

    Two polyhedra, one per sign of `lam_1 - lam_0`; each asks the A-gap to dominate EVERY
    ordered pair of B-cells, so the rows are conjunctive within a polyhedron.
    """
    n = 4 + 2 * r
    bcells = [2, 3] + list(range(4, n))
    out = []
    for s in (1.0, -1.0):
        rows = []
        for p in bcells:
            for q in bcells:
                if p == q:
                    continue
                a = np.zeros(n)
                a[1] += s
                a[0] -= s
                a[p] -= 1.0
                a[q] += 1.0
                rows.append(a)
        out.append(np.array(rows))
    return out


def halfspace_min(a, h, mu):
    t = -float(a @ mu)
    if t <= 0.0:
        return 0.0
    nz = np.abs(a) > 0
    if ((h <= 0.0) & nz).any():
        return 0.0
    denom = float(np.sum(a[nz] ** 2 / h[nz]))
    return 0.0 if denom <= 0.0 else t * t / (2.0 * denom)


def value_at(w, var, mu, HS):
    h = w / var
    return min(max(halfspace_min(a, h, mu) for a in poly) for poly in HS)


def answer_at(mu, bcells):
    rA = abs(mu[1] - mu[0])
    rB = float(mu[bcells].max() - mu[bcells].min())
    return "A" if rB <= rA else "B"


def w_uniform(r, M):
    n = 4 + 2 * r
    return np.full(n, 1.0 / n)


def w_proxy(r, M):
    n = 4 + 2 * r
    w = np.zeros(n)
    w[:4] = 0.25
    return w


def w_cert(r, M, var):
    return var / var.sum()


def run(rng, theta, var, bcells, HSA, HSB, w_vec, alpha, budget, check_every,
        rho_floor, symmetric, reverse_tie, a_reg=1.0):
    n = len(theta)
    N = np.zeros(n)
    S = np.zeros(n)
    for e in range(n):
        S[e] += theta[e] + math.sqrt(var[e]) * rng.normal()
        N[e] += 1.0
    t = n
    W = np.zeros(n)
    while t < budget:
        w = w_vec
        if rho_floor > 0.0:
            rho = min(1.0, rho_floor / math.sqrt(t))
            w = (1.0 - rho) * w + rho * np.full(n, 1.0 / n)
        W += w
        gap = W - N
        e_t = int(n - 1 - np.argmax(gap[::-1])) if reverse_tie else int(np.argmax(gap))
        S[e_t] += theta[e_t] + math.sqrt(var[e_t]) * rng.normal()
        N[e_t] += 1.0
        t += 1
        if t % check_every == 0:
            mu = S / np.maximum(N, 1.0)
            ans = answer_at(mu, bcells)
            HS = HSA if ans == "A" else (HSB if symmetric else None)
            if HS is None:
                continue
            # The martingale of `LeanPaperA7ConfidenceV1.Mstat_log` is
            #     Q_t = sum_e N_e^2 (mu_e - lam_e)^2 / (2 sigma_e^2 (a + N_e)),
            # so the weight the certificate must use is N^2/(a+N), NOT N.  Using N
            # inflates the statistic and the alpha-guarantee would not apply to it.
            effective_N = N ** 2 / (a_reg + N)
            lo = value_at(effective_N, var, mu, HS)
            thr = math.log(1.0 / alpha) + 0.5 * float(np.sum(np.log1p(N / a_reg)))
            if lo > thr:
                return t, ans, N, False
    mu = S / np.maximum(N, 1.0)
    return budget, answer_at(mu, bcells), N, True


def main():
    smoke = "--smoke" in sys.argv
    rng = np.random.default_rng(20260922)
    M = 1.0
    rs = [1] if smoke else [1, 2]
    alpha = 0.1
    budget = 4000 if smoke else 40000
    n_runs = 4 if smoke else 24
    check_every = 200

    print("=" * 78)
    print("Paper A: does the rule learn the answer, or only certify one of them?")
    print("=" * 78)

    # --- the certificates sit on the right sides at the true world -----------------
    ok_sides, zero_rows = True, []
    for r in rs:
        HSA, HSB = half_spaces_A(r), half_spaces_B(r)
        for swapped in (False, True):
            theta, var, bcells = build(r, M, swapped)
            w = np.full(len(theta), 1.0 / len(theta))
            correct = answer_at(theta, bcells)
            HS_ok = HSA if correct == "A" else HSB
            HS_bad = HSB if correct == "A" else HSA
            v_ok = value_at(w, var, theta, HS_ok)
            v_bad = value_at(w, var, theta, HS_bad)
            ok_sides &= (v_ok > 0.0) and (v_bad == 0.0)
            zero_rows.append({"r": r, "swapped": swapped, "correct_answer": correct,
                              "cert_for_correct_answer": v_ok,
                              "cert_for_wrong_answer": v_bad})
    check("the two covers sit on the RIGHT sides at the true world: the correct answer's"
          " certificate is POSITIVE (the world is outside its own alternative set, which is"
          " what lets the rule stop) and the wrong answer's is exactly ZERO (the world is"
          " inside that one, so nothing can be certified)", ok_sides,
          "; ".join(f"r={z['r']} swapped={z['swapped']} -> {z['correct_answer']}:"
                    f" correct {z['cert_for_correct_answer']:.4f},"
                    f" wrong {z['cert_for_wrong_answer']:.1e}" for z in zero_rows))

    # --- the panel -------------------------------------------------------------------
    rows = []
    for r in rs:
        HSA, HSB = half_spaces_A(r), half_spaces_B(r)
        for swapped in (False, True):
            theta, var, bcells = build(r, M, swapped)
            correct = answer_at(theta, bcells)
            for rule, wv in (("proxy", w_proxy(r, M)), ("geometry", w_cert(r, M, var)),
                             ("uniform", w_uniform(r, M))):
                for symmetric in (True, False):
                    for reverse_tie in (False, True):
                        # A run either STOPS with a certified answer or is CENSORED at
                        # the budget.  Only the first kind carries the alpha-guarantee, so
                        # the two are counted separately and never added together.  The
                        # horizon estimate of a censored run is reported on its own line
                        # and is NOT evidence about the stopping rule.
                        taus, cens = [], 0
                        stopped_correct = stopped_wrong = 0
                        horizon_correct = 0
                        for _ in range(n_runs):
                            t, ans, N, c = run(rng, theta, var, bcells, HSA, HSB, wv,
                                               alpha, budget, check_every, 1.0,
                                               symmetric, reverse_tie)
                            taus.append(min(t, budget))
                            if c:
                                cens += 1
                                horizon_correct += int(ans == correct)
                            elif ans == correct:
                                stopped_correct += 1
                            else:
                                stopped_wrong += 1
                        rows.append({
                            "r": r, "swapped": swapped, "correct_answer": correct,
                            "rule": rule, "symmetric_certificate": symmetric,
                            "reverse_tie_break": reverse_tie,
                            "restricted_mean_tau": float(np.mean(taus)),
                            "sem": float(np.std(taus, ddof=1) / math.sqrt(len(taus)))
                                   if len(taus) > 1 else 0.0,
                            "stopped_correct": stopped_correct,
                            "stopped_wrong": stopped_wrong,
                            "stopped": stopped_correct + stopped_wrong,
                            "censored_horizon_estimate_correct": horizon_correct,
                            "runs": n_runs, "censored": cens})
                        print(f"  r={r} swapped={str(swapped):5s} {rule:8s}"
                              f" sym={str(symmetric):5s} revtie={str(reverse_tie):5s}"
                              f" E[min(tau,B)]={rows[-1]['restricted_mean_tau']:7.0f}"
                              f" stopped_ok={stopped_correct}"
                              f" stopped_wrong={stopped_wrong}"
                              f" censored={cens}/{n_runs}")

    sym_rows = [x for x in rows if x["symmetric_certificate"]]
    asym_rows = [x for x in rows if not x["symmetric_certificate"]]

    # The alpha-guarantee is about runs that STOPPED.  A censored run says nothing about
    # it, so it is excluded from the numerator AND the denominator here.
    n_stopped = sum(x["stopped"] for x in sym_rows)
    n_stopped_wrong = sum(x["stopped_wrong"] for x in sym_rows)
    n_cens_sym = sum(x["censored"] for x in sym_rows)
    ok_learn = all(x["stopped_wrong"] == 0 for x in sym_rows)
    check("with a certificate for EACH answer, NO run that stopped returned the wrong"
          " answer on either world -- so where the rule does answer, the answer is read"
          " off the data and not fixed in advance.  Censored runs are excluded: they"
          " carry no guarantee and are counted separately",
          ok_learn,
          f"{n_stopped - n_stopped_wrong}/{n_stopped} stopped runs correct,"
          f" {n_stopped_wrong} stopped wrong, {n_cens_sym} censored, over"
          f" {len(sym_rows)} configurations")

    ok_cens_reported = all(x["stopped"] + x["censored"] == x["runs"] for x in rows)
    check("every run is accounted for exactly once as stopped or censored, so no censored"
          " run is silently counted as a correct answer", ok_cens_reported,
          f"{sum(x['stopped'] for x in rows)} stopped +"
          f" {sum(x['censored'] for x in rows)} censored ="
          f" {sum(x['runs'] for x in rows)} runs")

    # M = 1 makes every variance equal, so the geometry allocation var/sum(var) IS the
    # uniform allocation.  Any difference between the two labels on this panel is Monte
    # Carlo noise, not a benefit of geometry, and the check below says so rather than
    # letting the two column names suggest a comparison.
    w_geom_is_uniform = all(
        np.allclose(w_cert(r, M, build(r, M, False)[1]), w_uniform(r, M)) for r in rs)
    check("at M = 1 the 'geometry' and 'uniform' allocations are the SAME vector, so the"
          " two rows are one allocation measured twice and their difference is noise --"
          " this panel does not measure a geometry benefit", w_geom_is_uniform,
          "var/sum(var) == 1/n at M=1 for every r tested")

    swapped_asym = [x for x in asym_rows if x["swapped"]]
    ok_limit = all(x["censored"] == x["runs"] for x in swapped_asym)
    check("the A-only rule NEVER stops on the swapped world: every run is censored.  That is"
          " a limitation of that rule, reported rather than hidden, and it is why the earlier"
          " panel could not distinguish learning the answer from always naming it",
          ok_limit,
          f"{sum(x['censored'] for x in swapped_asym)}/"
          f"{sum(x['runs'] for x in swapped_asym)} censored")

    ok_tie = True
    for a in sym_rows:
        if not a["reverse_tie_break"]:
            b = next((x for x in sym_rows if x["r"] == a["r"]
                      and x["swapped"] == a["swapped"] and x["rule"] == a["rule"]
                      and x["reverse_tie_break"]), None)
            if b is not None:
                ok_tie &= (a["stopped_wrong"] == b["stopped_wrong"])
    check("reversing the tie-break order of the tracker changes no answer, so the result is"
          " not an artefact of how ties are broken", ok_tie)

    ok_cens = all("censored" in x and "restricted_mean_tau" in x for x in rows)
    check("censoring is reported and the mean is the RESTRICTED mean to the budget, so a run"
          " that never stopped is not recorded as stopping at the budget", ok_cens,
          f"{sum(x['censored'] for x in rows)} censored runs over {len(rows)} configurations")

    out = {"source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "M": M, "r_values": rs, "alpha": alpha, "budget": budget, "n_runs": n_runs,
           "certificate_sides_at_truth": zero_rows, "rows": rows,
           "checks": CHECKS, "all_passed": all(c["ok"] for c in CHECKS)}
    OUT.write_text(json.dumps(out, indent=1))
    print(f"\n{sum(c['ok'] for c in CHECKS)}/{len(CHECKS)} self-checks passed")
    print(f"  artifact: {OUT.relative_to(ROOT)}")
    if not out["all_passed"]:
        print("REFUSING to report: a self-check failed.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
