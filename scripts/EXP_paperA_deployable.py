#!/usr/bin/env python3
"""Paper A, figure A-F2 on DEPLOYABLE policies: one two-answer stopping certificate for every rule.

Deviation P-1 of the 2026-09-24 audit: `EXP_paperA_mechanism.py` stops only when the certificate
for answer A clears the threshold, so the true answer entered the stop and its rules are an
allocation diagnostic, not learners.  This producer removes that: every rule uses the SAME
certificate for EACH answer (the covers of `EXP_paperA_swap.py`), stops at the first check where
the certificate of the answer its estimate currently retains clears the threshold, and returns
that answer.  It is run on the base world (answer A) and on the swapped world (answer B).

THE RULES (each is a tracking learner: warm start, forcing `min(1, 1/sqrt t)` toward uniform,
first argmax of `W - N`; they differ only in the oracle, which sees ONLY the estimate):

* `surrogate_at_estimate` -- re-solves the FROZEN SURROGATE at the estimate every round: freeze
  the estimate's extremum cells (arm A's max and min, arm B's max and min) and put
  `w_e proportional to sigma_e` on those four cells.  That is the surrogate's exact optimum at
  the estimate (checked below against random designs); when the estimate is within 1/16 of the
  truth it is the uniform-anchor design `wUnifC` of Lean (`surD_middle_zero`).  This is the
  learner of `surrogate_learner_cost` (`LeanPaperA6EstCostV1`), up to the forcing offset and
  the stop.
* `geometry` -- the TRUE game at the estimate: a Nelder-Mead ascent of the certificate of the
  answer the estimate retains, refreshed every `REFRESH_EVERY` rounds (recorded).
* `uniform` -- the uniform design.

WHAT THE STOP IS.  The certificate is a valid LOWER bound on the generalised likelihood ratio of
the retained answer (union-of-polyhedra relaxation, each polyhedron bounded by its best
half-space), with the martingale weight `N^2/(a+N)` and the threshold
`log(1/alpha) + 1/2 sum log(1 + N/a)` of `Qstat` / `bthr`.  So a stop is certified, and the
answer is read off the data.  It is not the Lean stop `tauG` (which uses the exact infimum), and
alpha here is far above the `delta_0` of the Lean theorem: the panel is evidence about these
rules, not a test of `Omega(log^2)`.

SELF-CHECKS (refuse to report on failure):
* both certificates sit on the right sides at the true world (positive for the correct answer,
  zero for the wrong one);
* the surrogate oracle is an exact frozen optimum at random estimates (no random design beats
  it) and equals the anchor design whenever the estimate is within 1/16 of the truth;
* every run is accounted for exactly once as stopped or censored;
* the wrong-answer rate among stopped runs is within a binomial tail of alpha (`correctG`);
* THE THEOREM CHECK (`oCount_le_bad`, transcribed for the code's forcing): at the end of every
  run, every middle cell has `N_e <= 2 + bad_e + q(t)`, with `bad_e` the post-warm rounds at
  which the oracle weighted `e` and `q(t) = sum_{n <= s < t} min(1, 1/sqrt s)/n`.

Output (new file; refuses to overwrite): research/unified_20260919/paperA_deployable.json
Smoke: `--smoke --out DIR`.
"""

import hashlib
import json
import math
import pathlib
import sys
import time

import numpy as np
from scipy.optimize import minimize

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "research/unified_20260919/paperA_deployable.json"
CHECKS = []
REFRESH_EVERY = 500


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""), flush=True)
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


def poly_value(P, h, mu):
    """Max over the polyhedron's rows of the exact half-space minimum (vectorised)."""
    t = -(P @ mu)
    nz = np.abs(P) > 0
    bad = ((h <= 0.0)[None, :] & nz).any(axis=1)
    hh = np.where(h > 0.0, h, np.inf)
    denom = np.sum(np.where(nz, P ** 2 / hh[None, :], 0.0), axis=1)
    vals = np.where((t > 0.0) & (~bad) & (denom > 0.0), t * t / (2.0 * np.maximum(denom, 1e-300)),
                    0.0)
    return float(vals.max())


def value_at(w, var, mu, HS):
    h = w / var
    return min(poly_value(P, h, mu) for P in HS)


def answer_at(mu, bcells):
    rA = abs(mu[1] - mu[0])
    rB = float(mu[bcells].max() - mu[bcells].min())
    return "A" if rB <= rA else "B"


def frozen_cells(mu, bcells):
    a_hi, a_lo = (1, 0) if mu[1] >= mu[0] else (0, 1)
    b_hi = int(bcells[int(np.argmax(mu[bcells]))])
    b_lo = int(bcells[int(np.argmin(mu[bcells]))])
    return [a_hi, a_lo, b_hi, b_lo]


def w_surrogate_at(mu, var, bcells):
    """The frozen surrogate's exact optimum at the estimate: `w_e ~ sigma_e` on its four frozen
    extremum cells (minimise `sum_e sigma_e^2 / w_e` over the simplex on those cells)."""
    w = np.zeros(len(mu))
    cells = frozen_cells(mu, bcells)
    sd = np.sqrt(var[cells])
    w[cells] = sd / sd.sum()
    return w


def frozen_value_at(w, var, mu, bcells):
    """Closed form of the frozen game at `mu`: one linear contrast on the four frozen cells,
    margin `g = |range_A - range_B|`, value `g^2 / (2 sum_e sigma_e^2 / w_e)` (0 if some frozen
    cell has zero weight)."""
    cells = frozen_cells(mu, bcells)
    g = abs(abs(mu[1] - mu[0]) - float(mu[bcells].max() - mu[bcells].min()))
    if np.any(w[cells] <= 0.0):
        return 0.0
    return g * g / (2.0 * float(np.sum(var[cells] / w[cells])))


def w_uniform(n):
    return np.full(n, 1.0 / n)


def w_geometry(w0, var, mu, HS, iters=40):
    n = len(var)

    def neg(z):
        w = np.exp(z - z.max())
        w = w / w.sum()
        return -value_at(w, var, mu, HS)

    z0 = np.log(np.maximum(w0, 1e-12))
    res = minimize(neg, z0, method="Nelder-Mead",
                   options={"maxiter": iters * n, "fatol": 1e-12, "xatol": 1e-9})
    w = np.exp(res.x - res.x.max())
    return w / w.sum()


def forcing_quota(t, n):
    if t <= n:
        return 0.0
    s = np.arange(n, t, dtype=float)
    return float(np.sum(np.minimum(1.0, 1.0 / np.sqrt(s))) / n)


def run(rng, theta, var, bcells, HSA, HSB, rule, alpha, budget, check_every, a_reg=1.0):
    n = len(theta)
    N = np.zeros(n)
    S = np.zeros(n)
    for e in range(n):
        S[e] += theta[e] + math.sqrt(var[e]) * rng.normal()
        N[e] += 1.0
    t = n
    W = np.zeros(n)
    bad_w = np.zeros(n)          # post-warm rounds at which the oracle weighted each cell
    bad_est = 0                  # post-warm rounds with some estimate off by 1/16 or more
    geo = {"key": None, "w": None}
    while t < budget:
        mu = S / N
        if rule == "surrogate_at_estimate":
            w = w_surrogate_at(mu, var, bcells)
        elif rule == "geometry":
            key = t // REFRESH_EVERY
            if geo["key"] != key:
                HS = HSA if answer_at(mu, bcells) == "A" else HSB
                geo["w"] = w_geometry(var / var.sum(), var, mu, HS)
                geo["key"] = key
            w = geo["w"]
        else:
            w = w_uniform(n)
        bad_w += (w > 0.0)
        bad_est += int(np.any(np.abs(mu - theta) >= 1.0 / 16.0))
        rho = min(1.0, 1.0 / math.sqrt(t))
        wt = (1.0 - rho) * w + rho / n
        W += wt
        e_t = int(np.argmax(W - N))
        S[e_t] += theta[e_t] + math.sqrt(var[e_t]) * rng.normal()
        N[e_t] += 1.0
        t += 1
        if t % check_every == 0:
            mu = S / N
            ans = answer_at(mu, bcells)
            HS = HSA if ans == "A" else HSB
            lo = value_at(N ** 2 / (a_reg + N), var, mu, HS)
            thr = math.log(1.0 / alpha) + 0.5 * float(np.sum(np.log1p(N / a_reg)))
            if lo > thr:
                return t, ans, N, False, bad_w, bad_est
    mu = S / N
    return budget, answer_at(mu, bcells), N, True, bad_w, bad_est


def binom_tail(k, n, p):
    """P(Bin(n, p) >= k)."""
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
    M = 1.0
    rs = [1] if smoke else [1, 2, 4, 8]
    alpha = 0.05
    budget = 3000 if smoke else 60000
    n_runs = 3 if smoke else 24
    check_every = 50
    rules = ["surrogate_at_estimate", "geometry", "uniform"]
    t0 = time.time()
    print("=" * 78, flush=True)
    print("Paper A: deployable policies under ONE two-answer certificate", flush=True)
    print("=" * 78, flush=True)

    # --- certificates on the right sides at the truth ----------------------------
    ok_sides, sides = True, []
    for r in rs:
        HSA, HSB = half_spaces_A(r), half_spaces_B(r)
        for swapped in (False, True):
            theta, var, bcells = build(r, M, swapped)
            w = w_uniform(len(theta))
            correct = answer_at(theta, bcells)
            v_ok = value_at(w, var, theta, HSA if correct == "A" else HSB)
            v_bad = value_at(w, var, theta, HSB if correct == "A" else HSA)
            ok_sides &= (v_ok > 0.0) and (v_bad == 0.0)
            sides.append({"r": r, "swapped": swapped, "correct": correct,
                          "cert_correct": v_ok, "cert_wrong": v_bad})
    check("both certificates sit on the right sides at the true world (positive for the correct"
          " answer, zero for the wrong one)", ok_sides)

    # --- the surrogate oracle is the surrogate's exact optimum at the estimate ------
    rng0 = np.random.default_rng(1)
    ok_opt, worst_gap, ok_anchor = True, 0.0, True
    for r in rs:
        for swapped in (False, True):
            theta, var, bcells = build(r, M, swapped)
            n = len(theta)
            for _ in range(50):
                mu = theta + rng0.normal(scale=0.3, size=n)
                w_s = w_surrogate_at(mu, var, bcells)
                v_s = frozen_value_at(w_s, var, mu, bcells)
                for _ in range(40):
                    w_r = rng0.dirichlet(np.ones(n))
                    gap = frozen_value_at(w_r, var, mu, bcells) - v_s
                    worst_gap = max(worst_gap, gap)
                    ok_opt &= gap <= 1e-12
                mu_c = theta + rng0.uniform(-1 / 16, 1 / 16, size=n) * 0.999
                w_c = w_surrogate_at(mu_c, var, bcells)
                anchors = np.zeros(n)
                anchors[:4] = 0.25
                ok_anchor &= np.allclose(w_c, anchors)
    check("the surrogate oracle is the frozen surrogate's exact optimum at the estimate: no"
          " random design beats it", ok_opt, f"worst gap {worst_gap:.1e} over 50 estimates x 40 designs")
    check("within 1/16 of the truth the surrogate oracle IS the uniform-anchor design (Lean"
          " `surD_middle_zero`, M = 1)", ok_anchor)

    # --- the panel ------------------------------------------------------------------
    rows = []
    ok_count, ok_thm, thm_slack = True, True, math.inf
    for r in rs:
        HSA, HSB = half_spaces_A(r), half_spaces_B(r)
        for swapped in (False, True):
            theta, var, bcells = build(r, M, swapped)
            n = len(theta)
            correct = answer_at(theta, bcells)
            for ri, rule in enumerate(rules):
                taus, ans_l, cens_l, share_l, bad_l = [], [], [], [], []
                for ix in range(n_runs):
                    rng = np.random.default_rng([20260924, r, int(swapped), ri, ix])
                    t, ans, N, c, bad_w, bad_est = run(rng, theta, var, bcells, HSA, HSB, rule,
                                                       alpha, budget, check_every)
                    q = forcing_quota(int(N.sum()), n)
                    for e in range(4, n):
                        slack = 2.0 + bad_w[e] + q - N[e]
                        thm_slack = min(thm_slack, slack)
                        ok_thm &= slack >= -1e-9
                    taus.append(int(t))
                    ans_l.append(ans)
                    cens_l.append(bool(c))
                    share_l.append(float(N[4:].sum() / N.sum()))
                    bad_l.append(int(bad_est))
                stopped = [i for i in range(n_runs) if not cens_l[i]]
                row = {"r": r, "swapped": swapped, "correct_answer": correct, "rule": rule,
                       "tau_per_run": taus, "answer_per_run": ans_l, "censored_per_run": cens_l,
                       "middle_share_per_run": share_l, "bad_estimate_rounds_per_run": bad_l,
                       "stopped": len(stopped),
                       "stopped_wrong": sum(1 for i in stopped if ans_l[i] != correct),
                       "censored": sum(cens_l),
                       "restricted_mean_tau": float(np.mean(taus)),
                       "budget": budget, "alpha": alpha}
                ok_count &= row["stopped"] + row["censored"] == n_runs
                rows.append(row)
                print(f"  r={r} swapped={str(swapped):5s} {rule:22s} E[min(tau,B)]="
                      f"{row['restricted_mean_tau']:8.0f} stopped={row['stopped']:2d}"
                      f" wrong={row['stopped_wrong']} censored={row['censored']:2d}"
                      f" share={np.mean(share_l):.4f} bad_est={np.mean(bad_l):7.1f}"
                      f"   [{time.time() - t0:6.0f}s]", flush=True)
    check("every run is accounted for exactly once as stopped or censored", ok_count)
    n_stop = sum(x["stopped"] for x in rows)
    n_wrong = sum(x["stopped_wrong"] for x in rows)
    tail = binom_tail(n_wrong, n_stop, alpha) if n_stop else 1.0
    check("the wrong-answer rate among stopped runs is consistent with alpha (`correctG`):"
          " P(Bin(stopped, alpha) >= wrong) >= 1e-3", tail >= 1e-3,
          f"{n_wrong} wrong of {n_stop} stopped, tail {tail:.3f}")
    check("THEOREM (`oCount_le_bad`, transcribed for the code's forcing): every middle cell of"
          " every run has N_e <= 2 + bad_e + q(t)", ok_thm, f"min slack {thm_slack:.2f}")

    out = {"producer": "scripts/EXP_paperA_deployable.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "M": M, "r_values": rs, "alpha": alpha, "budget": budget, "n_runs": n_runs,
           "check_every": check_every, "geometry_refresh_every": REFRESH_EVERY,
           "rules": rules, "certificate_sides_at_truth": sides, "rows": rows,
           "scope": "deployable policies (oracle sees only the estimate) under one two-answer"
                    " lower certificate; alpha far above delta_0 of the Lean theorem; not the"
                    " Lean stop tauG",
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
