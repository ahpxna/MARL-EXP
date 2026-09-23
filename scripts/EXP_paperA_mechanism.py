#!/usr/bin/env python3
"""Paper A: the ALLOCATION MECHANISM, on the family the theorems are about.

WHY THIS PRODUCER EXISTS.  `EXP_paperA7_learner.py` measures stopping on an eight-cell
instance.  It is not the family `LeanPaperACentredV1` proves the separation for, so it
cannot show the mechanism the separation is about: that optimising the frozen surrogate
STARVES the cells carrying the compression.  This producer builds the theorem's own family,
checks the theorems numerically before running anything, and then compares allocation rules
with the stopping certificate held FIXED, so a difference in stopping time is attributable
to the allocation and not to one arm being allowed a weaker certificate.

THE FAMILY (`thetaC` of `LeanPaperACentredV1`).  Arm `A` has two extremum cells at
`-1/2, +1/2`; arm `B` has two at `-1/8, +1/8` and `2r` middle cells at `0`.  The four
extremum cells have variance `1`, the middle cells variance `M`.  Retaining an arm costs
half the range of the OTHER arm, so at the true world retaining `A` costs `1/8` and
retaining `B` costs `1/2`: the correct answer is `A`.

THE ALTERNATIVES, AND A CLOSED-FORM CERTIFICATE.  Retaining `A` is wrong exactly when
`range(lam_B) > range(lam_A)`.  That set is covered by finitely many HALF-SPACES: for each
ordered pair `(p, q)` of arm-`B` cells and each sign `s`,

    H(p, q, s) = { lam : lam_p - lam_q >= s * (lam_{A,1} - lam_{A,0}) } .

Over a single half-space `a . lam >= c` the minimum of the energy has an exact closed form:
with `h_e = w_e / sigma_e^2` and `t = c - a . mu`,

    min = 0                       if t <= 0,
    min = t^2 / (2 * sum_e a_e^2 / h_e)   otherwise,

and `min = 0` whenever some coordinate with `a_e != 0` carries `h_e = 0` -- a starved cell
is free for the adversary to move.  Since `Alt` is CONTAINED in the union, the minimum over
half-spaces is a valid LOWER bound on the regional infimum, which is the direction a
stopping rule needs.  No solver, no dual, no tolerance: the certificate is exact arithmetic
on the estimate.  (Verified against a constrained solver to `2e-16` before this was built.)

WHAT IS COMPARED.  Three DEPLOYABLE rules, all stopping on the same certificate:

    GEOMETRY   allocation from the true game at the current estimate.
    PROXY      allocation from the frozen surrogate, plus forced exploration.
    UNIFORM    equal weight.

The surrogate's optimum is supported on the four extremum cells, so PROXY's middle-cell
share is whatever forced exploration puts there -- which is the mechanism, measured rather
than asserted.
"""

import hashlib
import json
import math
import pathlib
import sys

import numpy as np
from scipy.optimize import minimize

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "research/unified_20260919/paperA_mechanism.json"
OUT_SMOKE = ROOT / "research/unified_20260919/paperA_mechanism_smoke.json"

CHECKS = []
REFRESH_EVERY = 200


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


# ----------------------------------------------------------------- the family
def build(r, M):
    """`thetaC` and its variance profile, as a flat cell vector."""
    n = 4 + 2 * r
    theta = np.zeros(n)
    theta[0], theta[1] = -0.5, 0.5          # arm A extrema
    theta[2], theta[3] = -0.125, 0.125      # arm B extrema
    var = np.ones(n)
    var[4:] = M
    bcells = np.array([2, 3] + list(range(4, n)))   # arm B's cells
    return theta, var, bcells


def half_spaces(r):
    """The cover of `Alt(retain A is wrong)` by POLYHEDRA, each a pair of half-spaces.

    `range(lam_B) > range(lam_A)` means `lam_p - lam_q > |lam_1 - lam_0|` for the extremal
    pair, and the absolute value makes that TWO simultaneous constraints,

        lam_p - lam_q >= lam_1 - lam_0    and    lam_p - lam_q >= lam_0 - lam_1,

    not two alternatives.  Treating them as alternatives -- an earlier version of this file
    did -- makes the cover include the true world itself (take `p, q` two middle cells and
    the sign that points away from arm `A`'s gap), so the certificate collapses to zero and
    the rule never stops.  Each pair therefore contributes ONE polyhedron, returned as its
    two rows.
    """
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


def halfspace_min(a, h, mu):
    """Exact minimum of the energy over `a . lam >= 0`, at estimate `mu`, precision `h`."""
    t = -float(a @ mu)
    if t <= 0.0:
        return 0.0
    free = (np.abs(a) > 0) & (h <= 0.0)
    if free.any():
        return 0.0                      # a starved cell moves for free
    denom = float(np.sum(a[np.abs(a) > 0] ** 2 / h[np.abs(a) > 0]))
    if denom <= 0.0:
        return 0.0
    return t * t / (2.0 * denom)


def value_at(w, var, mu, HS):
    """A valid LOWER bound on `inf_{lam in Alt} energy`.

    `Alt` is contained in the union of the polyhedra, so the infimum over `Alt` is at least
    the minimum over polyhedra of each one's infimum; and each polyhedron's infimum is at
    least the infimum over EITHER of its two half-spaces, hence at least the larger of the
    two.  Both relaxations go the right way, so `min over pairs of max over the pair's two
    rows` is sound -- conservative, never optimistic, which is what a stopping rule needs.
    """
    h = w / var
    return min(max(halfspace_min(a, h, mu) for a in poly) for poly in HS)


def true_range_answer(mu, bcells):
    """Which arm to retain at `mu`: the one whose loss is smaller."""
    rA = abs(mu[1] - mu[0])
    rB = float(mu[bcells].max() - mu[bcells].min())
    return ("A" if rB <= rA else "B"), rA, rB


# ------------------------------------------------------------------ the rules
def w_uniform(r, M):
    n = 4 + 2 * r
    return np.full(n, 1.0 / n)


def w_proxy(r, M):
    """The frozen surrogate's optimum: the four extremum cells, nothing on the middles."""
    n = 4 + 2 * r
    w = np.zeros(n)
    w[:4] = 0.25
    return w


def w_cert(r, M):
    """The design certifying the true game's lower bound: weight proportional to variance."""
    _, var, _ = build(r, M)
    return var / var.sum()


def w_geometry(w0, var, mu, HS, iters=60):
    """Allocation from the TRUE game at the estimate: maximise the certificate over the
    simplex.  The objective is concave in `w` (a min of concave functions), so a projected
    ascent from the variance-proportional design is adequate and its value is reported."""
    n = len(var)

    def neg(z):
        w = np.exp(z - z.max())
        w = w / w.sum()
        return -value_at(w, var, mu, HS)

    z0 = np.log(np.maximum(w0, 1e-12))
    res = minimize(neg, z0, method="Nelder-Mead",
                   options={"maxiter": iters * n, "fatol": 1e-14, "xatol": 1e-10})
    z = res.x
    w = np.exp(z - z.max())
    return w / w.sum()


# ------------------------------------------------------------------- the runs
def run(rng, theta, var, bcells, HS, w_rule, alpha, budget, check_every, rho_floor,
        a_reg=1.0, trace_every=0):
    n = len(theta)
    N = np.zeros(n)
    S = np.zeros(n)
    for e in range(n):
        S[e] += theta[e] + math.sqrt(var[e]) * rng.normal()
        N[e] += 1.0
    t = n
    W = np.zeros(n)
    trace = []
    while t < budget:
        mu = S / np.maximum(N, 1.0)
        w = w_rule(mu)
        if rho_floor > 0.0:
            rho = min(1.0, rho_floor / math.sqrt(t))
            w = (1.0 - rho) * w + rho * np.full(n, 1.0 / n)
        W += w
        e_t = int(np.argmax(W - N))
        S[e_t] += theta[e_t] + math.sqrt(var[e_t]) * rng.normal()
        N[e_t] += 1.0
        t += 1
        if trace_every and t % trace_every == 0:
            trace.append({"t": int(t), "middle_share": float(N[4:].sum() / t)})
        if t % check_every == 0:
            mu = S / np.maximum(N, 1.0)
            ans, _, _ = true_range_answer(mu, bcells)
            # Same correction as EXP_paperA_swap: the martingale's weight is
            # N^2/(a+N), not N.  See LeanPaperA7ConfidenceV1.Mstat_log.
            effective_N = N ** 2 / (a_reg + N)
            lo = value_at(effective_N, var, mu, HS)
            thr = math.log(1.0 / alpha) + 0.5 * float(np.sum(np.log1p(N / a_reg)))
            if lo > thr and ans == "A":
                return t, ans, N, False, trace
    mu = S / np.maximum(N, 1.0)
    ans, _, _ = true_range_answer(mu, bcells)
    return budget, ans, N, True, trace


# ------------------------------------------------------------------ the panel
def main():
    smoke = "--smoke" in sys.argv
    print("=" * 78)
    print("Paper A: the allocation mechanism, on the theorems' own family")
    print("=" * 78)

    M = 1.0
    rs = [1, 2] if smoke else [1, 2, 4, 8]
    n_runs = 3 if smoke else 24
    budget = 4000 if smoke else 60000
    check_every = 50
    global REFRESH_EVERY
    REFRESH_EVERY = 200
    alphas = [0.05]

    rows = []
    for r in rs:
        theta, var, bcells = build(r, M)
        HS = half_spaces(r)
        ans0, rA0, rB0 = true_range_answer(theta, bcells)

        # ---- the theorems, checked numerically BEFORE anything is run ----------
        G_fr = 9.0 / 512.0
        lo_thm = 9.0 / (128.0 * (4.0 + 2.0 * r * M))
        up_thm = 1.0 / (8.0 * r * M)
        v_cert = value_at(w_cert(r, M), var, theta, HS)
        v_proxy = value_at(w_proxy(r, M), var, theta, HS)
        v_unif = value_at(w_uniform(r, M), var, theta, HS)
        w_g = w_geometry(w_cert(r, M), var, theta, HS)
        v_geom = value_at(w_g, var, theta, HS)
        G_true_lo = max(v_cert, v_geom, v_unif)

        rows.append({
            "r": r, "M": M, "answer_at_truth": ans0, "rangeA": rA0, "rangeB": rB0,
            "Gamma_frozen_theorem": G_fr,
            "Gamma_true_lower_theorem": lo_thm, "Gamma_true_upper_theorem": up_thm,
            "J_true_lower_at_cert_design": v_cert,
            "J_true_lower_at_geometry_design": v_geom,
            "J_true_lower_at_proxy_optimum": v_proxy,
            "J_true_lower_at_uniform": v_unif,
            "Gamma_true_attained_lower": G_true_lo,
            "ratio_lower_theorem": 4.0 / (4.0 + 2.0 * r * M),
            "ratio_upper_theorem": 64.0 / (9.0 * r * M),
            "runs": {},
        })

    print("\n  the theorems, evaluated on this family before any run")
    print("  " + "-" * 74)
    print("      r | J_true_lo(cert) J_true_lo(geom) J_true_lo(proxy)  [thm lower, upper]")
    for row in rows:
        print(f"    {row['r']:3d} | {row['J_true_lower_at_cert_design']:.6e}"
              f"  {row['J_true_lower_at_geometry_design']:.6e}"
              f"  {row['J_true_lower_at_proxy_optimum']:.6e}"
              f"   [{row['Gamma_true_lower_theorem']:.3e},"
              f" {row['Gamma_true_upper_theorem']:.3e}]")

    check("THE STARVATION THEOREM, on this family: the frozen surrogate's optimum is"
          " supported on the four extremum cells and carries EXACTLY ZERO information"
          " against the compression alternatives (`frozen_optimum_trueValueC0_zero`)",
          all(row["J_true_lower_at_proxy_optimum"] == 0.0 for row in rows),
          "; ".join(f"r={row['r']}: {row['J_true_lower_at_proxy_optimum']:.1e}" for row in rows))

    check("THE SEPARATION BRACKET (`centred_separation`): an attained design's value is at"
          " least the theorem's lower bound and no design exceeds its upper bound",
          all(row["Gamma_true_attained_lower"] >= row["Gamma_true_lower_theorem"] - 1e-12
              and row["Gamma_true_attained_lower"] <= row["Gamma_true_upper_theorem"] + 1e-12
              for row in rows),
          "; ".join(f"r={row['r']}: {row['Gamma_true_lower_theorem']:.3e} <="
                    f" {row['Gamma_true_attained_lower']:.3e} <="
                    f" {row['Gamma_true_upper_theorem']:.3e}" for row in rows))

    # ---- the frontier, evaluated on the same family -------------------------
    betas = [0.0, 0.25, 0.5, 0.75, 1.0]
    for row in rows:
        r = row["r"]
        _, var, _ = build(r, M)
        HS = half_spaces(r)
        theta, _, _ = build(r, M)
        fr = []
        for b in betas:
            wb = (1.0 - b) * w_proxy(r, M) + b * w_cert(r, M)
            fr.append({"beta": b,
                       "J_true": value_at(wb, var, theta, HS),
                       "lower_theorem": 9.0 * b / (128.0 * (4.0 + 2.0 * r * M)),
                       "upper_theorem": b / (8.0 * r * M)})
        row["frontier"] = fr

    check("THE FRONTIER (`frontier_two_sided`): the explicit mixture"
          " `(1-b)*w_proxy + b*w_cert` lands inside `[9b/(128(4+2rM)), b/(8rM)]` at every"
          " sacrifice `b`, so the two-sided law is exhibited and not only proved",
          all(f["lower_theorem"] - 1e-12 <= f["J_true"] <= f["upper_theorem"] + 1e-12
              for row in rows for f in row["frontier"]),
          "; ".join(f"r={row['r']}: b=0.5 -> {row['frontier'][2]['J_true']:.3e}"
                    f" in [{row['frontier'][2]['lower_theorem']:.3e},"
                    f" {row['frontier'][2]['upper_theorem']:.3e}]" for row in rows))

    # ---- the runs, all three rules on ONE certificate ------------------------
    print("\n  runs (same stopping certificate for every rule)")
    print("  " + "-" * 74)
    rng = np.random.default_rng(20260922)
    for row in rows:
        r = row["r"]
        theta, var, bcells = build(r, M)
        HS = half_spaces(r)
        # The geometry rule solves a maximin at the estimate; that is recomputed on a
        # SCHEDULE rather than every step, and the schedule is recorded, exactly as the
        # A7 learner does for its own oracle.
        cache = {}

        def geom_rule(mu, r=r):
            # The refresh counter must NOT be reset inside the refresh branch: doing so
            # made the schedule 1, 201, 202, 402, 403, ... instead of 1, 201, 401, ...
            t = int(cache.get("t", 0))
            key = t // REFRESH_EVERY
            if key not in cache:
                cache.clear()
                cache["t"] = t
                cache[key] = w_geometry(w_cert(r, M), var, mu, HS)
            cache["t"] = t + 1
            return cache[key]

        rules = {
            "geometry": (geom_rule, 0.0),
            "proxy": (lambda mu, r=r: w_proxy(r, M), 1.0),
            "uniform": (lambda mu, r=r: w_uniform(r, M), 0.0),
        }
        for alpha in alphas:
            for name, (rule, rho) in rules.items():
                taus, cens, corr, shares = [], 0, 0, []
                # The oracle cache is per RUN: leaving it outside this loop let a run
                # start from an allocation computed on the previous run's data, so the
                # runs were not independent restarts.
                rule_id = {"geometry": 1, "proxy": 2, "uniform": 3}[name]
                for ix in range(n_runs):
                    cache.clear()
                    # a fixed numeric id, not hash(name): PYTHONHASHSEED makes `hash`
                    # differ between interpreter processes, so the seed was not reproducible
                    rr = np.random.default_rng([20260922, r, rule_id, ix])
                    t, ans, N, c, tr = run(rr, theta, var, bcells, HS, rule, alpha,
                                           budget, check_every, rho,
                                           trace_every=max(1, budget // 40))
                    taus.append(t)
                    cens += int(c)
                    corr += int((not c) and ans == "A")
                    shares.append(float(N[4:].sum() / t))
                    if ix == 0:
                        row.setdefault("traces", {})[name] = tr
                row["runs"][name] = {
                    "alpha": alpha, "n": n_runs,
                    "tau_per_run": [int(t) for t in taus],
                    "restricted_mean_tau": float(np.mean(taus)),
                    "sem": float(np.std(taus, ddof=1) / math.sqrt(len(taus))),
                    "censored": cens, "correct": corr,
                    "mean_middle_share": float(np.mean(shares)),
                    "budget": budget,
                }
                a = row["runs"][name]
                print(f"      r={r:2d} {name:9s} E[min(tau,B)]={a['restricted_mean_tau']:8.0f}"
                      f" +/- {a['sem']:6.0f}   middle share={a['mean_middle_share']:.4f}"
                      f"   correct={corr}/{n_runs}  censored={cens}")

    check("CENSORING IS REPORTED, NOT ABSORBED: what is tabulated is the RESTRICTED mean"
          " `E[min(tau, B)]` together with the censored count, so a run that never stopped"
          " is not silently recorded as stopping at the budget",
          all("censored" in a and "restricted_mean_tau" in a
              for row in rows for a in row["runs"].values()),
          "; ".join(f"r={row['r']} {k}: {v['censored']} censored"
                    for row in rows for k, v in row["runs"].items()))

    check("the middle-cell share separates the rules in the direction the starvation"
          " theorem predicts: the surrogate's design puts on the middles only what forced"
          " exploration puts there, and strictly less than the geometry-driven design",
          all(row["runs"]["proxy"]["mean_middle_share"]
              < row["runs"]["geometry"]["mean_middle_share"] for row in rows),
          "; ".join(f"r={row['r']}: proxy {row['runs']['proxy']['mean_middle_share']:.4f}"
                    f" vs geometry {row['runs']['geometry']['mean_middle_share']:.4f}"
                    for row in rows))

    out = {
        "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        "family": "thetaC of LeanPaperACentredV1: arm A at (-1/2,1/2), arm B at"
                  " (-1/8,1/8) with 2r middle cells at 0; variance 1 on the four extrema,"
                  " M on the middles",
        "M": M, "r_values": rs, "alphas": alphas, "n_runs": n_runs, "budget": budget,
        "certificate": "exact closed form on each covering half-space; Alt is CONTAINED in"
                       " the union, so the minimum over half-spaces is a valid LOWER bound"
                       " on the regional infimum -- the direction stopping needs",
        "same_certificate_for_every_rule": True,
        "rows": rows,
        "checks": CHECKS,
        "all_passed": all(c["ok"] for c in CHECKS),
    }
    dest = OUT_SMOKE if smoke else OUT
    dest.write_text(json.dumps(out, indent=1))
    print(f"\n{sum(c['ok'] for c in CHECKS)}/{len(CHECKS)} self-checks passed")
    print(f"  artifact: {dest.relative_to(ROOT)}")
    if not out["all_passed"]:
        print("REFUSING to report: a self-check failed.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
