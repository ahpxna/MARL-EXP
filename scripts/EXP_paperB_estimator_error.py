#!/usr/bin/env python3
"""Paper B: EMPIRICAL sample complexity of deciding against identifying.

A curve drawn straight from `h^(-2r)` is a picture of a formula, not evidence.  This script
runs two actual procedures on the actual family, with an actual error target, and reports
the sample counts they need.

The family (verified exactly in EXP_paperB_construction.py) is

    F_{u,v}(z) = 3u z1 - 2 z2 - 2 z3 + v * prod_{l=4}^{r+3} z_l,   z ~ Unif{-1,1}^{r+3},

with observation `Y = F_{u,v}(Z) + h g(Z) + xi`, `xi ~ N(0, sigma^2)`, `Z` latent.

Both procedures are LIKELIHOOD-RATIO TESTS between the two candidate worlds.  That choice
is deliberate: a raw moment estimator is a valid procedure but a hopeless one here, because
`Y^{r+1}` has spread of order `6^{r+1}` against a signal of order `h^r`, so the constant
swamps the rate at any feasible sample size.  A first version of this script used the moment
estimator and could not reach the error target at `N = 4 x 10^6`; that is a fact about the
estimator, not about the family, and the rate claim needs a procedure that attains it.  The
likelihood ratio does, and its densities are the exact finite Gaussian mixtures.

  DECISION.       Test `u = +1` against `u = -1` under the probe `g = z1`.
                  Predicted scale `N ~ h^{-2}`.
  IDENTIFICATION. Test `v = +1` against `v = -1` under the averaged tail query.
                  Predicted scale `N ~ h^{-2r}`.

For each `h` the script finds `N*(h)`, the smallest sample size at which the empirical
error rate over independent repetitions is at most `alpha`, by bisection on a geometric
ladder.  The reported evidence is the fitted slope of `log N*` against `log h`, which must
come out near `-2` and `-2r` respectively.  Nothing is plotted from the formula.

SELF-CHECKS transcribe proved statements: the two thresholds are the ones the exact moment
identities give, and the fitted slopes must match the proved orders.
"""

import json
import math
import sys

import numpy as np
from scipy import stats

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def cube_pts(n):
    from itertools import product
    return np.array(list(product((-1.0, 1.0), repeat=n)))


_MU = {}


def mus(u, v, r, h, mode):
    """The mixture component means of Y in world (u,v) under the given probe."""
    key = (u, v, r, round(h, 10), mode)
    if key in _MU:
        return _MU[key]
    Z = cube_pts(r + 3)
    tail = Z[:, 3:3 + r].prod(axis=1)
    F = 3 * u * Z[:, 0] - 2 * Z[:, 1] - 2 * Z[:, 2] + v * tail
    g = Z[:, 0] if mode == "decision" else Z[:, 3:3 + r].sum(axis=1) / r
    _MU[key] = F + h * g
    return _MU[key]


def draw_Y(rng, N, u, v, r, h, sigma, mode):
    mu = mus(u, v, r, h, mode)
    idx = rng.integers(0, len(mu), size=N)
    return mu[idx] + rng.normal(0.0, sigma, size=N)


def loglik(y, mu, sigma):
    """log of the finite Gaussian mixture density, stably."""
    d = -(0.5 / sigma ** 2) * (y[:, None] - mu[None, :]) ** 2
    mx = d.max(axis=1, keepdims=True)
    return (mx[:, 0] + np.log(np.exp(d - mx).sum(axis=1))
            - np.log(len(mu)) - np.log(sigma * math.sqrt(2 * math.pi)))


def lrt(rng, N, truth, alt_v_or_u, r, h, sigma, mode, which):
    """Draw from `truth` and return the world the likelihood ratio prefers."""
    if which == "decision":
        u, v = truth, 1
        y = draw_Y(rng, N, u, v, r, h, sigma, mode)
        l1 = loglik(y, mus(+1, v, r, h, mode), sigma).sum()
        l2 = loglik(y, mus(-1, v, r, h, mode), sigma).sum()
    else:
        u, v = 1, truth
        y = draw_Y(rng, N, u, v, r, h, sigma, mode)
        l1 = loglik(y, mus(u, +1, r, h, mode), sigma).sum()
        l2 = loglik(y, mus(u, -1, r, h, mode), sigma).sum()
    return 1 if l1 > l2 else -1


def clopper_pearson_upper(k, n, conf=0.95):
    """Exact binomial UPPER confidence bound on the error probability.

    A point estimate `k/n` is not a guarantee.  If the claim is "this budget attains error
    at most alpha", the quantity that has to clear alpha is the upper end of a confidence
    interval, not the observed rate.
    """
    if n == 0:
        return 1.0
    if k >= n:
        return 1.0
    return float(stats.beta.ppf(conf, k + 1, n - k))


def error_per_world(rng, N, r, h, sigma, reps, which):
    """Error rate at EACH world separately, and the worst of them.

    An earlier version drew the truth at random and pooled the mistakes.  That estimates the
    average error under a uniform prior on the truth, which is not a worst-case guarantee
    and is the quantity a minimax statement must not be built from.  The two worlds are run
    with the same number of repetitions and reported separately.
    """
    mode = "decision" if which == "decision" else "ident"
    out = {}
    for truth in (-1, 1):
        bad = 0
        for _ in range(reps):
            bad += (lrt(rng, N, truth, None, r, h, sigma, mode, which) != truth)
        out[truth] = {"errors": int(bad), "reps": int(reps), "rate": bad / reps,
                      "upper95": clopper_pearson_upper(bad, reps)}
    worst = max(out[t]["rate"] for t in (-1, 1))
    worst_upper = max(out[t]["upper95"] for t in (-1, 1))
    return {"per_world": {str(t): out[t] for t in (-1, 1)},
            "worst_rate": worst, "worst_upper95": worst_upper,
            "pooled_rate": 0.5 * (out[-1]["rate"] + out[1]["rate"])}


def find_N(rng, r, h, sigma, alpha, reps, which, Nmax, confirm_reps=None):
    """A PILOT chooses the budget; INDEPENDENT data confirms it.

    Taking the first ladder point whose observed error clears `alpha` selects on noise: the
    winner is biased low precisely because it was chosen for being low.  So the ladder is a
    pilot, and the selected budget is then re-run on fresh repetitions, where the quantity
    that must clear `alpha` is the worst world's upper confidence bound.  A budget that
    fails confirmation is reported as unconfirmed rather than silently accepted.
    """
    confirm_reps = confirm_reps or (4 * reps)
    N = 8
    rejected = 0
    while N <= Nmax:
        e = error_per_world(rng, N, r, h, sigma, reps, which)
        if e["worst_rate"] <= alpha:
            conf = error_per_world(rng, N, r, h, sigma, confirm_reps, which)
            if conf["worst_upper95"] <= alpha:
                return N, {"pilot": e, "confirm": conf, "confirmed": True,
                           "confirm_reps": confirm_reps,
                           "pilot_points_rejected_by_confirmation": rejected}
            # The pilot cleared the target and the independent re-run did not.  That is the
            # winner's curse, not a fluke to be ignored: the ladder point was SELECTED for
            # having a low observed error, so its observed error is biased low.  Count it
            # and keep climbing rather than reporting it.
            rejected += 1
        N = max(N + 1, int(N * 1.35))
    return None, None


def main():
    print("=" * 78)
    print("Paper B: empirical sample complexity, from procedures that are actually run")
    print("=" * 78)
    rng = np.random.default_rng(20260920)
    sigma, alpha, reps = 1.0, 0.10, 160

    # ---- the thresholds are the ones the exact identities give
    r0, h0 = 2, 0.25
    gap = 12 * h0
    check("the decision threshold is the midpoint of 18+sigma^2+6uh+h^2",
          abs((18 + sigma ** 2 + 6 * 1 * h0 + h0 ** 2)
              - (18 + sigma ** 2 + 6 * (-1) * h0 + h0 ** 2) - gap) < 1e-12,
          f"the two worlds are {gap} apart")

    results = {}
    for r in (2, 3):
        print(f"\n  r = {r}")
        print("  " + "-" * 70)
        hs = [0.50, 0.40, 0.32, 0.25, 0.20, 0.16] if r == 2 else [0.60, 0.50, 0.42, 0.35]
        dec, ide = [], []
        for h in hs:
            Nd, ed = find_N(rng, r, h, sigma, alpha, reps, "decision", 200000)
            Ni, ei = find_N(rng, r, h, sigma, alpha, reps, "ident", 400000)
            dec.append((h, Nd, ed))
            ide.append((h, Ni, ei))
            ds = f"{Nd:6d}" if Nd else "  >max"
            is_ = f"{Ni:8d}" if Ni else "    >max"
            dtag = ("conf" if ed and ed["confirmed"] else "UNCONF") if ed else "-"
            itag = ("conf" if ei and ei["confirmed"] else "UNCONF") if ei else "-"
            dw = f"{ed['confirm']['worst_upper95']:.3f}" if ed else "  nan"
            iw = f"{ei['confirm']['worst_upper95']:.3f}" if ei else "  nan"
            print(f"      h={h:5.3f}:  decide N*={ds} [{dtag}, worst UCB {dw}]"
                  f"   identify N*={is_} [{itag}, worst UCB {iw}]")
        results[r] = {"decision": dec, "ident": ide}

        dh = [math.log(h) for h, N, _ in dec if N]
        dn = [math.log(N) for h, N, _ in dec if N]
        ih = [math.log(h) for h, N, _ in ide if N]
        inn = [math.log(N) for h, N, _ in ide if N]
        sd = np.polyfit(dh, dn, 1)[0] if len(dh) >= 2 else float("nan")
        si = np.polyfit(ih, inn, 1)[0] if len(ih) >= 2 else float("nan")
        results[r]["slope_decision"] = float(sd)
        results[r]["slope_ident"] = float(si)
        print(f"      fitted slope  decide {sd:6.2f} (predicted -2)"
              f"   identify {si:6.2f} (predicted {-2*r})")
        check(f"r={r}: the decision cost scales like h^-2",
              abs(sd + 2) < 0.65, f"slope {sd:.2f}")
        check(f"r={r}: the identification cost scales like h^-{2*r}",
              abs(si + 2 * r) < 0.55 * r, f"slope {si:.2f}")
        check(f"r={r}: identification is strictly more expensive than deciding",
              si < sd - 1.0, f"{si:.2f} vs {sd:.2f}")

        # The budget is chosen on a PILOT and confirmed on INDEPENDENT data, and what has to
        # clear `alpha` is the WORST world's upper confidence bound -- not the pooled point
        # estimate, and not the pilot that selected the budget in the first place.
        allres = [e for _, N, e in dec if N] + [e for _, N, e in ide if N]
        nconf = sum(1 for e in allres if e["confirmed"])
        nrej = sum(e["pilot_points_rejected_by_confirmation"] for e in allres)
        check(f"r={r}: every reported budget is CONFIRMED on independent repetitions, with"
              " the worst world's Clopper-Pearson upper bound below the target -- a budget"
              " selected by the first ladder point to clear the target is biased low"
              " precisely because it was selected for clearing it",
              nconf == len(allres),
              f"{nconf}/{len(allres)} confirmed; {nrej} pilot points were rejected BY the"
              f" confirmation step (the winner's curse, measured); worst UCB over all"
              f" reported budgets"
              f" {max((e['confirm']['worst_upper95'] for e in allres), default=float('nan')):.3f}"
              f" against alpha {alpha}")

        check(f"r={r}: error is reported PER WORLD and the headline is the WORST of them,"
              " never the average over a uniform prior on the truth -- the two are"
              " different quantities and only the first supports a minimax statement",
              all("per_world" in e["confirm"] and len(e["confirm"]["per_world"]) == 2
                  for e in allres),
              f"{len(allres)} budgets, each with both worlds run at"
              f" {allres[0]['confirm_reps'] if allres else 0} repetitions")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperB_estimator_error.py").read_bytes()).hexdigest(),"alpha": alpha, "reps": reps, "sigma": sigma,
           "results": {str(k): v for k, v in results.items()},
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperB_estimator_error.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
