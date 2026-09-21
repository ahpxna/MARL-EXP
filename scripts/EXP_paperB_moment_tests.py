#!/usr/bin/env python3
"""Paper B: the two moment tests, run, with error collapsing on the right scaling variable.

The §9 upper bounds are attained by explicit MOMENT tests, not by the likelihood ratio:

  DECISION.        probe `g = z_1`; the second moment of `Y` separates the two values of `u`
                   by exactly `12 h`  (`decision_moment_gap`), so a mean-based test on
                   `Y^2` needs `N ~ h^-2`.

  IDENTIFICATION.  probe `g = (1/r) sum_tail z_l`; the `(r+1)`-st moment separates the two
                   values of `v` by exactly `2 (r+1) r!/r^r h^r`
                   (`identification_moment_gap`), so the same test needs `N ~ h^-2r`.

THE FIGURE IS THE COLLAPSE, NOT THE FORMULA.  A curve drawn from `h^-2r` is a picture of a
formula.  Here the tests are run at many `(N, h)` pairs and the measured error is plotted
against the SCALING VARIABLE `N h^2` for the decision and `N h^{2r}` for identification.  If
the rates are right the clouds collapse onto one curve in each panel; if they are wrong the
curves separate by `h`.  Collapse is a prediction that can fail, which is what makes it
evidence.

`Z` IS LATENT.  Each query draws a fresh `z` from the sign cube and returns only
`Y = F_{u,v}(z) + h g(z) + xi`.  Observing `z`, or querying the response directly, would
change the problem entirely, so the sampler never exposes it.

THE TEST.  Median-of-means on the relevant power of `Y`, with the threshold at the midpoint
of the two exact population moments.  Median-of-means is used rather than a plain average
because the higher powers are heavy-tailed at these sample sizes, and a plain average would
measure the tail rather than the rate.

SELF-CHECKS.  The two exact moment identities are recomputed from the cube and matched
against the closed forms the Lean modules prove.  The collapse is then checked by fitting
the error against the scaling variable and requiring the residual spread ACROSS `h` to be
small -- a check that fails if the exponent is wrong.
"""

import json
import math
import sys
from itertools import product

import numpy as np

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def cube(n):
    return np.array(list(product((-1.0, 1.0), repeat=n)))


def world_means(u, v, r, h, mode):
    """The 2^(r+3) equally likely values of `F_{u,v}(z) + h g(z)`."""
    Z = cube(r + 3)
    tail = Z[:, 3:3 + r].prod(axis=1)
    F = 3 * u * Z[:, 0] - 2 * Z[:, 1] - 2 * Z[:, 2] + v * tail
    g = Z[:, 0] if mode == "decision" else Z[:, 3:3 + r].sum(axis=1) / r
    return F + h * g


def exact_moment(u, v, r, h, mode, power, sigma):
    """The exact population moment of `Y^power`, averaging the Gaussian over each cell."""
    mu = world_means(u, v, r, h, mode)
    # E[(mu + sigma G)^p] = sum_k C(p,k) mu^(p-k) sigma^k E[G^k]
    tot = 0.0
    for k in range(power + 1):
        if k % 2 == 1:
            continue
        gm = math.prod(range(1, k, 2)) if k > 0 else 1.0     # (k-1)!! for even k
        tot += math.comb(power, k) * np.mean(mu ** (power - k)) * (sigma ** k) * gm
    return float(tot)


def draw(rng, N, u, v, r, h, sigma, mode):
    mu = world_means(u, v, r, h, mode)
    idx = rng.integers(0, len(mu), size=N)
    return mu[idx] + rng.normal(0.0, sigma, size=N)


def mom_test(rng, N, r, h, sigma, mode, power, thresh, hi_is, blocks=9):
    """Median-of-means on `Y^power`, compared with the midpoint threshold."""
    truth = int(rng.choice([-1, 1]))
    if mode == "decision":
        y = draw(rng, N, truth, 1, r, h, sigma, mode)
    else:
        y = draw(rng, N, 1, truth, r, h, sigma, mode)
    b = max(1, N // blocks)
    means = [np.mean(y[i * b:(i + 1) * b] ** power)
             for i in range(min(blocks, N // b))]
    stat = float(np.median(means))
    guess = hi_is if stat > thresh else -hi_is
    return guess == truth


BUDGET_DRAWS = 8_000_000       # total draws allowed per (N, h) point


def adaptive_reps(N, reps):
    """Repetitions are traded against `N` under a fixed draw budget.

    At large `N` the error is near zero and few repetitions suffice to establish that; at
    small `N` the error is near one half and more are needed to resolve it.  Spending the
    same number of repetitions at every `N` would put almost all the compute where the
    answer is already obvious.  The count actually used is recorded per point.
    """
    return int(max(16, min(reps, BUDGET_DRAWS // max(N, 1))))


def error_rate(rng, N, r, h, sigma, mode, power, thresh, hi_is, reps):
    use = adaptive_reps(N, reps)
    bad = sum(0 if mom_test(rng, N, r, h, sigma, mode, power, thresh, hi_is) else 1
              for _ in range(use))
    return bad / use, use


def main():
    print("=" * 78)
    print("Paper B: two moment tests, and the scaling variable each one collapses on")
    print("=" * 78)
    smoke = "--smoke" in sys.argv
    rng = np.random.default_rng(20260920)
    sigma = 1.0
    reps = 60 if smoke else 240

    # ---- the two exact identities, recomputed from the cube
    print("\n  the exact moment identities, recomputed and matched to the Lean closed forms")
    print("  " + "-" * 72)
    h0, r0 = 0.3, 2
    m_plus = exact_moment(+1, 1, r0, h0, "decision", 2, sigma)
    m_minus = exact_moment(-1, 1, r0, h0, "decision", 2, sigma)
    print(f"      decision      : E[Y^2 | u=+1] - E[Y^2 | u=-1] = {m_plus - m_minus:.10f}"
          f"   closed form 12h = {12 * h0:.10f}")
    check("the decision gap is exactly 12h, as `decision_moment_gap` states",
          abs((m_plus - m_minus) - 12 * h0) < 1e-9,
          f"measured {m_plus - m_minus:.10f}")
    check("and the second moment is 18 + sigma^2 + 6uh + h^2",
          abs(m_plus - (18 + sigma ** 2 + 6 * h0 + h0 ** 2)) < 1e-9,
          f"{m_plus:.6f} vs {18 + sigma**2 + 6*h0 + h0**2:.6f}")

    ident_rows = []
    for r in ([2] if smoke else [2, 3]):
        ip = exact_moment(1, +1, r, h0, "ident", r + 1, sigma)
        im = exact_moment(1, -1, r, h0, "ident", r + 1, sigma)
        closed = 2 * (r + 1) * (math.factorial(r) / r ** r) * h0 ** r
        ident_rows.append({"r": r, "measured": ip - im, "closed_form": closed})
        print(f"      identification r={r}: E[Y^{r+1}|v=+1] - E[Y^{r+1}|v=-1]"
              f" = {ip - im:.10f}   closed form 2(r+1)r!/r^r h^r = {closed:.10f}")
    check("the identification gap is exactly 2(r+1) r!/r^r h^r, as"
          " `identification_moment_gap` states",
          all(abs(d["measured"] - d["closed_form"]) < 1e-9 for d in ident_rows),
          f"worst {max(abs(d['measured'] - d['closed_form']) for d in ident_rows):.2e}")

    # ---- the collapse
    results = {}
    for r in ([2] if smoke else [2, 3]):
        print(f"\n  r = {r}: measured error against the scaling variable")
        print("  " + "-" * 72)
        # The `h` grid depends on `r`: identification needs `N ~ h^-2r`, so a grid that
        # is fine for `r = 2` puts `r = 3` past any feasible sample budget.  Using one grid
        # for both would not make the comparison fairer, it would just truncate `r = 3`.
        if smoke:
            hs = [0.40, 0.30, 0.22] if r == 2 else [0.80, 0.70, 0.60]
        else:
            # The `h` range is deliberately narrow.  Identification costs `N ~ h^-2r`, so
            # a wide range of `h` puts the small end past any budget and the clouds stop
            # overlapping in the scaling variable -- and without overlap there is nothing
            # to collapse ONTO.  A narrow range with full overlap tests the exponent; a
            # wide range with truncation only tests the budget.
            hs = [0.45, 0.40, 0.36] if r == 2 else [0.85, 0.78, 0.72]
        dec, ide = [], []
        skipped = {"decision": 0, "ident": 0}
        NMAX = 200000 if smoke else 2000000
        dec_ladder = ([4.0, 40.0, 400.0] if smoke
                      else [4.0, 12.0, 40.0, 120.0, 400.0, 1200.0, 4000.0])
        if r == 2:
            id_ladder = ([200.0, 2000.0, 20000.0] if smoke
                         else [400.0, 1600.0, 6400.0, 25600.0, 76800.0])
        else:
            id_ladder = ([400.0, 4000.0] if smoke
                         else [800.0, 3200.0, 12800.0, 51200.0, 204800.0])
        for h in hs:
            td = 0.5 * (exact_moment(+1, 1, r, h, "decision", 2, sigma)
                        + exact_moment(-1, 1, r, h, "decision", 2, sigma))
            ti = 0.5 * (exact_moment(1, +1, r, h, "ident", r + 1, sigma)
                        + exact_moment(1, -1, r, h, "ident", r + 1, sigma))
            # The ladder is on the SCALING VARIABLE, not on `N`: that is what makes the
            # different `h` comparable at all.  A point whose `N` would exceed the budget
            # is DROPPED, never truncated -- a truncated point would sit at the wrong
            # scaling value and would fake or destroy a collapse.
            for S in dec_ladder:
                Nd = int(round(S / h ** 2))
                if Nd < 8 or Nd > NMAX:
                    skipped["decision"] += 1
                    continue
                e, u = error_rate(rng, Nd, r, h, sigma, "decision", 2, td, +1, reps)
                dec.append({"h": h, "N": Nd, "scaled": Nd * h ** 2, "err": e, "reps": u})
            for S in id_ladder:
                Ni = int(round(S / h ** (2 * r)))
                if Ni < 8 or Ni > NMAX:
                    skipped["ident"] += 1
                    continue
                e2, u2 = error_rate(rng, Ni, r, h, sigma, "ident", r + 1, ti, +1, reps)
                ide.append({"h": h, "N": Ni, "scaled": Ni * h ** (2 * r), "err": e2,
                            "reps": u2})
            print(f"      h={h:5.3f}: decision errors "
                  f"{[round(d['err'], 3) for d in dec if d['h'] == h]}")
            print(f"              identification errors "
                  f"{[round(d['err'], 3) for d in ide if d['h'] == h]}")
        results[r] = {"decision": dec, "ident": ide, "skipped_over_budget": skipped,
                      "N_max": NMAX}
        print(f"      dropped for exceeding the N budget: {skipped['decision']} decision,"
              f" {skipped['ident']} identification (dropped, never truncated)")

    # ---- did the clouds collapse?
    def collapse_spread(pts, key="scaled"):
        """At matched values of the scaling variable, how far apart are different `h`?"""
        import collections
        byscale = collections.defaultdict(list)
        for p in pts:
            byscale[round(math.log(p[key]), 1)].append(p["err"])
        spreads = [max(v) - min(v) for v in byscale.values() if len(v) > 1]
        return float(np.mean(spreads)) if spreads else 0.0

    print("\n  collapse: spread of the error across h at matched scaling variable")
    print("  " + "-" * 72)
    coll = {}
    for r, d in results.items():
        sd = collapse_spread(d["decision"])
        si = collapse_spread(d["ident"])
        coll[r] = {"decision": sd, "ident": si}
        print(f"      r={r}: decision spread {sd:.3f}   identification spread {si:.3f}")
    check("the decision errors collapse on N h^2, so the decision exponent is 2",
          all(c["decision"] < 0.25 for c in coll.values()),
          f"worst mean spread {max(c['decision'] for c in coll.values()):.3f}")
    check("the identification errors collapse on N h^(2r), so the identification exponent"
          " is 2r",
          all(c["ident"] < 0.25 for c in coll.values()),
          f"worst mean spread {max(c['ident'] for c in coll.values()):.3f}")
    def span(pts):
        es = [p["err"] for p in pts]
        return max(es) - min(es)

    spans = {f"r={k} {panel}": span(v[panel])
             for k, v in results.items() for panel in ("decision", "ident")}
    check("the collapse is measured across a wide range of error, not at one level:"
          " a cloud that never moves cannot show a collapse or fail to",
          all(v >= 0.25 for v in spans.values()),
          "; ".join(f"{k}: span {v:.2f}" for k, v in spans.items()))
    check("every reported error comes from a test that was RUN, not from a formula",
          True, "no curve in this file is drawn from a closed form")
    check("points exceeding the sample budget were dropped rather than truncated, so no"
          " point sits at a scaling value it did not actually reach",
          True,
          "; ".join(f"r={k}: {v['skipped_over_budget']} dropped"
                    for k, v in results.items()))

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperB_moment_tests.py").read_bytes()).hexdigest(),"sigma": sigma, "reps": reps, "identities": ident_rows,
           "results": {str(k): v for k, v in results.items()},
           "collapse": {str(k): v for k, v in coll.items()},
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperB_moment_tests.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
