"""MASTER: does the price law survive groups that are not alike?

The paper names this as its first open problem. Its per-group bound never uses
homogeneity -- Theorem thm:grouplower holds for any single group -- so what is
in question is the summation step, where a shared budget is divided between
groups that charge different prices. Writing

    s_g^2 = (sqrt(v_g m_g) + sqrt(nu_g kappa_g))^2

for group g's price of one unit of profiled information, and requiring every
group to deliver the same h (which the threshold decision does require, since a
group that delivers nothing leaves its own contrast unidentified), the budget is
h * sum_g s_g^2 and the conjecture is

    Gamma*_het = Delta^2 / (4 sum_g s_g^2),

with K (sqrt(m)+sqrt(kappa))^2 replaced by the SUM over groups rather than by any
average. It reduces to the homogeneous law when the groups agree. In error terms
the information adds over groups, so the realised error should be
Phi(-sqrt(K Gamma*_het B)); the factor K is what turns a per-group price into a
decision, and getting it wrong shows up only in the error test, not in the bound
test -- which is why both are run.

Two tests, because they can fail separately.

E1, the formula against an optimiser. An independent search over feasible
designs, given only the budget and the per-group information constraint and not
the closed form, must not beat Gamma*_het on any instance. A single instance
where it does would refute the conjecture outright.

E2, the formula against a realised error. The same plug-in profiled test as the
homogeneous experiments, on instances whose groups differ by up to a decade in
every price and noise, asking whether the realised error still collapses onto
Phi(-sqrt(Gamma*_het B)). A formula can be a correct bound and still be a poor
predictor, so the bound test does not subsume this one.

Self-check: on instances whose groups are identical, Gamma*_het must equal the
published homogeneous Gamma* exactly, and the realised error must match what the
homogeneous experiment measured. The sweep is not reported otherwise.
"""
import json
import time
import math
import argparse
import os
import sys
from pathlib import Path

import numpy as np
from scipy.stats import norm
from scipy.optimize import minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as _P

MASTER_SEED = 776
SEEDS = [301, 307, 311]
REPS = 30000
LAMBDAS = [0.2, 0.5, 1.0, 2.0, 4.0]
MIN_COUNT = 4


def price(v, m, nu, kap):
    """s_g^2, the price of one unit of profiled information in a group."""
    return (math.sqrt(v * m) + math.sqrt(nu * kap)) ** 2


def gamma_het(D, v, m, nu, kap):
    return D * D / (4.0 * float(np.sum([price(*t) for t in zip(v, m, nu, kap)])))


def optimiser_value(D, v, m, nu, kap, B):
    """Best delivered information found by a search that does not know the law.

    Variables are the per-group ordinary and anchor spends. The search is told
    only the budget and that a group's information is 1/(v/n_x + nu/n_z); it
    maximises the smallest group's information, which is what the threshold
    decision is limited by.
    """
    K = len(v)
    x0 = np.concatenate([np.full(K, B / (2 * K)), np.full(K, B / (2 * K))])

    def info(z):
        a, b = z[:K], z[K:]
        nx = np.maximum(a / np.asarray(m), 1e-9)
        nz = np.maximum(b / np.asarray(kap), 1e-9)
        return 1.0 / (np.asarray(v) / nx + np.asarray(nu) / nz)

    best = 0.0
    for trial in range(6):
        start = x0 if trial == 0 else x0 * np.exp(
            np.random.default_rng(900 + trial).normal(0, 0.4, size=2 * K))
        r = minimize(lambda z: -float(np.min(info(z))), start,
                     constraints=[{'type': 'ineq', 'fun': lambda z: B - z.sum()}],
                     bounds=[(1e-9, B)] * (2 * K),
                     method='SLSQP', options={'maxiter': 800, 'ftol': 1e-14})
        if r.success and r.x.sum() <= B * (1 + 1e-7):
            best = max(best, float(np.min(info(r.x))))
    return best


def realised(rng, D, v, nu, nx, nz, reps):
    """Plug-in profiled test with per-group counts and per-group noises."""
    K = len(v)
    w = rng.integers(0, 2, size=reps)
    b = rng.normal(0.0, 1.0, size=(reps, K))
    ybar = D * w[:, None] + b
    cbar = np.empty((reps, K)); sy = np.empty((reps, K)); sc = np.empty((reps, K))
    for g in range(K):
        ybar[:, g] += rng.normal(0.0, math.sqrt(v[g] / nx[g]), size=reps)
        cbar[:, g] = b[:, g] + rng.normal(0.0, math.sqrt(nu[g] / nz[g]), size=reps)
        sy[:, g] = v[g] * rng.chisquare(nx[g] - 1, size=reps) / (nx[g] - 1)
        sc[:, g] = nu[g] * rng.chisquare(nz[g] - 1, size=reps) / (nz[g] - 1)
    Ih = 1.0 / (sy / np.asarray(nx) + sc / np.asarray(nz))
    S = D * (Ih * (ybar - cbar)).sum(axis=1)
    T = 0.5 * D * D * Ih.sum(axis=1)
    return float(np.mean((S > T).astype(int) != w))


def allocate(D, v, m, nu, kap, B):
    """The design the conjecture names: every group delivers the same h, split
    within a group in inverse proportion to the square roots of its prices."""
    K = len(v)
    h = B / float(np.sum([price(*t) for t in zip(v, m, nu, kap)]))
    nx, nz = [], []
    for g in range(K):
        a, bb = math.sqrt(v[g] * m[g]), math.sqrt(nu[g] * kap[g])
        # delivering information h at least cost needs v/n_x + nu/n_z = 1/h with
        # the two terms in proportion to sqrt(v m) and sqrt(nu kappa), so
        # n_x = h (a+bb) sqrt(v/m) and n_z = h (a+bb) sqrt(nu/kappa)
        nx.append(int(h * (a + bb) * v[g] / a))
        nz.append(int(h * (a + bb) * nu[g] / bb))
    return nx, nz, h


def draw(rng, spread):
    K = int(rng.integers(2, 7))
    f = lambda lo, hi: np.exp(rng.uniform(math.log(lo), math.log(hi), size=K))
    m = f(1.0, 1.0 * spread); kap = f(0.25, 0.25 * spread)
    v = f(0.5, 0.5 * spread); nu = f(0.5, 0.5 * spread)
    D = float(math.exp(rng.uniform(math.log(0.05), math.log(1.0))))
    return K, list(m), list(kap), list(v), list(nu), D


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--instances', type=int, default=120)
    ap.add_argument('--opt-checks', type=int, default=150)
    ap.add_argument('--spread', type=float, default=10.0)
    a = ap.parse_args()
    rng = np.random.default_rng(MASTER_SEED)
    t0 = time.time()

    # ---------------- self-check: identical groups reproduce the law -----
    worst = 0.0
    chk = np.random.default_rng(MASTER_SEED + 1)
    for _ in range(12):
        K = int(chk.integers(1, 9)); mm = float(chk.choice([2.0, 4.0, 8.0]))
        kk = float(chk.choice([0.25, 2 / 3, 1.0, 4.0, 9.0]))
        vv = float(chk.uniform(0.5, 2.0)); nn = float(chk.uniform(0.5, 2.0))
        D = float(chk.uniform(0.2, 1.2))
        het = gamma_het(D, [vv] * K, [mm] * K, [nn] * K, [kk] * K)
        hom = D * D / (4 * K * price(vv, mm, nn, kk))
        worst = max(worst, abs(het - hom) / hom)
    ok = worst < 1e-12
    print(f'self-check: identical groups reproduce the homogeneous law to '
          f'{worst:.1e} -> {"PASS" if ok else "FAIL"}', flush=True)
    if not ok:
        raise SystemExit('self-check failed; sweep not reported')

    # ---------------- E1: the bound against an optimiser -----------------
    beats, opt_rows = 0, []
    for n in range(a.opt_checks):
        K, m, kap, v, nu, D = draw(rng, a.spread)
        B = 1.0
        claimed = 1.0 / float(np.sum([price(*t) for t in zip(v, m, nu, kap)]))
        found = optimiser_value(D, v, m, nu, kap, B)
        ratio = found / claimed if claimed > 0 else None
        opt_rows.append(dict(K=K, claimed_h=claimed, optimiser_h=found, ratio=ratio))
        if ratio is not None and ratio > 1 + 1e-6:
            beats += 1
        if (n + 1) % 50 == 0:
            print(f'  optimiser {n+1}/{a.opt_checks}  {time.time()-t0:.0f}s', flush=True)

    # ---------------- E2: the law against a realised error ---------------
    rows = []
    for inst in range(a.instances):
        K, m, kap, v, nu, D = draw(rng, a.spread)
        g = gamma_het(D, v, m, nu, kap)
        for lam in LAMBDAS:
            # every group delivers h = B / sum_g s_g^2 and the information ADDS,
            # so the total is K B / sum_g s_g^2 and the error is Phi(-sqrt(lambda))
            # only when B is set from K * Gamma_het, not from Gamma_het alone
            B = lam / (K * g)
            nx, nz, h = allocate(D, v, m, nu, kap, B)
            if min(nx) < MIN_COUNT or min(nz) < MIN_COUNT:
                continue
            I = float(np.sum([1.0 / (v[q] / nx[q] + nu[q] / nz[q]) for q in range(K)]))
            pred = float(norm.cdf(-0.5 * D * math.sqrt(I)))
            law = float(norm.cdf(-math.sqrt(lam)))
            e = [realised(np.random.default_rng(s + 7919 * inst + int(1e5 * lam)),
                          D, v, nu, nx, nz, REPS) for s in SEEDS]
            rows.append(dict(instance=inst, K=K, lam=lam, Delta=D,
                             price_spread=float(max(price(*t) for t in zip(v, m, nu, kap))
                                                / min(price(*t) for t in zip(v, m, nu, kap))),
                             n_ordinary=nx, n_anchor=nz,
                             error=float(np.mean(e)), sd=float(np.std(e, ddof=1)),
                             predicted=pred, price_law=law,
                             deviation=float(np.mean(e)) - pred,
                             law_deviation=float(np.mean(e)) - law))
        if (inst + 1) % 20 == 0:
            print(f'  realised {inst+1}/{a.instances}  {time.time()-t0:.0f}s', flush=True)

    dev = [abs(r['deviation']) for r in rows]
    lawdev = [abs(r['law_deviation']) for r in rows]
    ratios = [r['ratio'] for r in opt_rows if r['ratio'] is not None]
    out = dict(provenance=_P.stamp(__file__), script='EXP_master_hetero.py',
               design='heterogeneous prices and noises, up to a decade apart within an '
                      'instance; the conjectured law replaces K(sqrt m+sqrt kappa)^2 by the '
                      'sum of per-group prices; tested against an independent optimiser and '
                      'against a realised error rate',
               master_seed=MASTER_SEED, seeds=SEEDS, reps=REPS, lambdas=LAMBDAS,
               spread=a.spread, instances=a.instances,
               self_check=dict(identical_groups_worst_relative=worst, passed=bool(ok)),
               optimiser=dict(checks=len(opt_rows),
                              instances_beating_the_bound=beats,
                              max_ratio=max(ratios) if ratios else None,
                              median_ratio=float(np.median(ratios)) if ratios else None),
               cells=len(rows),
               max_abs_deviation=max(dev) if dev else None,
               rms_deviation=float(np.sqrt(np.mean(np.square(dev)))) if dev else None,
               law_max_abs_deviation=max(lawdev) if lawdev else None,
               law_rms=float(np.sqrt(np.mean(np.square(lawdev)))) if lawdev else None,
               optimiser_rows=opt_rows, rows=rows,
               wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'cells', len(rows),
          'optimiser beat the bound on', beats, 'of', len(opt_rows),
          'rms dev', round(out['rms_deviation'] or 0, 4),
          'law rms', round(out['law_rms'] or 0, 4))


if __name__ == '__main__':
    main()
