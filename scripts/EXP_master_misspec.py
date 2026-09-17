"""MASTER: does the price law still predict when the model is wrong?

Experiment E2 tests the law against an estimator that has to work for its
answer -- but inside a world that matches the model exactly: Gaussian noise,
homogeneous variances, a separation the test knows. A design sheet is used under
none of those conditions. This asks how the prediction degrades when each
assumption is broken one at a time, which is the question an experimenter
actually has.

Five families of misspecification, each applied to the price-law optimal design:

  heavy_tail_t{3,5,10}   observation noise is Student-t, rescaled to the same
                         variance, so the law's input is unchanged and only the
                         shape is wrong
  hetero                 per-group variances drawn over a 9x range while the
                         analyst pools them into one
  delta_{0.5,...,2}      the test is run at a separation c*Delta while the truth
                         is Delta -- the most common misspecification in practice
  contaminated_{1,5}pct  that fraction of anchor observations is replaced by an
                         outlier at ten standard deviations
  nuisance_t3            the group offset itself is heavy-tailed rather than
                         Gaussian

The baseline arm reproduces E2's own conditions and must agree with E2's
finite-count prediction; that is the self-check, and it ties this experiment to
the validated one rather than letting it float free.
"""
import json
import time
import math
import argparse
import importlib.util
import os
import sys
from pathlib import Path

import numpy as np
from scipy.stats import norm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as _P

spec = importlib.util.spec_from_file_location('mf', 'scripts/EXP_master_finite.py')
MF = importlib.util.module_from_spec(spec)
spec.loader.exec_module(MF)

MASTER_SEED = 8123
SEEDS = [911, 913, 917]
REPS = 20000
LAMBDAS = [0.4, 1.0, 2.25, 4.0]
MIN_COUNT = 4

ARMS = ('gaussian', 'heavy_tail_t10', 'heavy_tail_t5', 'heavy_tail_t3',
        'hetero', 'delta_0.5', 'delta_0.75', 'delta_1.25', 'delta_2.0',
        'contaminated_1pct', 'contaminated_5pct', 'nuisance_t3')


def draw_noise(rng, arm, scale, size):
    """Noise of the stated variance, with the shape the arm specifies."""
    if arm.startswith('heavy_tail_t'):
        df = int(arm.rsplit('t', 1)[1])
        return rng.standard_t(df, size=size) * scale / math.sqrt(df / (df - 2))
    return rng.normal(0.0, scale, size=size)


REPLICATE_ARMS = ('heavy_tail_t10', 'heavy_tail_t5', 'heavy_tail_t3',
                  'contaminated_1pct', 'contaminated_5pct')


def realised(rng, arm, K, D, v, nu, nx, nz, reps):
    """Error rate of the plug-in profiled test under one misspecification.

    Two code paths, and which one is correct depends on the arm.

    For an arm whose data really are Gaussian with the variance the test is
    estimating -- the baseline, the heterogeneous-variance arm, the heavy-tailed
    OFFSET arm (the offset cancels in the contrast and never enters the
    replicate spread), and every wrong-Delta arm -- the sample variance has the
    exact sampling law v * chi^2_{n-1} / (n-1), so it can be drawn directly and
    the per-observation draws are unnecessary.

    For an arm that breaks the shape of the observation noise, that law no
    longer holds: Student-t replicates have a far more dispersed sample variance
    than Gaussian ones, and contaminated anchors have an inflated one. Drawing
    the sample variance from the Gaussian law there would simulate an analyst
    who somehow still gets clean variance estimates from dirty data, which is
    not the situation being studied. Those arms therefore draw every replicate
    and compute the mean and variance from them.
    """
    v_g = np.full(K, v)
    if arm == 'hetero':
        v_g = v * np.exp(rng.uniform(-math.log(3), math.log(3), size=K))
    D_test = D
    if arm.startswith('delta_'):
        D_test = D * float(arm.split('_', 1)[1])

    w = rng.integers(0, 2, size=reps)
    b = (rng.standard_t(3, size=(reps, K)) / math.sqrt(3.0)
         if arm == 'nuisance_t3' else rng.normal(0.0, 1.0, size=(reps, K)))

    if arm in REPLICATE_ARMS:
        ybar = np.empty((reps, K)); sy = np.empty((reps, K))
        cbar = np.empty((reps, K)); sc = np.empty((reps, K))
        frac = (float(arm.split('_')[1].replace('pct', '')) / 100.0
                if arm.startswith('contaminated_') else 0.0)
        for g in range(K):
            yg = draw_noise(rng, arm, math.sqrt(v_g[g]), size=(reps, nx))
            ybar[:, g] = D * w + b[:, g] + yg.mean(axis=1)
            sy[:, g] = yg.var(axis=1, ddof=1)
            cg = rng.normal(0.0, math.sqrt(nu), size=(reps, nz))
            if frac:
                hit = rng.random((reps, nz)) < frac
                cg = np.where(hit, cg + 10.0 * math.sqrt(nu), cg)
            cbar[:, g] = b[:, g] + cg.mean(axis=1)
            sc[:, g] = cg.var(axis=1, ddof=1)
    else:
        ybar = D * w[:, None] + b
        for g in range(K):
            ybar[:, g] += rng.normal(0.0, math.sqrt(v_g[g] / nx), size=reps)
        cbar = b + rng.normal(0.0, math.sqrt(nu / nz), size=(reps, K))
        sy = np.empty((reps, K))
        for g in range(K):
            sy[:, g] = v_g[g] * rng.chisquare(nx - 1, size=reps) / (nx - 1)
        sc = nu * rng.chisquare(nz - 1, size=(reps, K)) / (nz - 1)

    Ih = 1.0 / (sy / nx + sc / nz)
    S = D_test * (Ih * (ybar - cbar)).sum(axis=1)
    T = 0.5 * D_test * D_test * Ih.sum(axis=1)
    return float(np.mean((S > T).astype(int) != w))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--instances', type=int, default=150)
    ap.add_argument('--replicate-nmax', type=int, default=64)
    ap.add_argument('--replicate-reps', type=int, default=8000)
    a = ap.parse_args()
    rng = np.random.default_rng(MASTER_SEED)
    t0 = time.time()

    # ---------------- self-check: the baseline arm must match E2 --------
    # The comparison is made where the finite-count prediction is sharp. E2
    # established that the plug-in test sits about a percentage point above it
    # when a group can afford only a handful of observations, so a check at
    # small n would be testing that known penalty rather than this generator;
    # the check therefore forces at least 64 ordinary observations per group,
    # where E2 measured the residual at 0.0006 or less.
    worst, checked = 0.0, 0
    chk = np.random.default_rng(MASTER_SEED + 1)
    tries = 0
    while checked < 8 and tries < 400:
        tries += 1
        K = int(chk.integers(1, 9)); m = float(chk.choice([2.0, 4.0, 8.0]))
        kap = float(chk.choice([0.25, 2 / 3, 1.0, 4.0, 9.0]))
        D = float(math.exp(chk.uniform(math.log(0.05), math.log(0.4))))
        v = float(chk.uniform(0.5, 2.0)); nu = float(chk.uniform(0.5, 2.0))
        gamma = D * D / (4 * (math.sqrt(v * m) + math.sqrt(nu * kap)) ** 2)
        B = 2.25 / gamma
        x, z = MF.allocation(K, m, kap, v, nu, 'optimal')
        nx, nz = int(B * x / m), int(B * z / kap)
        if nx < 64 or nz < 64:
            continue
        checked += 1
        pred = norm.cdf(-0.5 * D * math.sqrt(MF.information(K, 'optimal', v, nu, nx, nz)))
        got = realised(np.random.default_rng(4242 + checked), 'gaussian',
                       K, D, v, nu, nx, nz, 60000)
        worst = max(worst, abs(got - pred))
    ok = checked >= 8 and worst < 0.006
    print(f'self-check: baseline arm vs the E2 finite-count prediction on {checked} '
          f'cells with n_x >= 64, worst gap {worst:.4f} -> '
          f'{"PASS" if ok else "FAIL"}', flush=True)
    if not ok:
        raise SystemExit('self-check failed; sweep not reported')

    rows = []
    for inst in range(a.instances):
        K = int(rng.integers(1, 9)); m = float(rng.choice([2.0, 4.0, 8.0]))
        kap = float(rng.choice([0.25, 2 / 3, 1.0, 4.0, 9.0]))
        D = float(math.exp(rng.uniform(math.log(0.2), math.log(1.6))))
        v = float(rng.uniform(0.5, 2.0)); nu = float(rng.uniform(0.5, 2.0))
        gamma = D * D / (4 * (math.sqrt(v * m) + math.sqrt(nu * kap)) ** 2)
        for lam in LAMBDAS:
            B = lam / gamma
            x, z = MF.allocation(K, m, kap, v, nu, 'optimal')
            nx, nz = int(B * x / m), int(B * z / kap)
            if nx < MIN_COUNT or nz < MIN_COUNT:
                continue
            I = MF.information(K, 'optimal', v, nu, nx, nz)
            pred = float(norm.cdf(-0.5 * D * math.sqrt(I)))
            law = float(norm.cdf(-math.sqrt(lam)))
            cell = dict(instance=inst, K=K, m=m, kappa=kap, Delta=D, v=v, nu=nu,
                        lam=lam, n_ordinary=nx, n_anchor=nz,
                        predicted=pred, price_law=law)
            for arm in ARMS:
                rep = REPS
                if arm in REPLICATE_ARMS:
                    if max(nx, nz) > a.replicate_nmax:
                        cell[arm] = dict(skipped=True, reason='counts above the '
                                         'replicate-level budget')
                        continue
                    rep = a.replicate_reps
                e = [realised(np.random.default_rng(s + 7919 * inst + int(1e5 * lam)),
                              arm, K, D, v, nu, nx, nz, rep) for s in SEEDS]
                cell[arm] = dict(error=float(np.mean(e)), sd=float(np.std(e, ddof=1)),
                                 deviation=float(np.mean(e)) - pred, reps=rep,
                                 replicate_level=(arm in REPLICATE_ARMS))
            rows.append(cell)
        if (inst + 1) % 10 == 0:
            print(f'{inst+1}/{a.instances}  {time.time()-t0:.0f}s', flush=True)

    summary = {}
    for arm in ARMS:
        d = [r[arm]['deviation'] for r in rows if not r[arm].get('skipped')]
        if not d:
            summary[arm] = dict(cells=0)
            continue
        summary[arm] = dict(cells=len(d),
                            replicate_level=(arm in REPLICATE_ARMS),
                            mean_deviation=float(np.mean(d)),
                            median_deviation=float(np.median(d)),
                            max_abs_deviation=float(np.max(np.abs(d))),
                            rms_deviation=float(np.sqrt(np.mean(np.square(d)))),
                            frac_worse_than_predicted=float(np.mean(np.array(d) > 0)))
    out = dict(provenance=_P.stamp(__file__),
               script='EXP_master_misspec.py',
               design='the price-law optimal design under twelve generators, one matching '
                      'the model and eleven breaking a single assumption each; the '
                      'baseline arm is checked against the finite-count prediction of the '
                      'main finite-sample experiment before anything else is reported',
               master_seed=MASTER_SEED, seeds=SEEDS, reps=REPS, lambdas=LAMBDAS,
               arms=list(ARMS), replicate_arms=list(REPLICATE_ARMS),
               replicate_nmax=a.replicate_nmax, replicate_reps=a.replicate_reps,
               instances=a.instances,
               self_check=dict(baseline_worst_gap=worst, cells_checked=checked,
                               min_n_ordinary=64, passed=bool(ok)),
               summary=summary, rows=rows, cells=len(rows),
               wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'cells', len(rows))
    for arm in ARMS:
        s = summary[arm]
        if not s['cells']:
            print(f'  {arm:20s} no cells within the replicate-level budget'); continue
        print(f"  {arm:20s} mean dev {s['mean_deviation']:+.4f}  "
              f"rms {s['rms_deviation']:.4f}  max {s['max_abs_deviation']:.4f}")


if __name__ == '__main__':
    main()
