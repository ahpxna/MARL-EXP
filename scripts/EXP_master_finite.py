"""MASTER: does the price law predict finite-sample behaviour?

The price law is an information statement.  A group buys ordinary observations
at unit cost m and noise v, and anchor observations at unit cost kappa and noise
nu; splitting a budget optimally between them delivers Fisher information
B/(sqrt(v m)+sqrt(nu kappa))^2 about the contrast, so the likelihood-ratio
decision errs at rate Phi(-sqrt(Gamma* B)) with

    Gamma* = Delta^2 / (4 (sqrt(v m) + sqrt(nu kappa))^2).

That is an asymptote in three separate ways.  It assumes the two variances are
known, it treats observation counts as continuous, and it treats the per-group
nuisance as removed exactly rather than by a finite anchor sample.  This
experiment measures how far a real estimator sits from it.

Two predictions are tested, not one.

  (1) The finite-count prediction.  Whatever the design, the delivered
      information is the sum over groups of 1/(v/n_x + nu/n_z) for a group with
      anchors and 1/(v/n_x + 1) for a group without, and the error should be
      Phi(-(Delta/2) sqrt(sum)).  This is falsifiable design by design.

  (2) The price law itself, Phi(-sqrt(Gamma* B)), for the optimal design only.
      It differs from (1) by integer rounding alone.

The budget is set from a dimensionless grid, B = lambda/Gamma*, so prediction
(2) is one curve for every instance -- a universality collapse the experiment
can falsify.  Delta is drawn log-uniformly over a wide range, which decouples
the two axes: at a fixed lambda a small Delta buys the same information with
many more observations per group, so the plug-in penalty can be measured
against sample size at constant information.

Four designs: the price-law optimum, an even split, the optimum with one
group's anchors absent, and an anchor-free design.  The anchor-free design is
not a straw man -- its groups are still analysed, through the marginal channel,
whose information is capped at 1 per group however large the budget.  The
prediction there is a plateau, not a failure.

The test is a plug-in profiled likelihood ratio.  It does not know v or nu and
estimates both from the replicate spread; it uses the integer counts the budget
actually buys; and it weights each group by its own estimated information, so a
missing anchor costs information rather than miscalibrating the threshold.
"""
import json, math, time, argparse
from pathlib import Path
import numpy as np
from scipy.stats import norm

import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import EXP_provenance as _P

MASTER_SEED = 7331
N_INSTANCES = 240
SEEDS = [5501, 5503, 5507]
REPS = 30000
LAMBDAS = [0.05, 0.1, 0.2, 0.4, 0.7, 1.0, 1.5, 2.25, 3.0, 4.0]
MIN_COUNT = 4                 # below this a replicate variance is meaningless
DESIGNS = ('optimal', 'uniform', 'one_missing', 'anchor_free')


def allocation(K, m, kap, v, nu, kind):
    """Per-group budget fractions (ordinary, anchor).  K*(x+z) = 1."""
    if kind == 'anchor_free':
        return 1.0 / K, 0.0
    if kind == 'uniform':
        return 1.0 / (2 * K), 1.0 / (2 * K)
    a, b = math.sqrt(v * m), math.sqrt(nu * kap)
    return (1.0 / K) * a / (a + b), (1.0 / K) * b / (a + b)


def anchored(K, kind):
    """How many groups keep their anchors under this design."""
    if kind == 'anchor_free':
        return 0
    if kind == 'one_missing':
        return max(K - 1, 0)
    return K


def information(K, kind, v, nu, nx, nz):
    """Delivered information: contrast channel where anchors exist, marginal
    channel where they do not."""
    na = anchored(K, kind)
    tot = 0.0
    if na and nz >= MIN_COUNT:
        tot += na / (v / nx + nu / nz)
    else:
        na = 0
    tot += (K - na) / (v / nx + 1.0)
    return tot


def realised_error(rng, K, kind, D, v, nu, nx, nz, reps):
    """Error rate of the plug-in profiled test."""
    na = anchored(K, kind)
    if nz < MIN_COUNT:
        na = 0
    nm = K - na
    w = rng.integers(0, 2, size=reps)
    S = np.zeros(reps); T = np.zeros(reps)
    if na:
        b = rng.normal(0.0, 1.0, size=(reps, na))
        ybar = D * w[:, None] + b + rng.normal(0.0, math.sqrt(v / nx), size=(reps, na))
        cbar = b + rng.normal(0.0, math.sqrt(nu / nz), size=(reps, na))
        sy = v * rng.chisquare(nx - 1, size=(reps, na)) / (nx - 1)
        sc = nu * rng.chisquare(nz - 1, size=(reps, na)) / (nz - 1)
        Ih = 1.0 / (sy / nx + sc / nz)
        S += D * (Ih * (ybar - cbar)).sum(axis=1); T += 0.5 * D * D * Ih.sum(axis=1)
    if nm:
        b = rng.normal(0.0, 1.0, size=(reps, nm))
        ybar = D * w[:, None] + b + rng.normal(0.0, math.sqrt(v / nx), size=(reps, nm))
        sy = v * rng.chisquare(nx - 1, size=(reps, nm)) / (nx - 1)
        Ih = 1.0 / (sy / nx + 1.0)
        S += D * (Ih * ybar).sum(axis=1); T += 0.5 * D * D * Ih.sum(axis=1)
    return float(np.mean((S > T).astype(int) != w))


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True)
    a = ap.parse_args()
    rng = np.random.default_rng(MASTER_SEED)
    t0 = time.time(); rows = []; skipped = 0
    for inst in range(N_INSTANCES):
        K = int(rng.integers(1, 9)); m = float(rng.choice([2.0, 4.0, 8.0]))
        kap = float(rng.choice([0.25, 2 / 3, 1.0, 4.0, 9.0]))
        D = float(math.exp(rng.uniform(math.log(0.05), math.log(1.6))))
        v = float(rng.uniform(0.5, 2.0)); nu = float(rng.uniform(0.5, 2.0))
        scale = (math.sqrt(v * m) + math.sqrt(nu * kap)) ** 2
        gamma = D * D / (4 * scale)
        for lam in LAMBDAS:
            B = lam / gamma
            cell = dict(instance=inst, K=K, m=m, kappa=kap, Delta=D, v=v, nu=nu,
                        gamma_star=gamma, lam=lam, budget=B,
                        price_law=float(norm.cdf(-math.sqrt(lam))))
            for kind in DESIGNS:
                x, z = allocation(K, m, kap, v, nu, kind)
                nx = int(B * x / m); nz = int(B * z / kap) if z > 0 else 0
                if nx < MIN_COUNT or (anchored(K, kind) and 0 < nz < MIN_COUNT):
                    cell[kind] = dict(skipped=True, n_ordinary=nx, n_anchor=nz)
                    skipped += 1
                    continue
                I = information(K, kind, v, nu, nx, nz)
                e = [realised_error(np.random.default_rng(s + 7919 * inst + int(1e5 * lam)),
                                    K, kind, D, v, nu, nx, nz, REPS) for s in SEEDS]
                cell[kind] = dict(skipped=False, error=float(np.mean(e)),
                                  sd=float(np.std(e, ddof=1)),
                                  predicted=float(norm.cdf(-0.5 * D * math.sqrt(I))),
                                  information=I, n_ordinary=nx, n_anchor=nz)
            rows.append(cell)
        if (inst + 1) % 10 == 0:
            print(f'{inst+1}/{N_INSTANCES}  {time.time()-t0:.0f}s', flush=True)
    dev = [abs(c[k]['error'] - c[k]['predicted']) for c in rows for k in DESIGNS
           if not c[k].get('skipped')]
    law = [abs(c['optimal']['error'] - c['price_law']) for c in rows
           if not c['optimal'].get('skipped')]
    live = [c for c in rows if not c['optimal'].get('skipped')
            and not c['uniform'].get('skipped') and not c['anchor_free'].get('skipped')]
    order_ok = sum(1 for c in live
                   if c['optimal']['error'] <= c['uniform']['error'] + 0.005
                   and c['uniform']['error'] <= c['anchor_free']['error'] + 0.005)
    out = dict(provenance=_P.stamp(__file__), script='EXP_master_finite.py',
               design='240 random instances; budget from a dimensionless grid B=lambda/Gamma*; '
                      'Delta log-uniform so sample size varies at fixed information; four designs; '
                      'plug-in profiled likelihood-ratio test with estimated variances and integer '
                      'counts; 3 seeds x 30000 replications per cell',
               master_seed=MASTER_SEED, n_instances=N_INSTANCES, seeds=SEEDS, reps=REPS,
               lambdas=LAMBDAS, designs=list(DESIGNS), min_count=MIN_COUNT, rows=rows,
               cells_simulated=len(dev), cells_skipped=skipped,
               max_abs_deviation=max(dev), rms_deviation=float(np.sqrt(np.mean(np.square(dev)))),
               price_law_max_deviation=max(law),
               price_law_rms=float(np.sqrt(np.mean(np.square(law)))),
               ordering_holds=order_ok, ordering_of=len(live),
               wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'max dev', round(max(dev), 4), 'rms', round(out['rms_deviation'], 4),
          'price-law max', round(max(law), 4), 'ordering', order_ok, '/', len(live),
          'skipped', skipped)


if __name__ == '__main__':
    main()
