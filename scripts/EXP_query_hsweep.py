"""QUERY: measure the leakage-order scaling directly.

Holds the two worlds fixed and sweeps the perturbation scale h for two admissible
measurements of different leakage order.  At each h it computes the per-sample
squared Hellinger distance exactly from the mixture densities by numerical
quadrature on a fine grid, derives the required sample count from the proved
transfer, and then MEASURES the Bayes regret of the likelihood-ratio test by
simulation at that count.  The point is to replace extrapolation from a single
cell with a measured curve.

Frozen protocol: seeds, grid and reps are fixed here and not tuned afterwards.
"""
import json, math, time, argparse
from pathlib import Path
import numpy as np

SEEDS = [8801, 8803, 8807, 8809, 8813]
REPS = 4000                      # per world, per seed, per cell
SIGMA = 1.0
GRID = np.linspace(-14.0, 14.0, 24001)   # quadrature grid for H^2


def phi(x, s=SIGMA):
    return np.exp(-0.5 * (x / s) ** 2) / (s * math.sqrt(2 * math.pi))


def mixture(y, pi, f, g, h):
    """Density of the finite Gaussian mixture at perturbation scale h."""
    out = np.zeros_like(y)
    for w, fx, gx in zip(pi, f, g):
        out += w * phi(y - fx - h * gx)
    return out


# Two worlds, fixed for the whole study.  Level structure is shared.
PI = [0.25, 0.25, 0.25, 0.25]
F0 = [-1.0, 0.0, 1.0, 2.0]
F1 = [-1.0, 0.0, 1.0, 2.0]

# Two admissible measurements.  G2 cancels at first order (level moments agree),
# G1 does not; the strict top level carries a non-zero coefficient in both.
G_ORDER2 = [1.0, -1.0, -1.0, 1.0]
G_ORDER1 = [0.0, 0.0, 0.0, 1.0]


def hellinger2(h, g):
    p = mixture(GRID, PI, F0, [0.0] * 4, 0.0)
    q = mixture(GRID, PI, F1, g, h)
    d = np.trapezoid((np.sqrt(p) - np.sqrt(q)) ** 2, GRID) / 2.0
    return float(max(d, 0.0))


def sample_mixture(rng, n, pi, f, g, h):
    k = rng.choice(len(pi), size=n, p=pi)
    mu = np.asarray(f)[k] + h * np.asarray(g)[k]
    return mu + rng.normal(0.0, SIGMA, size=n)


def logratio(y, g, h):
    p = mixture(y, PI, F0, [0.0] * 4, 0.0)
    q = mixture(y, PI, F1, g, h)
    return np.log(np.maximum(q, 1e-300)) - np.log(np.maximum(p, 1e-300))


def run_cell(h, g, N, seed):
    """Measure the error rate of the likelihood-ratio test at N samples."""
    rng = np.random.default_rng(seed)
    err = 0
    for w in (0, 1):
        ff, gg, hh = (F0, [0.0] * 4, 0.0) if w == 0 else (F1, g, h)
        y = sample_mixture(rng, REPS * N, PI, ff, gg, hh).reshape(REPS, N)
        s = logratio(y, g, h).sum(axis=1)
        pred = (s > 0).astype(int)
        err += int((pred != w).sum())
    return err / (2 * REPS)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--eps', type=float, default=0.05)
    a = ap.parse_args()
    t0 = time.time()
    hs = [0.60, 0.50, 0.42, 0.35, 0.29, 0.24, 0.20, 0.17, 0.14]
    rows = []
    for name, g, r in (('order2', G_ORDER2, 2), ('order1', G_ORDER1, 1)):
        for h in hs:
            H2 = hellinger2(h, g)
            L = -math.log(max(1e-300, 1 - H2))
            N = max(1, math.ceil(math.log(1 / (2 * a.eps)) / L))
            if N > 400000:
                rows.append(dict(measurement=name, r=r, h=h, H2=H2, L=L, N=N,
                                 measured_error=None, skipped='N too large'))
                print(f'{name} h={h} N={N} skipped', flush=True)
                continue
            errs = [run_cell(h, g, N, s) for s in SEEDS]
            rows.append(dict(measurement=name, r=r, h=h, H2=H2, L=L, N=N,
                             measured_error=float(np.mean(errs)),
                             error_sd=float(np.std(errs, ddof=1)),
                             seeds=SEEDS, reps_per_world=REPS,
                             target_eps=a.eps))
            print(f'{name} h={h:.3f} H2={H2:.4e} N={N} err={np.mean(errs):.5f} '
                  f'({time.time()-t0:.0f}s)', flush=True)
    out = dict(script='EXP_query_hsweep.py',
               design='two fixed worlds, two admissible measurements, h swept; '
                      'H^2 by quadrature, N from the proved transfer, error measured '
                      'by simulating the likelihood-ratio test',
               sigma=SIGMA, pi=PI, f0=F0, f1=F1,
               g_order2=G_ORDER2, g_order1=G_ORDER1,
               seeds=SEEDS, reps_per_world=REPS, target_eps=a.eps,
               grid_points=len(GRID), wall_seconds=round(time.time() - t0, 1),
               rows=rows)
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, f'{time.time()-t0:.0f}s')


if __name__ == '__main__':
    main()
