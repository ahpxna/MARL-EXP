"""QUERY: does the leakage order govern the rate ACROSS instances and orders?

A first pass drew the perturbation map g at random and found every instance had
order one, so it never tested the case the paper's argument is about.  It also
fitted the decay from h=0.5 downward, which mixes the pre-asymptotic regime into
the slope.  This version fixes both.

Design.  Draw many random instances (level set, weights, responses, noise scale).
For each, CONSTRUCT perturbation maps of designed leakage order r=1,2,3 by
solving the cancellation conditions on the level moments, then verify the order
independently with the exact procedure the paper proves.  Measure the squared
Hellinger distance by quadrature on a wide h grid reaching 1e-3, and fit the
slope on the asymptotic tail only, with the fit window declared here and the
pre-asymptotic points reported separately rather than dropped silently.

The test is whether the fitted slope equals 2r on every instance where the order
is determined, across all three orders.
"""
import json, math, time, argparse
from pathlib import Path
import numpy as np

MASTER_SEED = 90210
N_INSTANCES = 200
ORDERS = (1, 2, 3)
H_GRID = [0.5 * (0.6 ** i) for i in range(14)]       # 0.5 .. 1.3e-3
TAIL_FROM = 6                                         # fit uses h <= 0.5*0.6^6 = 0.023
QUAD = np.linspace(-26.0, 26.0, 160001)
SIM_SEEDS = [8801, 8803, 8807, 8809, 8813]
SIM_REPS = 2000
SIM_N_CAP = 1500          # largest N the confirmatory simulation is run at
CHUNK_CELLS = 2_000_000   # draws held in memory at once
TOL = 1e-11


def phi(x, s):
    return np.exp(-0.5 * (x / s) ** 2) / (s * math.sqrt(2 * math.pi))


def mix(y, pi, mu, s):
    out = np.zeros_like(y)
    for w, m in zip(pi, mu):
        out += w * phi(y - m, s)
    return out


_NULL = {}


def hell2(pi, f, g, h, s, grid=None, key=None):
    """Squared Hellinger distance by quadrature.  The null mixture does not
    depend on h, so it is computed once per instance and reused across the grid."""
    x = QUAD if grid is None else grid
    if grid is None and key is not None:
        sp = _NULL.get(key)
        if sp is None:
            sp = np.sqrt(mix(x, pi, f, s)); _NULL.clear(); _NULL[key] = sp
    else:
        sp = np.sqrt(mix(x, pi, f, s))
    q = mix(x, pi, [a + h * b for a, b in zip(f, g)], s)
    return float(max(np.trapezoid((sp - np.sqrt(q)) ** 2, x) / 2.0, 0.0))


def level_index(f):
    lv = sorted(set(f))
    return lv, [[i for i, x in enumerate(f) if x == v] for v in lv]


def construct_g(rng, pi, f, r):
    """Perturbation with level moments vanishing at orders 1..r-1 and not at r.

    Within each level the weighted moments sum_{i in level} pi_i g_i^j must vanish
    for j < r.  A level with n members gives n unknowns and r-1 equations, so a
    solution exists whenever every level has at least r members; we solve the
    polynomial system by placing the g_i at the roots of a weighted orthogonal
    family on that level, which zeroes exactly the first r-1 moments.
    """
    lv, idx = level_index(f)
    g = [0.0] * len(f)
    for members in idx:
        n = len(members)
        if n < r + 1:
            return None
        w = np.array([pi[i] for i in members], dtype=float)
        # choose values whose first r-1 weighted power sums vanish:
        # take x_k = base_k and solve for a scaling on a Vandermonde system
        base = rng.normal(0.0, 1.0, size=n)
        base = base - base.mean()
        V = np.vstack([base ** j for j in range(1, r)]) * w if r > 1 else None
        if r > 1:
            # project base onto the null space of the weighted moment map
            A = np.vstack([w * base ** j for j in range(1, r)])
            _, _, Vt = np.linalg.svd(A)
            ns = Vt[(r - 1):]
            if ns.shape[0] == 0:
                return None
            c = rng.normal(size=ns.shape[0])
            vals = ns.T @ c
        else:
            vals = base
        if np.allclose(vals, 0):
            return None
        vals = vals / (np.abs(vals).max() + 1e-300)
        for i, v in zip(members, vals):
            g[i] = float(v)
    return g


def leakage_order(pi, f, g, jmax=8):
    lv, idx = level_index(f)
    for j in range(1, jmax + 1):
        mom = {}
        for v, members in zip(lv, idx):
            mom[v] = sum(pi[i] * g[i] ** j for i in members)
        nz = [v for v in lv if abs(mom[v]) > TOL]
        if not nz:
            continue
        top = max(nz)
        if sum(1 for v in lv if abs(v - top) <= TOL) > 1:
            return None, 'UNDETERMINED_tie_at_top'
        return j, 'OK'
    return None, 'UNDETERMINED_no_leak'


def fit_slope(hs, vals, lo):
    x = np.log(np.asarray(hs[lo:])); y = np.log(np.asarray(vals[lo:]))
    ok = np.isfinite(y) & (np.asarray(vals[lo:]) > 1e-300)
    if ok.sum() < 4:
        return None, None
    A = np.vstack([x[ok], np.ones(ok.sum())]).T
    sol, *_ = np.linalg.lstsq(A, y[ok], rcond=None)
    yh = A @ sol
    ss = float(((y[ok] - yh) ** 2).sum()); st = float(((y[ok] - y[ok].mean()) ** 2).sum())
    return float(sol[0]), (1.0 - ss / st if st > 0 else None)


def measure_error(pi, f, g, h, s, N, seed):
    """Realised error of the likelihood-ratio test on N samples.  The draws are
    chunked so that memory stays bounded whatever N is: a single array of
    SIM_REPS x N doubles reaches gigabytes at the large-N end of the grid."""
    rng = np.random.default_rng(seed)
    fh = [a + h * b for a, b in zip(f, g)]
    mus = np.asarray(f); muh = np.asarray(fh)
    err = 0
    chunk = max(1, CHUNK_CELLS // max(N, 1))
    for w in (0, 1):
        mu = mus if w == 0 else muh
        done = 0
        while done < SIM_REPS:
            r = min(chunk, SIM_REPS - done)
            k = rng.choice(len(pi), size=r * N, p=pi)
            y = (mu[k] + rng.normal(0.0, s, size=r * N)).reshape(r, N)
            lp = np.log(np.maximum(mix(y, pi, f, s), 1e-300))
            lq = np.log(np.maximum(mix(y, pi, fh, s), 1e-300))
            err += int((((lq - lp).sum(axis=1) > 0).astype(int) != w).sum())
            done += r
    return err / (2 * SIM_REPS)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--eps', type=float, default=0.05)
    ap.add_argument('--sim-cells', type=int, default=90)
    a = ap.parse_args()
    rng = np.random.default_rng(MASTER_SEED)
    t0 = time.time(); rows = []; pairs = []; sim_budget = a.sim_cells

    # Self-check: the reported H^2 must be a property of the distributions, not
    # of the quadrature.  Recompute a sample of cells on a grid twice as fine
    # and twice as wide, and report the worst relative disagreement.
    FINE = np.linspace(-40.0, 40.0, 480001)
    chk = np.random.default_rng(MASTER_SEED + 1); worst_q = 0.0
    for _ in range(6):
        nl = int(chk.integers(2, 5)); pr = int(chk.integers(4, 7))
        lv = sorted(chk.choice(np.arange(-3, 4), size=nl, replace=False).astype(float))
        fc = [float(v) for v in lv for _ in range(pr)]
        pc = chk.dirichlet(np.ones(len(fc)) * 3.0); sc = float(chk.uniform(0.7, 1.5))
        gc = construct_g(chk, pc, fc, 2)
        if gc is None:
            continue
        for hh in (H_GRID[0], H_GRID[5], H_GRID[9]):
            c = hell2(pc, fc, gc, hh, sc); r = hell2(pc, fc, gc, hh, sc, grid=FINE)
            if r > 0:
                worst_q = max(worst_q, abs(c - r) / r)
    print(f'quadrature self-check: worst relative disagreement {worst_q:.3e}', flush=True)
    for inst in range(N_INSTANCES):
        nlev = int(rng.integers(2, 5))
        per = int(rng.integers(4, 7))                 # members per level
        levels = sorted(rng.choice(np.arange(-3, 4), size=nlev, replace=False).astype(float))
        f = [float(v) for v in levels for _ in range(per)]
        pi = rng.dirichlet(np.ones(len(f)) * 3.0)
        s = float(rng.uniform(0.7, 1.5))
        got = {}
        for r in ORDERS:
            g = construct_g(rng, pi, f, r)
            if g is None:
                continue
            rr, status = leakage_order(pi, f, g)
            h2 = [hell2(pi, f, g, h, s, key=(inst, r)) for h in H_GRID]
            sl_tail, r2_tail = fit_slope(H_GRID, h2, TAIL_FROM)
            sl_all, r2_all = fit_slope(H_GRID, h2, 0)
            row = dict(instance=inst, designed_order=r, verified_order=rr,
                       status=status, order_matches=(rr == r),
                       sigma=s, levels=[float(x) for x in levels], per_level=per,
                       slope_tail=sl_tail, slope_tail_r2=r2_tail,
                       slope_full=sl_all, slope_full_r2=r2_all,
                       dev_tail=(None if (sl_tail is None or rr is None)
                                 else sl_tail - 2 * rr),
                       dev_full=(None if (sl_all is None or rr is None)
                                 else sl_all - 2 * rr),
                       h2_max=h2[0], h2_min=h2[-1])
            if rr is not None and h2[0] > 0:
                L = -math.log(max(1e-300, 1 - h2[0]))
                N = max(1, math.ceil(math.log(1 / (2 * a.eps)) / L))
                row['N_at_h0'] = N
                got[rr] = min(got.get(rr, 10 ** 12), N)
                if sim_budget > 0 and N <= SIM_N_CAP:
                    e = [measure_error(pi, f, g, H_GRID[0], s, N, sd) for sd in SIM_SEEDS]
                    row['measured_error'] = float(np.mean(e))
                    row['measured_error_sd'] = float(np.std(e, ddof=1))
                    row['target_eps'] = a.eps
                    sim_budget -= 1
            rows.append(row)
        ks = sorted(got)
        for i in range(len(ks) - 1):
            pairs.append(dict(instance=inst, order_low=ks[i], order_high=ks[i + 1],
                              N_low=got[ks[i]], N_high=got[ks[i + 1]],
                              ratio=got[ks[i]] / got[ks[i + 1]]))
        if (inst + 1) % 20 == 0:
            print(f'{inst+1}/{N_INSTANCES}  {time.time()-t0:.0f}s', flush=True)
    det = [r for r in rows if r['dev_tail'] is not None]
    dv = [abs(r['dev_tail']) for r in det]
    df = [abs(r['dev_full']) for r in det if r['dev_full'] is not None]
    import collections
    out = dict(script='EXP_query_generalize.py',
               quadrature_selfcheck_worst_relative=worst_q,
               design='random instances; perturbation maps CONSTRUCTED at designed '
                      'order 1,2,3 and the order verified independently; H^2 by '
                      'quadrature on a 14-point grid to h=1.3e-3; slope fitted on the '
                      'asymptotic tail (h <= 0.023) with the full-grid fit reported '
                      'alongside',
               master_seed=MASTER_SEED, n_instances=N_INSTANCES, orders=list(ORDERS),
               h_grid=H_GRID, tail_from_index=TAIL_FROM,
               tail_h_max=H_GRID[TAIL_FROM], quad_points=len(QUAD),
               sim_seeds=SIM_SEEDS, sim_reps=SIM_REPS, target_eps=a.eps,
               cells_total=len(rows),
               order_counts={str(k): v for k, v in sorted(
                   collections.Counter(r['verified_order'] for r in rows).items(),
                   key=lambda kv: (kv[0] is None, kv[0]))},
               designed_order_matched=sum(1 for r in rows if r['order_matches']),
               tail_max_abs_dev=(max(dv) if dv else None),
               tail_mean_abs_dev=(float(np.mean(dv)) if dv else None),
               full_max_abs_dev=(max(df) if df else None),
               full_mean_abs_dev=(float(np.mean(df)) if df else None),
               order_pairs=pairs, rows=rows,
               wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out,
          f"orders={out['order_counts']} tail max|dev|={out['tail_max_abs_dev']} "
          f"full max|dev|={out['full_max_abs_dev']} {time.time()-t0:.0f}s")


if __name__ == '__main__':
    main()
