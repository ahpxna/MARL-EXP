"""QUERY: does the leakage order govern the rate ACROSS instances and orders?

Two earlier passes were wrong in ways worth recording, because both produced
plausible output.

The first drew the perturbation g at random and found every instance had order
one, so it never tested the case the paper's argument is about.  The second
tried to force higher orders by making the weighted level moments
sum_{x in level} pi_x g(x)^j vanish for j < r.  That is impossible: the weights
are positive, so the j=2 moment is a sum of non-negative terms and vanishes only
when g vanishes on the level.  Order three is unreachable in that model, and the
run duly returned order one for all 600 cells.

The error was modelling a single world with a perturbation.  Equation (5) of the
paper is a statement about TWO worlds that share a level set: the coefficients
that must agree below the order are M^(0)_j(v) and M^(1)_j(v), and their equality
is a difference of two positive sums, not the vanishing of one.  This version
follows the paper.

Design.  Each instance carries two responses f_0 and f_1 over a common index set
with a common level set and equal level masses, so the two worlds are
indistinguishable at h=0, and a single perturbation direction g.  World 1 is
world 0 with a block of indices exchanged between two levels at equal weight,
which preserves the level masses exactly.  On that block g takes the values of a
Prouhet--Thue--Morse pair: splitting {0,...,2^r-1} by the parity of the binary
digit sum gives two sets whose j-th power sums agree for every j < r and differ
at j = r, so the designed order is r by construction, at any scale and offset.
Off the block g is drawn at random and cancels identically, because those indices
sit in the same level in both worlds.

The designed order is then VERIFIED independently from the level coefficients,
the squared Hellinger distance between the two worlds is measured by quadrature
on a 14-point h grid reaching 6.5e-4, and the slope is fitted on the asymptotic
tail only, with the fit window declared here and the full-grid fit reported
alongside rather than the pre-asymptotic points being dropped silently.

The test is whether the fitted slope equals 2r on every instance where the order
is determined, across all three orders.
"""
import json, math, time, argparse, collections
from pathlib import Path
import numpy as np

import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import EXP_provenance as _P

MASTER_SEED = 90210
N_INSTANCES = 200
ORDERS = (1, 2, 3)
H_GRID = [0.5 * (0.6 ** i) for i in range(14)]       # 0.5 .. 6.5e-4
TAIL_FROM = 6                                         # fit uses h <= 0.5*0.6^6 = 0.023
QUAD = np.linspace(-26.0, 26.0, 160001)
SIM_SEEDS = [8801, 8803, 8807]
SIM_REPS = 2000
SIM_N_CAP = 1500
CHUNK_CELLS = 2_000_000
TOL = 1e-11


def phi(x, s):
    return np.exp(-0.5 * (x / s) ** 2) / (s * math.sqrt(2 * math.pi))


def mixture(y, pi, mu, s):
    out = np.zeros_like(y)
    for w, m in zip(pi, mu):
        out += w * phi(y - m, s)
    return out


def prouhet(r):
    """{0,...,2^r-1} split by parity of binary digit sum: the two halves have
    equal j-th power sums for every j < r and unequal ones at j = r."""
    A = [k for k in range(2 ** r) if bin(k).count('1') % 2 == 0]
    B = [k for k in range(2 ** r) if bin(k).count('1') % 2 == 1]
    return A, B


def build(rng, r):
    """One instance: two worlds sharing a level set, and a perturbation of
    designed leakage order r.  Returns None if the draw cannot host the block."""
    A, B = prouhet(r); blk = len(A)
    nlev = int(rng.integers(2, 5))
    per = int(rng.integers(max(4, blk), 7))
    if per < blk:
        return None
    levels = sorted(rng.choice(np.arange(-3, 4), size=nlev, replace=False).astype(float))
    n = nlev * per
    lev_of = [levels[i // per] for i in range(n)]        # world 0 assignment
    ia, ib = 0, 1                                        # the two levels swapped
    a_idx = [ia * per + k for k in range(blk)]
    b_idx = [ib * per + k for k in range(blk)]
    block = set(a_idx) | set(b_idx)

    mass = float(rng.uniform(0.3, 0.7))
    w_blk = mass / (2 * blk)
    rest = [i for i in range(n) if i not in block]
    pi = np.zeros(n)
    for i in block:
        pi[i] = w_blk
    pi[rest] = rng.dirichlet(np.ones(len(rest)) * 3.0) * (1.0 - mass)
    pi = pi / pi.sum()          # exact normalisation: the sampler demands it

    alpha = float(rng.uniform(0.5, 2.0)) * (1 if rng.integers(0, 2) else -1)
    beta = float(rng.uniform(-1.0, 1.0))
    g = np.zeros(n)
    g[rest] = rng.normal(0.0, 1.0, size=len(rest))
    for k in range(blk):
        g[a_idx[k]] = alpha * A[k] + beta
        g[b_idx[k]] = alpha * B[k] + beta

    f0 = list(lev_of)
    f1 = list(lev_of)
    for k in range(blk):                                 # exchange the block
        f1[a_idx[k]] = lev_of[b_idx[k]]
        f1[b_idx[k]] = lev_of[a_idx[k]]
    s = float(rng.uniform(0.7, 1.5))
    return dict(pi=pi, g=g, f0=f0, f1=f1, levels=[float(v) for v in levels],
                sigma=s, per=per, nlev=nlev, block=blk)


def level_moments(pi, f, g, j):
    m = collections.defaultdict(float)
    for w, v, x in zip(pi, f, g):
        m[v] += w * (x ** j)
    return m


def mass_check(inst):
    """The two worlds must be identical at h=0: equal mass on every level."""
    m0 = level_moments(inst['pi'], inst['f0'], np.ones_like(inst['g']), 1)
    m1 = level_moments(inst['pi'], inst['f1'], np.ones_like(inst['g']), 1)
    return max(abs(m0[v] - m1[v]) for v in set(m0) | set(m1))


def verified_order(inst, jmax=8):
    """Least j whose level coefficients differ between the two worlds."""
    pi, g, f0, f1 = inst['pi'], inst['g'], inst['f0'], inst['f1']
    for j in range(1, jmax + 1):
        m0 = level_moments(pi, f0, g, j); m1 = level_moments(pi, f1, g, j)
        vs = sorted(set(m0) | set(m1))
        d = {v: m0[v] - m1[v] for v in vs}
        scale = max(1.0, max(abs(m0[v]) + abs(m1[v]) for v in vs))
        nz = [v for v in vs if abs(d[v]) > TOL * scale]
        if not nz:
            continue
        top = max(nz)
        if sum(1 for v in vs if abs(v - top) <= TOL) > 1:
            return None, 'UNDETERMINED_tie_at_top'
        return j, 'OK'
    return None, 'UNDETERMINED_no_leak'


def hell2(inst, h, grid=None):
    x = QUAD if grid is None else grid
    pi, g, s = inst['pi'], inst['g'], inst['sigma']
    p = mixture(x, pi, [a + h * b for a, b in zip(inst['f0'], g)], s)
    q = mixture(x, pi, [a + h * b for a, b in zip(inst['f1'], g)], s)
    return float(max(np.trapezoid((np.sqrt(p) - np.sqrt(q)) ** 2, x) / 2.0, 0.0))


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


def measure_error(inst, h, N, seed):
    """Realised error of the likelihood-ratio test between the two worlds."""
    rng = np.random.default_rng(seed)
    pi, g, s = inst['pi'], inst['g'], inst['sigma']
    mu0 = np.asarray([a + h * b for a, b in zip(inst['f0'], g)])
    mu1 = np.asarray([a + h * b for a, b in zip(inst['f1'], g)])
    err = 0
    chunk = max(1, CHUNK_CELLS // max(N, 1))
    for w in (0, 1):
        mu = mu0 if w == 0 else mu1
        done = 0
        while done < SIM_REPS:
            rr = min(chunk, SIM_REPS - done)
            k = rng.choice(len(pi), size=rr * N, p=pi)
            y = (mu[k] + rng.normal(0.0, s, size=rr * N)).reshape(rr, N)
            lp = np.log(np.maximum(mixture(y, pi, mu0, s), 1e-300))
            lq = np.log(np.maximum(mixture(y, pi, mu1, s), 1e-300))
            err += int((((lq - lp).sum(axis=1) > 0).astype(int) != w).sum())
            done += rr
    return err / (2 * SIM_REPS)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--eps', type=float, default=0.05)
    ap.add_argument('--sim-cells', type=int, default=90)
    a = ap.parse_args()
    rng = np.random.default_rng(MASTER_SEED)
    t0 = time.time()

    # ---- self-check: the construction must do what it claims -------------
    chk = np.random.default_rng(MASTER_SEED + 1)
    sc = {'mass': 0.0, 'order_ok': 0, 'order_of': 0}
    FINE = np.linspace(-40.0, 40.0, 480001); worst_q = 0.0
    for _ in range(8):
        for r in ORDERS:
            inst = build(chk, r)
            if inst is None:
                continue
            sc['mass'] = max(sc['mass'], mass_check(inst))
            vr, _ = verified_order(inst)
            sc['order_of'] += 1; sc['order_ok'] += int(vr == r)
            if r == 2:
                for hh in (H_GRID[0], H_GRID[5], H_GRID[9]):
                    c = hell2(inst, hh); ref = hell2(inst, hh, grid=FINE)
                    if ref > 0:
                        worst_q = max(worst_q, abs(c - ref) / ref)
    ok = (sc['mass'] < 1e-12 and sc['order_ok'] == sc['order_of'])
    print(f"self-check: level masses agree to {sc['mass']:.1e}; designed order "
          f"verified {sc['order_ok']}/{sc['order_of']}; quadrature stable to "
          f"{worst_q:.1e} -> {'PASS' if ok else 'FAIL'}", flush=True)
    if not ok:
        raise SystemExit('construction self-check failed; sweep not reported')

    rows = []; pairs = []; sim_budget = a.sim_cells
    for inst_i in range(N_INSTANCES):
        got = {}
        for r in ORDERS:
            inst = build(rng, r)
            if inst is None:
                continue
            rr, status = verified_order(inst)
            h2 = [hell2(inst, h) for h in H_GRID]
            sl_t, r2_t = fit_slope(H_GRID, h2, TAIL_FROM)
            sl_a, r2_a = fit_slope(H_GRID, h2, 0)
            row = dict(instance=inst_i, designed_order=r, verified_order=rr,
                       status=status, order_matches=(rr == r),
                       sigma=inst['sigma'], levels=inst['levels'],
                       per_level=inst['per'], block=inst['block'],
                       mass_residual=mass_check(inst),
                       slope_tail=sl_t, slope_tail_r2=r2_t,
                       slope_full=sl_a, slope_full_r2=r2_a,
                       dev_tail=(None if (sl_t is None or rr is None) else sl_t - 2 * rr),
                       dev_full=(None if (sl_a is None or rr is None) else sl_a - 2 * rr),
                       h2_max=h2[0], h2_min=h2[-1], h2_curve=h2)
            if rr is not None and h2[0] > 0:
                L = -math.log(max(1e-300, 1 - h2[0]))
                N = max(1, math.ceil(math.log(1 / (2 * a.eps)) / L))
                row['N_at_h0'] = N
                got[rr] = min(got.get(rr, 10 ** 12), N)
                if sim_budget > 0 and N <= SIM_N_CAP:
                    e = [measure_error(inst, H_GRID[0], N, sd) for sd in SIM_SEEDS]
                    row['measured_error'] = float(np.mean(e))
                    row['measured_error_sd'] = float(np.std(e, ddof=1))
                    row['target_eps'] = a.eps
                    sim_budget -= 1
            rows.append(row)
        ks = sorted(got)
        for i in range(len(ks) - 1):
            pairs.append(dict(instance=inst_i, order_low=ks[i], order_high=ks[i + 1],
                              N_low=got[ks[i]], N_high=got[ks[i + 1]],
                              ratio=got[ks[i + 1]] / got[ks[i]]))
        if (inst_i + 1) % 20 == 0:
            print(f'{inst_i+1}/{N_INSTANCES}  {time.time()-t0:.0f}s', flush=True)

    det = [r for r in rows if r['dev_tail'] is not None]
    dv = [abs(r['dev_tail']) for r in det]
    df = [abs(r['dev_full']) for r in det if r['dev_full'] is not None]
    byord = collections.Counter(r['verified_order'] for r in rows)
    out = dict(provenance=_P.stamp(__file__), script='EXP_query_generalize.py',
               design='200 instances; each carries two worlds sharing a level set with equal '
                      'level masses and a perturbation of designed leakage order 1, 2 or 3 '
                      'built from a Prouhet-Thue-Morse pair; the order is verified '
                      'independently from the level coefficients; H^2 between the two worlds '
                      'by quadrature on a 14-point grid to h=6.5e-4; slope fitted on the '
                      'asymptotic tail (h <= 0.023) with the full-grid fit reported alongside',
               master_seed=MASTER_SEED, n_instances=N_INSTANCES, orders=list(ORDERS),
               h_grid=H_GRID, tail_from=TAIL_FROM, tail_h_max=H_GRID[TAIL_FROM],
               self_check=dict(mass_residual=sc['mass'], order_verified=sc['order_ok'],
                               order_of=sc['order_of'],
                               quadrature_worst_relative=worst_q, passed=bool(ok)),
               orders_verified={str(k): v for k, v in sorted(byord.items(), key=lambda t: (t[0] is None, t[0]))},
               order_matches=sum(1 for r in rows if r['order_matches']), cells=len(rows),
               tail_max_abs_dev=(max(dv) if dv else None),
               tail_rms_dev=(float(np.sqrt(np.mean(np.square(dv)))) if dv else None),
               full_max_abs_dev=(max(df) if df else None),
               rows=rows, pairs=pairs, wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'orders=', dict(byord), 'matched', out['order_matches'], '/', len(rows),
          'tail max|dev|=', out['tail_max_abs_dev'], f"{time.time()-t0:.0f}s")


if __name__ == '__main__':
    main()
