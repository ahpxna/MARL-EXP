"""QUERY: does the exponent stay 2r at leakage orders four and five?

The main sweep covers orders 1, 2 and 3. The sandwich theorem is stated for
every r, so the natural question is whether the measured exponent keeps up. It
cannot simply be asked on the same grid, for a reason worth stating rather than
discovering: H^2 falls like h^{2r}, so at order 5 and h = 6.5e-4 the true value
is about 1e-32, while it is computed as an integral of (sqrt(p) - sqrt(q))^2
where p and q are both of order 1. Double precision resolves their difference to
about 1e-16 in absolute terms, so everything below roughly 1e-24 in H^2 is
arithmetic noise, and a slope fitted through it would be a fit to rounding.

So the grid is chosen per order instead: it runs from h = 0.5 down to the point
where the predicted H^2 reaches about 1e-22, which keeps every evaluated value
inside the range double precision can represent while still spanning enough
decades to fit a slope. The floor is declared here, not tuned after seeing the
answer, and the fit quality is reported per cell so that a cell which does drift
into the noise is visible rather than averaged in.

Everything else -- the two-world construction, the Prouhet-Thue-Morse block, the
independent verification of the order, the quadrature self-check -- is imported
unchanged from the main sweep.
"""
import json
import math
import time
import argparse
import importlib.util
import collections
from pathlib import Path

import numpy as np

spec = importlib.util.spec_from_file_location('qg', 'scripts/EXP_query_generalize.py')
QG = importlib.util.module_from_spec(spec)
spec.loader.exec_module(QG)

MASTER_SEED = 515151
TARGET_FLOOR = 1e-18          # smallest H^2 the grid is allowed to reach
POINTS = 14
R2_MIN = 0.999                # a tail fit below this is reported, not used


def build_ho(rng, r):
    """The main sweep's two-world construction, with room for a bigger block.

    The Prouhet-Thue-Morse block has 2^(r-1) cells on each side, so order 4
    needs eight cells per level and order 5 needs sixteen -- more than the main
    sweep's draw allows. Only the level size changes; the construction, the
    mass-preserving exchange and the perturbation are the same, and the level
    count is held to two or three so the mixture stays small enough to integrate.
    """
    A, B = QG.prouhet(r)
    blk = len(A)
    # The raw Prouhet values run up to 2^r - 1, which is 31 at order 5; scaled by
    # h and by alpha they would push mixture components outside any fixed
    # quadrature window. The identity is invariant under affine maps, so
    # normalise to [0,1] and let alpha, beta supply the randomisation.
    span = float(max(max(A), max(B))) or 1.0
    A = [x / span for x in A]
    B = [x / span for x in B]
    nlev = int(rng.integers(2, 4))
    per = int(rng.integers(blk, blk + 3))
    levels = sorted(rng.choice(np.arange(-3, 4), size=nlev, replace=False).astype(float))
    n = nlev * per
    lev_of = [levels[i // per] for i in range(n)]
    ia, ib = 0, 1
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
    pi = pi / pi.sum()

    alpha = float(rng.uniform(0.5, 2.0)) * (1 if rng.integers(0, 2) else -1)
    beta = float(rng.uniform(-1.0, 1.0))
    g = np.zeros(n)
    g[rest] = rng.normal(0.0, 1.0, size=len(rest))
    for k in range(blk):
        g[a_idx[k]] = alpha * A[k] + beta
        g[b_idx[k]] = alpha * B[k] + beta

    f0 = list(lev_of)
    f1 = list(lev_of)
    for k in range(blk):
        f1[a_idx[k]] = lev_of[b_idx[k]]
        f1[b_idx[k]] = lev_of[a_idx[k]]
    s = float(rng.uniform(0.7, 1.5))
    return dict(pi=pi, g=g, f0=f0, f1=f1, levels=[float(v) for v in levels],
                sigma=s, per=per, nlev=nlev, block=blk)


def grid_for(order, h0=0.5, typical_at_h0=1e-3):
    """Geometric grid from h0 down to where the predicted H^2 hits the floor."""
    decades = math.log10(typical_at_h0 / TARGET_FLOOR)
    lo = h0 * 10 ** (-decades / (2 * order))
    ratio = (lo / h0) ** (1 / (POINTS - 1))
    return [h0 * ratio ** i for i in range(POINTS)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--instances', type=int, default=80)
    ap.add_argument('--orders', type=int, nargs='+', default=[1, 2, 3, 4, 5])
    a = ap.parse_args()
    rng = np.random.default_rng(MASTER_SEED)
    t0 = time.time()

    grids = {r: grid_for(r) for r in a.orders}
    tail_from = POINTS // 2

    # ---------------- self-check ----------------------------------------
    chk = np.random.default_rng(MASTER_SEED + 1)
    sc = {'mass': 0.0, 'order_ok': 0, 'order_of': 0, 'quad': 0.0}
    FINE = np.linspace(-40.0, 40.0, 480001)
    for _ in range(3):
        for r in a.orders:
            inst = build_ho(chk, r)
            if inst is None:
                continue
            sc['mass'] = max(sc['mass'], QG.mass_check(inst))
            vr, _ = QG.verified_order(inst)
            sc['order_of'] += 1
            sc['order_ok'] += int(vr == r)
            h = grids[r][0]
            c = QG.hell2(inst, h)
            ref = QG.hell2(inst, h, grid=FINE)
            if ref > 0:
                sc['quad'] = max(sc['quad'], abs(c - ref) / ref)
    ok = sc['mass'] < 1e-12 and sc['order_ok'] == sc['order_of'] and sc['quad'] < 1e-8
    print(f"self-check: masses {sc['mass']:.1e}; order {sc['order_ok']}/{sc['order_of']}; "
          f"quadrature {sc['quad']:.1e} -> {'PASS' if ok else 'FAIL'}", flush=True)
    if not ok:
        raise SystemExit('self-check failed; sweep not reported')

    rows = []
    for inst_i in range(a.instances):
        for r in a.orders:
            inst = build_ho(rng, r)
            if inst is None:
                rows.append(dict(instance=inst_i, designed_order=r, built=False))
                continue
            vr, status = QG.verified_order(inst)
            hs = grids[r]
            h2 = [QG.hell2(inst, h) for h in hs]
            st, r2t = QG.fit_slope(hs, h2, tail_from)
            sa, r2a = QG.fit_slope(hs, h2, 0)
            rows.append(dict(instance=inst_i, designed_order=r, built=True,
                             verified_order=vr, status=status,
                             order_matches=(vr == r), per_level=inst['per'],
                             block=inst['block'], sigma=inst['sigma'],
                             h_min=hs[-1], h2_min=h2[-1], h2_max=h2[0],
                             slope_tail=st, slope_tail_r2=r2t,
                             slope_full=sa, slope_full_r2=r2a,
                             dev_tail=(None if (st is None or vr is None) else st - 2 * vr),
                             dev_full=(None if (sa is None or vr is None) else sa - 2 * vr),
                             reliable=bool(r2t is not None and r2t >= R2_MIN),
                             h2_curve=h2))
        if (inst_i + 1) % 10 == 0:
            print(f'{inst_i+1}/{a.instances}  {time.time()-t0:.0f}s', flush=True)

    built = [x for x in rows if x.get('built')]
    good = [x for x in built if x['reliable'] and x['dev_tail'] is not None]
    by = collections.defaultdict(list)
    for x in good:
        by[x['verified_order']].append(x['dev_tail'])
    dv = [abs(x['dev_tail']) for x in good]
    out = dict(script='EXP_query_highorder.py',
               design='the two-world construction of the main sweep carried to leakage '
                      'orders 4 and 5, on a per-order h grid whose floor is set so the '
                      'predicted H^2 stays above 1e-22 and therefore above the level at '
                      'which double-precision cancellation would dominate; the slope is '
                      'fitted on the lower half of each grid',
               master_seed=MASTER_SEED, orders=a.orders, instances=a.instances,
               target_floor=TARGET_FLOOR, points=POINTS, tail_from=tail_from,
               r2_min=R2_MIN,
               grids={str(r): grids[r] for r in a.orders},
               self_check=dict(mass_residual=sc['mass'], order_verified=sc['order_ok'],
                               order_of=sc['order_of'], quadrature=sc['quad'],
                               passed=bool(ok)),
               cells=len(built), cells_reliable=len(good),
               order_matches=sum(1 for x in built if x.get('order_matches')),
               orders_verified={str(k): len(v) for k, v in sorted(by.items())},
               dev_by_order={str(k): dict(mean=float(np.mean(v)),
                                          max_abs=float(np.max(np.abs(v))))
                             for k, v in sorted(by.items())},
               tail_max_abs_dev=(max(dv) if dv else None),
               tail_rms_dev=(float(np.sqrt(np.mean(np.square(dv)))) if dv else None),
               rows=rows, wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'cells', len(built), 'reliable', len(good),
          'matched', out['order_matches'], 'max|dev|',
          round(out['tail_max_abs_dev'], 4) if dv else None)


if __name__ == '__main__':
    main()
