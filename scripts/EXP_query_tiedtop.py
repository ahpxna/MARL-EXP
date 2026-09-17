"""QUERY: how near to vanishing can the order-r coefficient get?

The paper calls this its most likely point of failure. Theorem thm:nonvanish
needs the largest level carrying a non-zero coefficient to be STRICTLY largest:
the proof factors out the Gaussian at that level, and every lower level then
carries a ratio exp(-(v*-v)(y-(v+v*)/2)/sigma^2) that decays as y -> +infinity.
When the gap v* - v closes, that decay disappears and the argument gives 0 = 0.
What the paper does not say -- because it cannot be read off the proof -- is
whether the conclusion is still true when the hypothesis is removed, or whether
it fails, and how.

That question has a sharp refutable form. Delta_r is identically zero, or it is
not; and how close it comes to zero as the gap closes is measurable. So this
sweeps the top-level gap down toward zero and measures

    ||Delta_r||  /  (|c_{v*}| ||H_r phi||),

the size of the assembled coefficient relative to the size of the single term it
is built from. If that ratio stays bounded away from zero, the strict-largest
hypothesis is removable and the theorem is weaker than it needs to be. If it goes
to zero, the hypothesis is essential, and the rate says how essential.

The structure predicts an answer worth checking against. In the two-world
construction the exchange moves the same weighted moment out of one level and
into another, so the two contributing coefficients are equal and opposite. Two
equal and opposite terms at a separation delta differ, to first order, by delta
times the derivative of the term -- so the ratio should fall LINEARLY in the gap
rather than jumping. A linear fall means the theorem's hypothesis is exactly the
right one and cannot simply be dropped; it also means nothing pathological
happens at a tie, which is worth knowing before anyone tries to prove the tied
case.

The gap is swept by construction rather than by luck: the two exchanged levels
are placed at a chosen separation, and sigma is fixed, so gap/sigma is the
independent variable.

Self-check: at a separation the main sweep also produces, the coefficients must
come out equal and opposite to machine precision, and the verified leakage order
must equal the designed one. The sweep is not reported otherwise.
"""
import json
import time
import math
import argparse
import os
import sys
import importlib.util
from pathlib import Path

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as _P

spec = importlib.util.spec_from_file_location('qg', 'scripts/EXP_query_generalize.py')
QG = importlib.util.module_from_spec(spec)
spec.loader.exec_module(QG)

MASTER_SEED = 24601
GAPS = [2.0, 1.0, 0.5, 0.25, 0.125, 6e-2, 3e-2, 1.5e-2, 8e-3, 4e-3, 2e-3, 1e-3]
ORDERS = (1, 2, 3)


def hermite(n, u):
    h0, h1 = np.ones_like(u), u
    if n == 0:
        return h0
    for k in range(1, n):
        h0, h1 = h1, u * h1 - k * h0
    return h1


def build_gap(rng, r, gap, sigma):
    """Two worlds whose two exchanged levels sit exactly `gap` apart."""
    A, B = QG.prouhet(r)
    span = float(max(max(A), max(B))) or 1.0
    A = [x / span for x in A]
    B = [x / span for x in B]
    blk = len(A)
    per = max(4, blk)
    levels = [0.0, gap]
    n = 2 * per
    lev_of = [levels[i // per] for i in range(n)]
    a_idx = list(range(blk))
    b_idx = [per + k for k in range(blk)]
    block = set(a_idx) | set(b_idx)

    mass = 0.5
    w_blk = mass / (2 * blk)
    rest = [i for i in range(n) if i not in block]
    pi = np.zeros(n)
    for i in block:
        pi[i] = w_blk
    pi[rest] = rng.dirichlet(np.ones(len(rest)) * 3.0) * (1.0 - mass)
    pi = pi / pi.sum()

    alpha = float(rng.uniform(0.7, 1.4)); beta = float(rng.uniform(-0.5, 0.5))
    g = np.zeros(n)
    g[rest] = rng.normal(0.0, 1.0, size=len(rest))
    for k in range(blk):
        g[a_idx[k]] = alpha * A[k] + beta
        g[b_idx[k]] = alpha * B[k] + beta

    f0 = list(lev_of); f1 = list(lev_of)
    for k in range(blk):
        f1[a_idx[k]] = lev_of[b_idx[k]]
        f1[b_idx[k]] = lev_of[a_idx[k]]
    return dict(pi=pi, g=g, f0=f0, f1=f1, levels=levels, sigma=sigma,
                per=per, nlev=2, block=blk)


def coefficients(inst, r):
    lv = sorted(set(inst['f0']))
    out = {}
    for v in lv:
        m0 = sum(inst['pi'][i] * inst['g'][i] ** r
                 for i in range(len(inst['g'])) if inst['f0'][i] == v)
        m1 = sum(inst['pi'][i] * inst['g'][i] ** r
                 for i in range(len(inst['g'])) if inst['f1'][i] == v)
        out[v] = m0 - m1
    return out


def assembled_ratio(inst, r, points=40001):
    """||Delta_r|| over the size of the single largest term, both in L2."""
    c = coefficients(inst, r)
    s = inst['sigma']
    lv = sorted(c)
    span = max(abs(v) for v in lv) + 10 * s
    y = np.linspace(-span, span, points)
    tot = np.zeros_like(y)
    biggest = 0.0
    for v in lv:
        u = (y - v) / s
        term = c[v] * hermite(r, u) * np.exp(-0.5 * u * u) / (s * math.sqrt(2 * math.pi))
        tot += term
        biggest = max(biggest, float(np.sqrt(np.trapezoid(term * term, y))))
    norm = float(np.sqrt(np.trapezoid(tot * tot, y)))
    return norm, biggest, (norm / biggest if biggest > 0 else None)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--instances', type=int, default=60)
    ap.add_argument('--sigma', type=float, default=1.0)
    a = ap.parse_args()
    rng = np.random.default_rng(MASTER_SEED)
    t0 = time.time()

    # ---------------- self-check ----------------------------------------
    chk = np.random.default_rng(MASTER_SEED + 1)
    worst_opp, order_ok, order_of = 0.0, 0, 0
    for r in ORDERS:
        for _ in range(4):
            inst = build_gap(chk, r, 1.0, a.sigma)
            c = coefficients(inst, r)
            vals = [c[v] for v in sorted(c)]
            scale = max(abs(x) for x in vals) or 1.0
            worst_opp = max(worst_opp, abs(sum(vals)) / scale)
            vr, _ = QG.verified_order(inst)
            order_of += 1; order_ok += int(vr == r)
    ok = worst_opp < 1e-12 and order_ok == order_of
    print(f'self-check: coefficients equal and opposite to {worst_opp:.1e}; '
          f'order verified {order_ok}/{order_of} -> {"PASS" if ok else "FAIL"}',
          flush=True)
    if not ok:
        raise SystemExit('self-check failed; sweep not reported')

    rows = []
    for r in ORDERS:
        for gap in GAPS:
            for k in range(a.instances):
                inst = build_gap(rng, r, gap, a.sigma)
                vr, status = QG.verified_order(inst)
                norm, biggest, ratio = assembled_ratio(inst, r)
                rows.append(dict(order=r, gap=gap, gap_over_sigma=gap / a.sigma,
                                 verified_order=vr, status=status,
                                 norm=norm, largest_term=biggest, ratio=ratio,
                                 vanishes=bool(ratio is not None and ratio < 1e-12)))
        print(f'order {r} done  {time.time()-t0:.0f}s', flush=True)

    vanished = [x for x in rows if x['vanishes']]
    import collections
    bygap = collections.defaultdict(list)
    for x in rows:
        if x['ratio'] is not None:
            bygap[(x['order'], x['gap'])].append(x['ratio'])
    summary = {f'{o}|{g}': dict(median=float(np.median(v)), min=float(np.min(v)),
                                max=float(np.max(v)), n=len(v))
               for (o, g), v in sorted(bygap.items())}

    # rate: fit log(ratio) against log(gap) on the small-gap tail, per order
    rates = {}
    for o in ORDERS:
        gs = sorted(g for (oo, g) in bygap if oo == o)
        tail = [g for g in gs if g <= 0.125]
        if len(tail) >= 4:
            x = np.log(np.array(tail))
            y = np.log(np.array([np.median(bygap[(o, g)]) for g in tail]))
            A_ = np.vstack([x, np.ones_like(x)]).T
            sol, *_ = np.linalg.lstsq(A_, y, rcond=None)
            rates[str(o)] = dict(slope=float(sol[0]), intercept=float(sol[1]))

    out = dict(provenance=_P.stamp(__file__), script='EXP_query_tiedtop.py',
               design='the top-level gap is swept by construction from two sigma down to '
                      'one thousandth of a sigma, at three leakage orders, and the '
                      'assembled order-r coefficient is measured in L2 against the single '
                      'largest term it is built from',
               master_seed=MASTER_SEED, gaps=GAPS, orders=list(ORDERS),
               sigma=a.sigma, instances_per_cell=a.instances,
               self_check=dict(coefficients_sum_to_zero=worst_opp,
                               order_verified=order_ok, order_of=order_of,
                               passed=bool(ok)),
               cells=len(rows), cells_vanishing=len(vanished),
               summary=summary, decay_rates=rates, rows=rows,
               wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'cells', len(rows), 'vanishing', len(vanished),
          'decay slopes', {k: round(v['slope'], 3) for k, v in rates.items()})


if __name__ == '__main__':
    main()
