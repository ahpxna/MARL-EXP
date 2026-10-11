#!/usr/bin/env python3
"""E14 report (research/marl_budget/PROTOCOL_E3_E12_E14_G3_G6_20261004.md §E14 + E14 freeze 04:04; written 04/10/2026 05:3x EDT after the
queue finished and before any E14 gain was computed).  Confirmation of the post-hoc note "OP beats FT-mix at L5" on fresh seeds 2-9 and the
never-evaluated panel 7601-7664 x headway 8/16.  Gain vs Z as in E3: -(sum_e q_arm / sum_e q_Z - 1) * 100 over the panel episodes, per seed;
old drop = parent (CK1) K1 gain - arm K1 gain.  Two-level crossed bootstrap (seeds x panel episodes resampled together), 2000 draws, rng 0.
  E14-1  OP - FTMIX new-channel (K = 0) gain: CI lower > 0
  E14-2  OP old drop - FTMIX old drop: CI upper < +0.5 (non-inferiority on the old channel)
  E14-3  OP - PCT new gain and old drop: reported
E14 SUPPORTED iff E14-1 and E14-2.  INCOMPLETE on any missing cell or a manifest that is not COMPLETE / PASS."""
import json
from pathlib import Path
import numpy as np

E = Path('research/marl_budget/e3_wave_20261003/e14'); SEEDS = list(range(2, 10)); EPS = [f'seed{t}_load{h}' for t in range(7601, 7665) for h in (8, 16)]


def rows(d, arm):
    mf = d / 'manifest.json'
    if not mf.exists():
        return None
    m = json.loads(mf.read_text())
    if m.get('status') != 'COMPLETE' or m.get('self_check', 'PASS') != 'PASS':
        return None
    r = {x['episode']: x['queue_sum'] for x in json.loads((d / 'rows.json').read_text()) if x['arm'] == arm}
    return r if all(e in r for e in EPS) else None


def main():
    Q = {}; miss = []
    for s in SEEDS:
        z = rows(E / f'Z_s{s}', 'Z')
        if z is None:
            miss.append(('Z', s)); continue
        Q[('Z', s)] = z
        for arm in ('CK1', 'OP', 'FTMIX', 'PCT'):
            for K in (0, 1):
                q = rows(E / f'E_{arm}_s{s}_K{K}', 'PLAIN')
                if q is None:
                    miss.append((arm, s, K))
                else:
                    Q[(arm, s, K)] = q
    out = ['== E14: OP vs FT-mix at L5 (budget 40), seeds 2-9, panel 7601-7664 x 8/16']
    if miss:
        out.append(f'INCOMPLETE {miss[:6]} ({len(miss)})'); (E / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    # per seed x episode arrays
    A = {k: np.array([[Q[(k[0], s, k[1])][e] for e in EPS] for s in SEEDS]) for k in [(a, K) for a in ('CK1', 'OP', 'FTMIX', 'PCT') for K in (0, 1)]}
    Z = np.array([[Q[('Z', s)][e] for e in EPS] for s in SEEDS])

    def gain(q, z):                                                 # per seed ratio-of-sums gain, mean over seeds
        return float(np.mean(-(q.sum(1) / z.sum(1) - 1) * 100))

    def stats(fn):
        rng = np.random.default_rng(0); n, m = Z.shape
        pt = fn(np.arange(n), np.arange(m)); bs = []
        for _ in range(2000):
            i = rng.integers(0, n, n); j = rng.integers(0, m, m); bs.append(fn(i, j))
        return pt, np.percentile(bs, [2.5, 97.5])
    G = lambda arm, K: (lambda i, j: gain(A[(arm, K)][np.ix_(i, j)], Z[np.ix_(i, j)]))
    drop = lambda arm: (lambda i, j: G('CK1', 1)(i, j) - G(arm, 1)(i, j))
    for arm in ('CK1', 'OP', 'FTMIX', 'PCT'):
        n0, c0 = stats(G(arm, 0)); n1, c1 = stats(G(arm, 1))
        out.append(f'  {arm:6s} new-channel gain {n0:+.2f} [{c0[0]:+.2f}, {c0[1]:+.2f}]; old-channel gain {n1:+.2f} [{c1[0]:+.2f}, {c1[1]:+.2f}]'
                   + ('' if arm == 'CK1' else f'; old drop {stats(drop(arm))[0]:+.2f}'))
    p1, c1 = stats(lambda i, j: G('OP', 0)(i, j) - G('FTMIX', 0)(i, j)); e1 = c1[0] > 0
    p2, c2 = stats(lambda i, j: drop('OP')(i, j) - drop('FTMIX')(i, j)); e2 = c2[1] < 0.5
    per_seed = [round(-(A[('OP', 0)][k].sum() / Z[k].sum() - 1) * 100 + (A[('FTMIX', 0)][k].sum() / Z[k].sum() - 1) * 100, 2) for k in range(len(SEEDS))]
    out.append(f'E14-1 OP - FTMIX new gain {p1:+.2f} [{c1[0]:+.2f}, {c1[1]:+.2f}] (per seed {per_seed}) -> {"SUPPORTED" if e1 else "NOT SUPPORTED"}')
    out.append(f'E14-2 OP old drop - FTMIX old drop {p2:+.2f} [{c2[0]:+.2f}, {c2[1]:+.2f}] (upper < +0.5) -> {"SUPPORTED" if e2 else "NOT SUPPORTED"}')
    p3, c3 = stats(lambda i, j: G('OP', 0)(i, j) - G('PCT', 0)(i, j)); p4, c4 = stats(lambda i, j: drop('OP')(i, j) - drop('PCT')(i, j))
    out.append(f'E14-3 (reported) OP - PCT new gain {p3:+.2f} [{c3[0]:+.2f}, {c3[1]:+.2f}]; old drop difference {p4:+.2f} [{c4[0]:+.2f}, {c4[1]:+.2f}]')
    out.append(f"E14 {'SUPPORTED: OP becomes the strongest update-permitted reference' if e1 and e2 else 'NOT SUPPORTED: the L-322 note stays post hoc; FT-mix / PCT remain the references'}")
    (E / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    main()
