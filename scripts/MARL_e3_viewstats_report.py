#!/usr/bin/env python3
"""Report of PROTOCOL_E3_VIEW_OOD_20261001.md (EXPLORATORY; written 01/10/2026 12:21:24 EDT before the probe output was read)."""
from __future__ import annotations
import json
from collections import Counter
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); D = M / 'e3_viewstats_20261001'; SEEDS = range(10); KS = (0, 1, 2, 3)
NAME = {0: 'iid', 1: 'K=1', 2: 'K=2', 3: 'K=3'}


def tv(a, b):
    keys = set(a) | set(b); na, nb = sum(a.values()), sum(b.values())
    return 0.5 * sum(abs(a.get(k, 0) / na - b.get(k, 0) / nb) for k in keys)


def main():
    F = {}
    for K in KS:
        parts = []
        for s in SEEDS:
            d = D / f's{s}_K{K}'
            if not (d / 'manifest.json').exists():
                print('INCOMPLETE', d.name); return
            parts.append(dict(np.load(d / 'flags.npz')))
        F[K] = {k: np.concatenate([p[k] for p in parts]) for k in parts[0] if k != 'age_hist'}
        F[K]['age_hist'] = sum(p['age_hist'] for p in parts)
    for K in KS:
        f = F[K]; f['cov'] = (f['n_fresh'] + f['n_relay']) / f['n_nbr']; f['never'] = f['n_nbr'] - f['n_fresh'] - f['n_relay']
        f['stale_frac'] = np.where(f['n_fresh'] + f['n_relay'] > 0, f['n_stale'] / np.maximum(f['n_fresh'] + f['n_relay'], 1), 0.0)
        f['flip'] = f['zok'] & ~f['protoS']
    L = ['regime | fresh | relay | coverage | never-heard | stale | stale frac | max age p50/p90/p99 | relayed age p50/p90 | fresh by distance 1/2/3/4 | flip_Z']
    for K in KS:
        f = F[K]; h = F[K]['age_hist'][1]; c = np.cumsum(h) / h.sum(); q = lambda p: int(np.searchsorted(c, p))
        L.append(f'{NAME[K]} | {f["n_fresh"].mean():.2f} | {f["n_relay"].mean():.2f} | {f["cov"].mean():.3f} | {f["never"].mean():.2f} | '
                 f'{f["n_stale"].mean():.2f} | {f["stale_frac"].mean():.3f} | {" / ".join(str(int(v)) for v in np.percentile(f["max_age"], [50, 90, 99]))} | '
                 f'{q(0.5)} / {q(0.9)} | {" / ".join(f"{f[k].mean():.2f}" for k in ("fd1", "fd2", "fd3", "fd4"))} | {f["flip"].mean():.3f}')
    L.append('TV distance from iid (marginals):')
    out = {}
    for K in (1, 2, 3):
        row = {k: tv(Counter(F[K][k].tolist()), Counter(F[0][k].tolist())) for k in ('n_fresh', 'n_relay', 'never', 'n_stale', 'max_age')}
        out[NAME[K]] = row; L.append(f'  {NAME[K]}: ' + ' '.join(f'{k} {v:.3f}' for k, v in row.items()))
    V1 = all(out['K=1'][k] >= out['K=2'][k] >= out['K=3'][k] for k in out['K=1'])
    ref = Counter(zip(F[0]['n_fresh'].tolist(), F[0]['n_stale'].tolist(), F[0]['max_age'].tolist())); n0 = sum(ref.values())
    share = {}
    for K in (1, 2, 3):
        cells = list(zip(F[K]['n_fresh'].tolist(), F[K]['n_stale'].tolist(), F[K]['max_age'].tolist()))
        outside = np.array([ref.get(c, 0) / n0 < 1e-3 for c in cells]); share[K] = float(outside.mean())
        fl = F[K]['flip']
        L.append(f'  {NAME[K]}: share outside iid support (freq < 0.1 %) {share[K]:.3f}; flip_Z outside {fl[outside].mean() if outside.any() else float("nan"):.3f} '
                 f'vs inside {fl[~outside].mean() if (~outside).any() else float("nan"):.3f}')
    V2 = share[1] > 0.5 and share[3] < 0.1
    f = F[1]; L.append('K=1 flip_Z by stale count: ' + ' '.join(f'{v}:{f["flip"][f["n_stale"] == v].mean():.3f}(n={int((f["n_stale"] == v).sum())})'
                                                           for v in sorted(set(f['n_stale'].tolist()))))
    L.append('K=1 flip_Z by max age: ' + ' '.join(f'{v}:{f["flip"][f["max_age"] == v].mean():.3f}(n={int((f["max_age"] == v).sum())})'
                                                  for v in sorted(set(f['max_age'].tolist()))))
    L.append('iid flip_Z by fresh count: ' + ' '.join(f'{v}:{F[0]["flip"][F[0]["n_fresh"] == v].mean():.3f}(n={int((F[0]["n_fresh"] == v).sum())})'
                                                      for v in sorted(set(F[0]['n_fresh'].tolist()))))
    L += [f'V1 TV from iid decreasing in K for every marginal: {V1}', f'V2 support share K=1 > 0.5 and K=3 < 0.1: {V2} ({share[1]:.3f}, {share[3]:.3f})']
    text = '\n'.join(L); print(text)
    (M / 'e3_viewstats_report_20261001.json').write_text(json.dumps(dict(tv=out, outside_share=share, V1=bool(V1), V2=bool(V2)), indent=1))
    (M / 'e3_viewstats_report_20261001.txt').write_text('EXPLORATORY\n' + text + '\n')


if __name__ == '__main__':
    main()
