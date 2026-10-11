"""Pooled train x deploy cells: per seed, average gain over the finished K-grid panels where the cell exists; seed bootstrap.
3x3: exactly the wake-2 matrix (research/marl_budget/e3_train_deploy_matrix_20261003/matrix.json, pooled.py rng order).
4x4: matrix.json panels + test D panel 4601 (extra_data.json), the only panel with 4x4 relayMIX."""
import json
import numpy as np
from common import *
MAT = MB / 'e3_train_deploy_matrix_20261003' / 'matrix.json'
ORDER = ['K1', 'K2', 'K3', 'iid']
def cells():
    C = json.loads(MAT.read_text())['cells']; X = json.loads((OUT / 'extra_data.json').read_text())['cells']
    for k, v in X.items():
        g, p, fam, K = k.split('|')[:4]
        if p == '4601':
            C.append(dict(grid=g, panel=4601, top='e3_g4_mix_20261002', fam=fam, K=K, seeds=v['seeds'], per_seed=v['per_seed'], mean=v['mean'], lo=v['lo'], hi=v['hi'], npos=v['npos']))
    return C
def pooled(include_4601=True):
    C = cells() if include_4601 else json.loads(MAT.read_text())['cells']
    rng = np.random.default_rng(2); res = {}
    for grid, fam in sorted({(c['grid'], c['fam']) for c in C}):
        for K in ORDER:
            cs = [c for c in C if c['grid'] == grid and c['fam'] == fam and c['K'] == K]
            if not cs: continue
            per = {}
            for c in cs:
                for s, g in zip(c['seeds'], c['per_seed']): per.setdefault(s, []).append(g)
            S = sorted(per); v = np.array([np.mean(per[s]) for s in S])
            bs = v[rng.integers(0, len(v), (20000, len(v)))].mean(1); lo, hi = np.percentile(bs, [2.5, 97.5])
            res[(grid, fam, K)] = dict(mean=float(v.mean()), lo=float(lo), hi=float(hi), seeds=S, per_seed=v.tolist(), npos=int((v > 0).sum()),
                                       panels=sorted({c['panel'] for c in cs}))
    return res
if __name__ == '__main__':
    a, b = pooled(True), pooled(False)
    for k in sorted(a):
        old = b.get(k); print(k, f"{a[k]['mean']:+.2f} [{a[k]['lo']:+.2f},{a[k]['hi']:+.2f}] panels {a[k]['panels']}" + (f" | matrix.json-only {old['mean']:+.2f}" if old else ' | new'))
