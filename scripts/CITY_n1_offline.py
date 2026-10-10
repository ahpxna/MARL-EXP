#!/usr/bin/env python3
"""N1 offline: forecast error by SUPPORT state (local / pool / none / program) for every second and every non-active green on recorded traces,
quantile q of the given table (grid4 old-format tables are augmented as c2; forecast-K tables as is).  Error = forecast ttg - actual time to that
green's next onset (CITY_spat_forecast_k_validate convention).  Usage: CITY_n1_offline.py <table> <q> <grid4|spider> <npz files>"""
import json, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
if __name__ == '__main__':
    tb, q, net = sys.argv[1], float(sys.argv[2]), sys.argv[3]
    if net == 'spider':
        import scripts.CITY_m4s_run  # noqa: F401
    import scripts.CITY_spat_forecast_n1 as N1
    import scripts.CITY_spat_forecast_c2 as C2
    T = json.loads(Path(tb).read_text()); T = C2.augment(T) if 'ng' not in T else T; F = N1.ForecastKX(T, q); E = defaultdict(list)
    for f in sys.argv[4:]:
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S = z['phases'], z['spent']
        for j, tid in enumerate(ids):
            if tid not in F.G:
                continue
            gs = F.G[tid]; col = P[:, j]; nxt = {g: np.full(len(col), -1) for g in gs}
            for g in gs:
                last = -1
                for i in range(len(col) - 1, -1, -1):
                    if col[i] == g and (i == 0 or col[i - 1] != g):
                        last = i
                    nxt[g][i] = last
            for i in range(len(col)):
                ph = int(col[i])
                for g in gs:
                    if ph == g or nxt[g][i] < 0:
                        continue
                    F.last = 'program'; fc = F.ttg(tid, ph, float(S[i, j]), {g})
                    if fc is not None:
                        E[F.last].append(fc - (nxt[g][i] - i))
    out = {}
    for k, v in E.items():
        e = np.array(v); out[k] = dict(n=int(len(e)), share=0.0, bias=float(e.mean()), mae=float(np.abs(e).mean()), within_1s=float((np.abs(e) <= 1).mean()), early_gt_5s=float((e < -5).mean()))
    n = sum(x['n'] for x in out.values())
    for k in out:
        out[k]['share'] = out[k]['n'] / max(1, n)
    print(json.dumps(dict(table=tb, q=q, net=net, by_support=out)))
