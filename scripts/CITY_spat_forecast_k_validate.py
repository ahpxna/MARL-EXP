#!/usr/bin/env python3
"""Forecast quality of CITY_spat_forecast_k (descriptive; PROTOCOL_CITY_M4_STAGE3 3b): on recorded traces, for every second and every green g
that is not active, the quantile-q forecast ttg to g vs the actual time to g's next onset (the convention of CITY_spat_forecast_k_conv, so a
perfect-duration forecast scores 0).  Prints n, bias (forecast - actual), MAE, median |error|, share within +-1 s and the share early (< -1 s).
Usage (spider): CITY_m4s_run.py scripts/CITY_spat_forecast_k_validate.py <table.json> <q> <npz files>"""
import json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
if __name__ == '__main__':
    T = json.loads(Path(sys.argv[1]).read_text()); q = float(sys.argv[2]); F = FK.ForecastK(T, q); err = []
    for f in sys.argv[3:]:
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
                ph = int(col[i]); t = i + 1
                for g in gs:
                    if ph == g or nxt[g][i] < 0:
                        continue
                    fc = F.ttg(tid, ph, float(S[i, j]), {g})
                    if fc is not None:
                        err.append(fc - ((nxt[g][i] + 1) - t))
    e = np.array(err); r = dict(n=int(len(e)), q=q, bias=float(e.mean()), mae=float(np.abs(e).mean()), med_abs=float(np.median(np.abs(e))),
                                within_1s=float((np.abs(e) <= 1).mean()), early_gt_1s=float((e < -1).mean()), late_gt_1s=float((e > 1).mean()))
    print(json.dumps(r))
