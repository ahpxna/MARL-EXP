#!/usr/bin/env python3
"""N2 report (PROTOCOL_CITY_N2_STATE_FORECAST_20261005; written before the N2 panel).  Offline: n2_20261005/model/n2_k<k>_compare.json.
Endpoints DEV 600-611, cube [k 2, fleet 2, traffic 12]: R and c2 q0.1 rows from n1_20261005/g4 (R_k<k>_<fl>, N1all_k<k>_<fl>); new rows in
n2_20261005/dev: C2q05_k<k>_<fl> (c2 at q 0.5), N2q01 / N2q05 (state model).  Decision (registered): FORECAST BETTER iff the state model's
query-weighted MAE is >= 10 % below age-only at both q for both k; N2 SUPPORTED iff, at some q, state - c2 (same q) agent fuel upper < 0 with
agent TL upper < +0.5 (paired; two q -> reported as 2 looks).  Each arm vs R is reported (a candidate if it meets every M3 limit)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'n2_20261005'; S = list(range(600, 612)); K = (0, 1); FL = ('s13', 's113')
KK = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))


def cube(Rt, A, B, key, pct):
    return np.array([[[100 * (Rt[A(k, f)][s][key] / Rt[B(k, f)][s][key] - 1) if pct else Rt[A(k, f)][s][key] - Rt[B(k, f)][s][key] for s in S] for f in FL] for k in K])


def block(out, Rt, nm, A, B):
    r = {}
    for k, p in KK:
        c = cube(Rt, A, B, k, p); dr = R.draws(c.shape); pt, ci, up = R.crossed(c, dr); r[k] = (pt, up)
    out.append(f'  {nm}: ' + ' | '.join(f'{k} {r[k][0]:+.2f} (up {r[k][1]:+.2f})' for k, _ in KK)); return r


if __name__ == '__main__':
    out = ['== N2 state-conditioned direct TTG forecast vs age-only (same data)']; better = []
    for k in K:
        c = json.load(open(D / f'model/n2_k{k}_compare.json'))['compare']
        for q in ('q0.1', 'q0.5'):
            a, s = c[q]['age_only']['query_weighted'], c[q]['state_model']['query_weighted']; better.append(s['mae'] <= 0.9 * a['mae'])
            out.append(f'  offline k{k} {q} query-weighted: age-only MAE {a["mae"]:.2f} bias {a["bias"]:+.2f} ±1s {a["within_1s"]:.2f} | state MAE {s["mae"]:.2f} bias {s["bias"]:+.2f} ±1s {s["within_1s"]:.2f}')
    fb = all(better); out.append(f'  FORECAST BETTER (>= 10 % lower query-weighted MAE, both q, both k): {"YES" if fb else "NO"}')
    Rt = {**rows(CS / 'n1_20261005/g4'), **rows(D / 'dev')}; Rb = lambda k, f: f'R_k{k}_{f}'
    arms = {'c2 q0.1': lambda k, f: f'N1all_k{k}_{f}', 'c2 q0.5': lambda k, f: f'C2q05_k{k}_{f}', 'state q0.1': lambda k, f: f'N2q01_k{k}_{f}', 'state q0.5': lambda k, f: f'N2q05_k{k}_{f}'}
    for nm, A in arms.items():
        block(out, Rt, f'{nm} vs R', A, Rb)
    sup = []
    for q, a, b in (('0.1', 'state q0.1', 'c2 q0.1'), ('0.5', 'state q0.5', 'c2 q0.5')):
        r = block(out, Rt, f'{a} - {b} (paired)', arms[a], arms[b]); sup.append(r['fuel_agent'][1] < 0 and r['timeloss_agent'][1] < 0.5)
    out.append(f'  N2 VERDICT: {"SUPPORTED" if any(sup) else ("REJECTED: better forecast, no endpoint gain" if fb else "REJECTED")}')
    t = '\n'.join(out) + '\n'; (D / 'report_n2.txt').write_text(t); print(t)
