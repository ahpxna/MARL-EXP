#!/usr/bin/env python3
"""TSI confirmation report (PROTOCOL_CITY_TSI_20261005; written before the panel).  Rows tsi_20261005/conf/<ARM>_t<t>_<fl>, ARM in R TSI HYB ADP;
cube [light t4..t8, fleet s213..s513, traffic 700..719]; crossed bootstrap (2000 draws); one-sided 95 % upper = R.crossed's third value."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as RR  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'tsi_20261005'; L = (4, 5, 6, 7, 8); FL = ('s213', 's313', 's413', 's513'); S = list(range(700, 720))
KK = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))


def full(Rt, a, b):
    r = {}
    for k, p in KK:
        c = np.array([[[100 * (Rt[f'{a}_t{t}_{f}'][s][k] / Rt[f'{b}_t{t}_{f}'][s][k] - 1) if p else Rt[f'{a}_t{t}_{f}'][s][k] - Rt[f'{b}_t{t}_{f}'][s][k] for s in S] for f in FL] for t in L])
        pt, ci, up = RR.crossed(c, RR.draws(c.shape)); r[k] = (pt, ci, up)
    return r


if __name__ == '__main__':
    Rt = rows(D / 'conf'); ch = json.load(open(D / 'sel/choice.json'))['choice']; var = json.load(open(D / 'sel/variant.json'))['variant']
    miss = [f'{a}_t{t}_{f}' for a in ('R', 'TSI', 'HYB', 'ADP') for t in L for f in FL if f'{a}_t{t}_{f}' not in Rt or len(Rt[f'{a}_t{t}_{f}']) != len(S)]
    out = [f'== TSI CONFIRMATION (lights t4-t8 x fleets s213-s513 x traffic 700-719); adapter (A, B) = ({ch}); forecaster variant {var}', f'  completeness: {"PASS" if not miss else "FAIL " + str(miss[:6])}']
    res = {}
    for a, b in (('TSI', 'R'), ('HYB', 'R'), ('ADP', 'R'), ('TSI', 'HYB'), ('TSI', 'ADP')):
        res[(a, b)] = full(Rt, a, b); out.append(f'  {a} - {b}: ' + ' | '.join(f'{k} {v[0]:+.2f} [{v[1][0]:+.2f}, {v[1][1]:+.2f}] (up {v[2]:+.2f})' for k, v in res[(a, b)].items()))
    tel = {a: np.mean([Rt[f'{a}_t{t}_{f}'][s]['teleports'] for t in L for f in FL for s in S]) for a in ('R', 'TSI')}; unf = {a: np.mean([Rt[f'{a}_t{t}_{f}'][s]['unfinished'] for t in L for f in FL for s in S]) for a in ('R', 'TSI')}
    out.append(f'  teleports per run {tel}; unfinished {unf}')
    v = res[('TSI', 'R')]; ok = (not miss) and v['fuel_agent'][2] < 0 and all(v[q][2] < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel['TSI'] <= tel['R'] + 0.1 and unf['TSI'] <= unf['R']
    per = {t: {k: float(np.mean([100 * (Rt[f'TSI_t{t}_{f}'][s]['fuel_agent'] / Rt[f'R_t{t}_{f}'][s]['fuel_agent'] - 1) if k == 'fuel_agent' else Rt[f'TSI_t{t}_{f}'][s][k] - Rt[f'R_t{t}_{f}'][s][k] for f in FL for s in S])) for k in ('fuel_agent', 'timeloss_agent')} for t in L}
    out.append(f'  per light (TSI - R): ' + ' | '.join(f't{t} fuel {p["fuel_agent"]:+.2f} aTL {p["timeloss_agent"]:+.2f}' for t, p in per.items()))
    out.append(f'  TSI CONFIRMATION VERDICT: {"PASS (every M3 limit met)" if ok else "FAIL"}')
    t = '\n'.join(out) + '\n'; (D / 'report_tsi_confirm.txt').write_text(t); print(t)
