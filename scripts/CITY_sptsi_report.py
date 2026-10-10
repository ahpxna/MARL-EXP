#!/usr/bin/env python3
"""Spider TSI confirmation report (PROTOCOL_CITY_SPIDER_TSI_20261005; written before the panel).  Cube [light 2, fleet 1, traffic 1110-1129]."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as RR  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
import os
D = Path(__file__).resolve().parents[1] / 'research/city_sim/sptsi_20261005'; L = (11, 111); V2 = os.environ.get('SPTSI_V2') == '1'
S = list(range(1130, 1150)) if V2 else list(range(1110, 1130)); CD, TD, A1 = ('conf2', 'tune2', 'TSIK2') if V2 else ('conf', 'tune', 'TSIK'); A2 = 'ADPK2' if V2 else 'ADPK'
KK = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))


def full(Rt, a, b):
    r = {}
    for k, p in KK:
        c = np.array([[[100 * (Rt[f'{a}_{t}'][s][k] / Rt[f'{b}_{t}'][s][k] - 1) if p else Rt[f'{a}_{t}'][s][k] - Rt[f'{b}_{t}'][s][k] for s in S]] for t in L])
        r[k] = RR.crossed(c, RR.draws(c.shape))
    return r


if __name__ == '__main__':
    Rt = rows(D / CD); ch = json.load(open(D / TD / 'choice.json'))
    miss = [f'{a}_{t}' for a in ('R', A1, 'HYBK', A2) for t in L if f'{a}_{t}' not in Rt or len(Rt[f'{a}_{t}']) != len(S)]
    out = ['== SPIDER TSI (second network; lights RLK11 / RLK111 x rule fleet x fresh traffic 1110-1129); per-light (A, B): ' + ', '.join(f'RLK{k} ({v["choice"]})' for k, v in ch.items()),
           f'  completeness: {"PASS" if not miss else "FAIL " + str(miss)}']
    res = {}
    for a, b in ((A1, 'R'), ('HYBK', 'R'), (A2, 'R'), (A1, 'HYBK'), (A1, A2)):
        res[(a, b)] = full(Rt, a, b); out.append(f'  {a} - {b}: ' + ' | '.join(f'{k} {v[0]:+.2f} [{v[1][0]:+.2f}, {v[1][1]:+.2f}] (up {v[2]:+.2f})' for k, v in res[(a, b)].items()))
    tel = {a: np.mean([Rt[f'{a}_{t}'][s]['teleports'] for t in L for s in S]) for a in ('R', A1)}; out.append(f'  teleports per run {tel}')
    v = res[(A1, 'R')]; up = (lambda x: x[1][1]) if V2 else (lambda x: x[2]); ok = (not miss) and up(v['fuel_agent']) < 0 and all(up(v[q]) < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel[A1] <= tel['R'] + 0.1
    out.append(f'  SECOND-SETTING REPLICATION VERDICT ({"attempt 2, alpha 0.025" if V2 else "attempt 1, alpha 0.05"} one-sided): {"PASS (every M3 limit met)" if ok else "FAIL"}')
    t = '\n'.join(out) + '\n'; (D / ('report_sptsi2.txt' if V2 else 'report_sptsi.txt')).write_text(t); print(t)
