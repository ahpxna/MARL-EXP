#!/usr/bin/env python3
"""TSI-2 confirmation report (PROTOCOL_CITY_TSI2_20261005; written before the panel).  Cube [light t4..t8, fleet index 0..3, traffic 720..739];
crossed bootstrap; PRIMARY at alpha 0.025 one-sided = the two-sided 95 % interval's upper end."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as RR  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/tsi2_20261005'; L = (4, 5, 6, 7, 8); FL = ('s213', 's313', 's413', 's513'); S = list(range(720, 740))
F1B = ('F1B_s213_t4', 'F1B_s313_t5', 'F1B_s413_t6', 'F1B_s513_t7'); KK = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))
nm = lambda a, t, i: f'{a}_t{t}_{FL[i]}' if a != 'F1B' else f'F1B_t{t}_{F1B[i]}'


def full(Rt, a, b):
    r = {}
    for k, p in KK:
        c = np.array([[[100 * (Rt[nm(a, t, i)][s][k] / Rt[nm(b, t, i)][s][k] - 1) if p else Rt[nm(a, t, i)][s][k] - Rt[nm(b, t, i)][s][k] for s in S] for i in range(4)] for t in L])
        pt, ci, up = RR.crossed(c, RR.draws(c.shape)); r[k] = (pt, ci, up)
    return r


if __name__ == '__main__':
    Rt = rows(D / 'conf'); ch = json.load(open(D / 'tune/choice.json'))
    miss = [nm(a, t, i) for a in ('R', 'TSI2', 'HYB', 'ADP2', 'F1B') for t in L for i in range(4) if nm(a, t, i) not in Rt or len(Rt[nm(a, t, i)]) != len(S)]
    out = ['== TSI-2 CONFIRMATION (lights t4-t8 x fleets s213-s513 x traffic 720-739); per-light (A, B): ' + ', '.join(f't{t} ({v["choice"]})' for t, v in ch.items()),
           f'  completeness: {"PASS" if not miss else "FAIL " + str(miss[:6])}']
    res = {}
    for a, b in (('TSI2', 'R'), ('HYB', 'R'), ('ADP2', 'R'), ('F1B', 'R'), ('TSI2', 'HYB'), ('TSI2', 'ADP2'), ('TSI2', 'F1B')):
        res[(a, b)] = full(Rt, a, b); out.append(f'  {a} - {b}: ' + ' | '.join(f'{k} {v[0]:+.2f} [{v[1][0]:+.2f}, {v[1][1]:+.2f}] (up95 {v[2]:+.2f})' for k, v in res[(a, b)].items()))
    tel = {a: np.mean([Rt[nm(a, t, i)][s]['teleports'] for t in L for i in range(4) for s in S]) for a in ('R', 'TSI2')}; unf = {a: np.mean([Rt[nm(a, t, i)][s]['unfinished'] for t in L for i in range(4) for s in S]) for a in ('R', 'TSI2')}
    out.append(f'  teleports per run {tel}; unfinished {unf}')
    v = res[('TSI2', 'R')]; ok = (not miss) and v['fuel_agent'][1][1] < 0 and all(v[q][1][1] < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel['TSI2'] <= tel['R'] + 0.1 and unf['TSI2'] <= unf['R']
    per = {t: (np.mean([100 * (Rt[nm('TSI2', t, i)][s]['fuel_agent'] / Rt[nm('R', t, i)][s]['fuel_agent'] - 1) for i in range(4) for s in S]), np.mean([Rt[nm('TSI2', t, i)][s]['timeloss_agent'] - Rt[nm('R', t, i)][s]['timeloss_agent'] for i in range(4) for s in S])) for t in L}
    out.append('  per light (TSI2 - R): ' + ' | '.join(f't{t} fuel {f:+.2f} aTL {a:+.2f}' for t, (f, a) in per.items()))
    out.append(f'  TSI-2 CONFIRMATION VERDICT (alpha 0.025 one-sided, uses the 97.5 % upper): {"PASS (every M3 limit met)" if ok else "FAIL"}')
    t = '\n'.join(out) + '\n'; (D / 'report_tsi2_confirm.txt').write_text(t); print(t)
