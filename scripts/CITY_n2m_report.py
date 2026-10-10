#!/usr/bin/env python3
"""N2M report (PROTOCOL_CITY_N2M_MECHANISM_20261005; written before the panel).  Rows: R / c2 from n1_20261005/g4, N2q05 from
n2_20261005/dev, new rows in n2m_20261005/dev (Rq10 Rq11 N2q10 N2q11 RPsig RPn2 RPc2, and the recordings Rrec_k<k>).  Cube [k 2, fleet 2,
traffic 12], crossed bootstrap (CITY_wave2_report_v2.crossed)."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_n2_report as N  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'n2m_20261005'; F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports', 'unfinished')


def full(Rt, A, B):
    r = {}
    for k, p in N.KK:
        c = N.cube(Rt, A, B, k, p); dr = N.R.draws(c.shape); pt, ci, up = N.R.crossed(c, dr); r[k] = (pt, ci, up)
    return r


def line(nm, r):
    return f'  {nm}: ' + ' | '.join(f'{k} {v[0]:+.2f} [{v[1][0]:+.2f}, {v[1][1]:+.2f}] (up {v[2]:+.2f})' for k, v in r.items())


if __name__ == '__main__':
    Rt = {**rows(CS / 'n1_20261005/g4'), **rows(CS / 'n2_20261005/dev'), **rows(D / 'dev')}; S = N.S; out = ['== N2M: hidden demand (light-input adapter) and feedback (open-loop replay) for the N2 state forecast']
    km1 = all(Rt[f'Rrec_k{k}'][s][q] == Rt[f'R_k{k}_s13'][s][q] for k in N.K for s in S for q in F)
    km2 = all(Rt[f'RPsig_k{k}_{f}'][s][q] == Rt[f'R_k{k}_{f}'][s][q] for k in N.K for f in N.FL for s in S for q in F)
    out += [f'  KM-1 recording == R: {"PASS" if km1 else "FAIL"}', f'  KM-2 sigma* under replay == R: {"PASS" if km2 else "FAIL"}']
    nm = lambda p: (lambda k, f: f'{p}_k{k}_{f}')
    res = {}
    for a, b in (('Rq10', 'R'), ('Rq11', 'R'), ('N2q05', 'R'), ('N2q10', 'R'), ('N2q11', 'R'), ('N2q10', 'N2q05'), ('N2q11', 'N2q05'), ('N2q10', 'Rq10'), ('N2q11', 'Rq11'),
                 ('RPn2', 'RPsig'), ('RPc2', 'RPsig'), ('RPn2', 'N2q05')):
        res[(a, b)] = full(Rt, nm(a), nm(b)); out.append(line(f'{a} - {b}', res[(a, b)]))
    tel = {p: np.mean([Rt[f'{p}_k{k}_{f}'][s]['teleports'] for k in N.K for f in N.FL for s in S]) for p in ('R', 'N2q10', 'N2q11')}
    unf = {p: np.mean([Rt[f'{p}_k{k}_{f}'][s]['unfinished'] for k in N.K for f in N.FL for s in S]) for p in ('R', 'N2q10', 'N2q11')}
    out.append(f'  teleports per run {tel}; unfinished per run {unf}')
    hd = []; cand = []
    for ab in ('q10', 'q11'):
        d = res[(f'N2{ab}', 'N2q05')]; e = res[(f'N2{ab}', f'R{ab}')]; v = res[(f'N2{ab}', 'R')]
        hd.append(d['timeloss_agent'][2] < 0 and d['timeloss_agent'][0] <= -0.5 and e['fuel_agent'][0] <= -2.0)
        cand.append(v['fuel_agent'][2] < 0 and all(v[q][2] < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel[f'N2{ab}'] <= tel['R'] + 0.1 and unf[f'N2{ab}'] <= unf['R'])
    out.append(f'  M-HD VERDICT: {"SUPPORTED" if any(hd) else "REJECTED"} (q10 {hd[0]}, q11 {hd[1]})')
    out.append(f'  CANDIDATE vs R (all M3 limits): q10 {cand[0]}, q11 {cand[1]}')
    o, c = res[('RPn2', 'RPsig')]['timeloss_agent'], res[('N2q05', 'R')]['timeloss_agent']
    fb = 'FEEDBACK-DOMINANT' if (o[2] < 0.5 and c[1][0] > 1.0) else ('FLEET-INTRINSIC' if o[1][0] > 1.0 else 'MIXED')
    out.append(f'  M-FB VERDICT: {fb} (open-loop agent TL {o[0]:+.2f} [{o[1][0]:+.2f}, {o[1][1]:+.2f}]; closed-loop {c[0]:+.2f} [{c[1][0]:+.2f}, {c[1][1]:+.2f}])')
    t = '\n'.join(out) + '\n'; (D / 'report_n2m.txt').write_text(t); print(t)
