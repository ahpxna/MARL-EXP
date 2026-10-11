#!/usr/bin/env python3
"""N4 DEV report (PROTOCOL_CITY_N4_SERVICE_GATE_20261005; written before the DEV panel).  R from n1_20261005/g4, publish-all = N2q05 rows of
n2_20261005/dev, gated arms in n4_20261005/dev: G_k<k>_<fl>, W_..., H_..., RND_...  Crossed bootstrap over [k, fleet, traffic]."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_n2_report as N  # noqa: E402
import scripts.CITY_n2m_report as M  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'n4_20261005'
if __name__ == '__main__':
    Rt = {**rows(CS / 'n1_20261005/g4'), **rows(CS / 'n2_20261005/dev'), **rows(D / 'dev')}; ch = json.load(open(D / 'sel' / 'choice.json'))
    out = ['== N4 service gate (N2 state forecast q0.5 or unavailable)', f'  SELECT choice: G* {ch["G"]} | Wbest {ch["W"]} | Hbest {ch["H"]} | RND p {ch["p"]}']
    act = {a: np.mean([json.load(open(f))['activation'] for f in (D / 'dev').glob(f'{a}_k*_n4.json')]) for a in ('G', 'W', 'H', 'RND')}; out.append(f'  DEV activation {act}')
    nm = lambda p: (lambda k, f: f'{p}_k{k}_{f}'); res = {}
    for a, b in (('G', 'R'), ('W', 'R'), ('H', 'R'), ('RND', 'R'), ('N2q05', 'R'), ('G', 'N2q05'), ('G', 'RND'), ('G', 'W'), ('G', 'H')):
        res[(a, b)] = M.full(Rt, nm(a), nm(b)); out.append(M.line(f'{a} - {b}', res[(a, b)]))
    tel = {p: np.mean([Rt[f'{p}_k{k}_{f}'][s]['teleports'] for k in N.K for f in N.FL for s in N.S]) for p in ('R', 'G')}; out.append(f'  teleports per run {tel}')
    v = res[('G', 'R')]; cand = v['fuel_agent'][2] < 0 and all(v[q][2] < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel['G'] <= tel['R'] + 0.1
    a, r = res[('G', 'N2q05')], res[('G', 'RND')]
    sup = (a['timeloss_agent'][2] < 0 and a['timeloss_agent'][0] <= -0.5 and a['fuel_agent'][0] <= 1.0) and (r['fuel_agent'][2] < 0 or r['timeloss_agent'][2] < 0)
    out += [f'  N4 CANDIDATE (G* vs R, all M3 limits): {cand}', f'  N4 VERDICT (selection helps): {"SUPPORTED" if sup else "REJECTED"}']
    t = '\n'.join(out) + '\n'; (D / 'report_n4.txt').write_text(t); print(t)
