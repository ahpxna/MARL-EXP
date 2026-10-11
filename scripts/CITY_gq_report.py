#!/usr/bin/env python3
"""GQ report (PROTOCOL_CITY_N4_SERVICE_GATE_20261005 Amendment A1): GQ = N4's G* gate + light adapter q:1:0, vs R / G* / N2+q10."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_n2_report as N  # noqa: E402
import scripts.CITY_n2m_report as M  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'n4_20261005'
if __name__ == '__main__':
    Rt = {**rows(CS / 'n1_20261005/g4'), **rows(CS / 'n2_20261005/dev'), **rows(CS / 'n2m_20261005/dev'), **rows(D / 'dev'), **rows(D / 'gq')}; nm = lambda p: (lambda k, f: f'{p}_k{k}_{f}')
    out = [f'== GQ: gate {json.load(open(D / "sel/choice.json"))["G"]} + light adapter q:1:0']; res = {}
    for a, b in (('GQ', 'R'), ('GQ', 'G'), ('GQ', 'N2q10'), ('G', 'R'), ('N2q10', 'R')):
        res[(a, b)] = M.full(Rt, nm(a), nm(b)); out.append(M.line(f'{a} - {b}', res[(a, b)]))
    tel = {p: np.mean([Rt[f'{p}_k{k}_{f}'][s]['teleports'] for k in N.K for f in N.FL for s in N.S]) for p in ('R', 'GQ')}; out.append(f'  teleports per run {tel}')
    v = res[('GQ', 'R')]; cand = v['fuel_agent'][2] < 0 and all(v[q][2] < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel['GQ'] <= tel['R'] + 0.1
    out.append(f'  GQ CANDIDATE (all M3 limits vs R): {cand}'); t = '\n'.join(out) + '\n'; (D / 'report_gq.txt').write_text(t); print(t)
