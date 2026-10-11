#!/usr/bin/env python3
"""N8 report (PROTOCOL_CITY_N8_CDC_20261005; written before the DEV panel).  DEV 600-611; R rows from n1_20261005/g4 (R_k<k>_<fl>); CDC rows
in n8_20261005/dev: CDC<v>_<fl> (theta = the final CEM mean of variant v, program SPaT), CDC<v>sig_<fl> (same light, fleet without SPaT),
FTp_<fl> / FTsig_<fl> (the static FT program).  CDC rows do not depend on k: cube [k 2, fleet 2, traffic 12] pairs each with R_k."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_n2_report as N  # noqa: E402
import scripts.CITY_n2m_report as M  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'n8_20261005'
if __name__ == '__main__':
    Rt = {**rows(CS / 'n1_20261005/g4'), **rows(D / 'dev')}; out = ['== N8 committed-duration controller (predictable splits; exact program SPaT) vs R = RL-H + no SPaT']
    for v in ('m3', 'city'):
        c = json.loads((D / f'cem/{v}/cem_{v}.json').read_text()); out.append(f'  CEM {v}: final mean theta {np.round(c["mean"], 3).tolist()} | best TRAIN J {c["best"]["J"]:+.3f}')
    k8 = [json.loads(f.read_text()) for f in sorted((D / 'dev').glob('*_n8.json'))]
    out.append(f'  KN8-1 SPaT exactness under CDC: {sum(x["mism"] for x in k8 if x["light"].startswith("CDC") and x["spat"] == "program")} mismatches in {sum(x["checked"] for x in k8 if x["light"].startswith("CDC") and x["spat"] == "program")} checked queries')
    for x in k8:
        if x['light'].startswith('CDC'):
            out.append(f'     {x["light"][:40]} spat {x["spat"]}: green duration mean {x["dur_mean"]:.1f} p90 {x["dur_p90"]:.1f} (n {x["n_greens"]})')
    R = lambda k, f: f'R_k{k}_{f}'; res = {}
    for nm in ('CDCm3', 'CDCm3sig', 'CDCcity', 'CDCcitysig', 'FTp', 'FTsig'):
        res[nm] = M.full(Rt, lambda k, f, nm=nm: f'{nm}_{f}', R); out.append(M.line(f'{nm} vs R', res[nm]))
    for a, b in (('CDCm3', 'CDCm3sig'), ('CDCcity', 'CDCcitysig'), ('FTp', 'FTsig')):
        out.append(M.line(f'{a} - {b} (fleet contribution under that light)', M.full(Rt, lambda k, f, a=a: f'{a}_{f}', lambda k, f, b=b: f'{b}_{f}')))
    tel = {nm: np.mean([Rt[f'{nm}_{f}'][s]['teleports'] for f in N.FL for s in N.S]) for nm in ('CDCm3', 'CDCcity', 'FTp')}; tel['R'] = np.mean([Rt[f'R_k{k}_{f}'][s]['teleports'] for k in N.K for f in N.FL for s in N.S])
    out.append(f'  teleports per run {tel}')
    for v in ('m3', 'city'):
        r = res[f'CDC{v}']; cand = r['fuel_agent'][2] < 0 and all(r[q][2] < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel[f'CDC{v}'] <= tel['R'] + 0.1
        out.append(f'  N8 CANDIDATE ({v}; all M3 limits vs R): {cand}')
    t = '\n'.join(out) + '\n'; (D / 'report_n8.txt').write_text(t); print(t)
