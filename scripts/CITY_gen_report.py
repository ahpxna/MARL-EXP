#!/usr/bin/env python3
"""GEN report (PROTOCOL_CITY_GEN_20261005).  Rows gen_20261005/conf/<ARM>_<class>_t<t>_<fleet>[_rho<r>]; cube [light, fleet, traffic 750-759]."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as RR  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/gen_20261005'; S = list(range(750, 760)); KK = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))


def full(Rt, a, b, L, FL):
    r = {}
    for k, p in KK:
        c = np.array([[[100 * (Rt[a(t, f)][s][k] / Rt[b(t, f)][s][k] - 1) if p else Rt[a(t, f)][s][k] - Rt[b(t, f)][s][k] for s in S] for f in FL] for t in L])
        r[k] = RR.crossed(c, RR.draws(c.shape))
    return r


def line(n, r):
    return f'  {n}: ' + ' | '.join(f'{k} {v[0]:+.2f} [{v[1][0]:+.2f}, {v[1][1]:+.2f}] (up {v[2]:+.2f})' for k, v in r.items())


if __name__ == '__main__':
    Rt = rows(D / 'conf'); L = (4, 5, 6, 7, 8); out = ['== GEN: generality of the two-sided interface (traffic 750-759, lights t4-t8)']
    for cls, FL in (('rule', ('R8',)), ('r9', ('s2', 's3'))):
        for a in ('TSI2', 'HYB'):
            r = full(Rt, lambda t, f, a=a: f'{a}_{cls}_t{t}_{f}', lambda t, f: f'R_{cls}_t{t}_{f}', L, FL); out.append(line(f'(a) {cls} {a} - R', r))
            if a == 'TSI2':
                out.append(f'  (a) {cls}: TSI2 fuel benefit (upper < 0): {r["fuel_agent"][2] < 0}; all M3 limits: {r["fuel_agent"][2] < 0 and all(r[q][2] < 0.5 for q in ("timeloss", "timeloss_agent", "timeloss_human"))}')
    FL = ('s213', 's313', 's413', 's513')
    for a, b in (('TSI2', 'R'), ('C2Q', 'R'), ('TSI2', 'C2Q')):
        r = full(Rt, lambda t, f, a=a: f'{a}_r10_t{t}_{f}', lambda t, f, b=b: f'{b}_r10_t{t}_{f}', L, FL); out.append(line(f'(b) {a} - {b}', r))
        if (a, b) == ('TSI2', 'C2Q'):
            out.append(f'  (b) STATE FORECASTER NECESSARY: {r["fuel_agent"][2] < 0}')
    for rho in ('0.25', '0.75'):
        r = full(Rt, lambda t, f: f'TSI2_r10_t{t}_{f}_rho{rho}', lambda t, f: f'R_r10_t{t}_{f}_rho{rho}', L, ('s213', 's313')); out.append(line(f'(c) rho {rho} TSI2 - R', r))
        out.append(f'  (c) rho {rho}: fuel benefit (upper < 0): {r["fuel_agent"][2] < 0}; all M3 limits: {r["fuel_agent"][2] < 0 and all(r[q][2] < 0.5 for q in ("timeloss", "timeloss_agent", "timeloss_human"))}')
    F1 = ('F1B_s213_t4', 'F1B_s313_t5', 'F1B_s413_t6', 'F1B_s513_t7')
    r = full(Rt, lambda t, f: f'FT_{F1[FL.index(f)]}', lambda t, f: f'FT_{f}', (0,), FL); out.append(line('(d) FT: F1B - R10 (fleet-first path, old light)', r))
    out.append(f'  (d) FLEET-FIRST SAFE UNDER THE OLD LIGHT: {r["fuel_agent"][2] < 0.5 and r["timeloss_agent"][2] < 0.5}')
    t = '\n'.join(out) + '\n'; (D / 'report_gen.txt').write_text(t); print(t)
