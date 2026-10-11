#!/usr/bin/env python3
"""N1 report (PROTOCOL_CITY_N1_TAIL_SUPPORT_20261005; written before the N1 panel).  grid4 dir n1_20261005/g4: R_k<k>_<fl> (no SPaT), N1<mode>_k<k>_<fl>
(mode all / tail / strict; RL-H:k, frozen R10 fleet, closed-loop prep table, q 0.1), DEV 600-611; cube [k 2, fleet 2, traffic 12], R.crossed.
spider dir n1_20261005/sp: N1<mode>_<k> (rule, RLK, fkcl table q 0.1, DEV 100-109) with R_<k> / Fq0.1_<k> from m4 spider s3b/dev.
Decision: N1 SUPPORTED iff tail exposure (share of fleet forecast queries with support 'none') >= 1 % AND tail - all agent fuel upper < 0 in a
setting; REJECTED iff exposure < 1 % or the paired effect is not shown in either setting.  Each arm vs R is reported (a win over R = a baseline fix)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'n1_20261005'; S = list(range(600, 612)); K = (0, 1); FL = ('s13', 's113')
KK = (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False))


def ci(c):
    dr = R.draws(c.shape); p, c2, up = R.crossed(c, dr); return f'{p:+.2f} [{c2[0]:+.2f}, {c2[1]:+.2f}] (up {up:+.2f})', up


def cube(Rt, A, B, key, pct, seeds, ks, fls):
    return np.array([[[100 * (Rt[A(k, f)][s][key] / Rt[B(k, f)][s][key] - 1) if pct else Rt[A(k, f)][s][key] - Rt[B(k, f)][s][key] for s in seeds] for f in fls] for k in ks])


def block(out, Rt, nm, A, B, seeds, ks, fls):
    r = {k: ci(cube(Rt, A, B, k, p, seeds, ks, fls)) for k, p in KK}
    out.append(f'  {nm}: agent fuel % {r["fuel_agent"][0]} | city TL {r["timeloss"][0]} | agent TL {r["timeloss_agent"][0]} | human TL {r["timeloss_human"][0]}'); return r


def exposure(paths):
    C = {}
    for p in paths:
        for k, v in json.loads(Path(p).read_text())['counts'].items():
            C[k] = C.get(k, 0) + v
    n = sum(v for k, v in C.items() if k in ('local', 'pool', 'none', 'program')); return {k: C.get(k, 0) / max(1, n) for k in ('local', 'pool', 'none', 'program')}, C


if __name__ == '__main__':
    out = ['== N1 tail-support abstention']; G = rows(D / 'g4'); verdict = []
    ex, C = exposure([D / f'g4/N1all_k{k}_{f}_n1.json' for k in K for f in FL])
    out.append(f'  grid4 exposure of fleet forecast queries by support (arm all): ' + ', '.join(f'{k} {100 * v:.2f} %' for k, v in ex.items()))
    for m in ('all', 'tail', 'strict'):
        block(out, G, f'grid4 {m} vs R', lambda k, f, m=m: f'N1{m}_k{k}_{f}', lambda k, f: f'R_k{k}_{f}', S, K, FL)
    rt = block(out, G, 'grid4 tail - all (paired)', lambda k, f: f'N1tail_k{k}_{f}', lambda k, f: f'N1all_k{k}_{f}', S, K, FL)
    block(out, G, 'grid4 strict - all (paired)', lambda k, f: f'N1strict_k{k}_{f}', lambda k, f: f'N1all_k{k}_{f}', S, K, FL)
    verdict.append(ex['none'] >= 0.01 and rt['fuel_agent'][1] < 0)
    SP = {**rows(CS / 'm4_20261004/spider/s3b/dev'), **rows(D / 'sp')}; SS = list(range(100, 110)); KS = (11, 111)
    if all(f'N1{m}_{k}' in SP for m in ('tail', 'strict') for k in KS):
        exs, _ = exposure([D / f'sp/N1tail_{k}_n1.json' for k in KS]); out.append(f'  spider exposure (arm tail, counts before abstaining): ' + ', '.join(f'{k} {100 * v:.2f} %' for k, v in exs.items()))
        block(out, SP, 'spider all (Fq0.1) vs R', lambda k, f: f'Fq0.1_{k}', lambda k, f: f'R_{k}', SS, KS, ('x',))
        for m in ('tail', 'strict'):
            block(out, SP, f'spider {m} vs R', lambda k, f, m=m: f'N1{m}_{k}', lambda k, f: f'R_{k}', SS, KS, ('x',))
        rs = block(out, SP, 'spider tail - all (paired)', lambda k, f: f'N1tail_{k}', lambda k, f: f'Fq0.1_{k}', SS, KS, ('x',))
        block(out, SP, 'spider strict - all (paired)', lambda k, f: f'N1strict_{k}', lambda k, f: f'Fq0.1_{k}', SS, KS, ('x',))
        verdict.append(exs['none'] >= 0.01 and rs['fuel_agent'][1] < 0)
    for f in sorted((D / 'check').glob('offline_*.json')):
        out.append(f'  offline {f.stem}: {f.read_text().strip()[:600]}')
    out.append(f'  N1 VERDICT: {"SUPPORTED (tail abstention helps where exposure >= 1 %)" if any(verdict) else "REJECTED as a material harm source in these settings"}')
    t = '\n'.join(out) + '\n'; (D / 'report_n1.txt').write_text(t); print(t)
