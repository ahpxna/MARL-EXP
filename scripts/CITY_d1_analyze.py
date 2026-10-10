#!/usr/bin/env python3
"""D1 analysis: for every ordered pair of policies (P, Q) on TRAIN traffic 0-7 (paired by seed), PHYSICAL dominance
  P >phys Q  iff  agent fuel %(P vs Q) upper < 0  AND  agent TL(P - Q) upper < +0.5  AND  human TL(P - Q) upper < +0.5   (one-sided 95 %)
and OBJECTIVE order on B_sum, B_agent_return (paired mean difference with a 95 % bootstrap CI over seeds).  A MISALIGNMENT is a pair with
P >phys Q while the objective significantly prefers Q (CI of obj(P) - obj(Q) entirely < 0).  Also: feasibility vs always-SUMO and the fuel
order among feasible policies.  No combined fuel/TL score.  Writes reward_alignment.json / .txt."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

D = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('research/city_sim/spat_pilot_20261004/diag/d1')
P = {f.stem: {r['seed']: r for r in json.loads(f.read_text())['rows']} for f in sorted(D.glob('*.json')) if f.stem != 'reward_alignment'}
seeds = sorted(set.intersection(*[set(v) for v in P.values()])); dr = R.draws((len(seeds),)); out = [f'== D1 reward alignment, FT, TRAIN traffic {seeds}']
summ = {}
for k, v in P.items():
    m = lambda x: float(np.mean([v[s][x] for s in seeds]))
    summ[k] = dict(fuel=m('fuel_agent'), tla=m('timeloss_agent'), tlh=m('timeloss_human'), tele=m('teleports'), unf=m('unfinished'), B_sum=m('B_sum'), B_ret=m('B_agent_return'),
                   R1=float(np.mean([v[s]['branch_share']['R1'] for s in seeds])))
    out.append(f"  {k:28s} fuel {summ[k]['fuel']:8.0f}  TLa {summ[k]['tla']:6.2f}  TLh {summ[k]['tlh']:6.2f}  tele {summ[k]['tele']:4.1f}  B_sum {summ[k]['B_sum']:9.0f}  B_ret {summ[k]['B_ret']:7.2f}  R1 {summ[k]['R1']:.3f}")
mis = []; agree = 0; npairs = 0
for a in P:
    for b in P:
        if a == b:
            continue
        F = R.crossed(np.array([100 * (P[a][s]['fuel_agent'] / P[b][s]['fuel_agent'] - 1) for s in seeds]), dr)
        T = R.crossed(np.array([P[a][s]['timeloss_agent'] - P[b][s]['timeloss_agent'] for s in seeds]), dr)
        H = R.crossed(np.array([P[a][s]['timeloss_human'] - P[b][s]['timeloss_human'] for s in seeds]), dr)
        if not (F[2] < 0 and T[2] < 0.5 and H[2] < 0.5):
            continue
        npairs += 1
        for obj in ('B_sum', 'B_agent_return'):
            O = R.crossed(np.array([P[a][s][obj] - P[b][s][obj] for s in seeds]), dr)
            if O[1][1] < 0:
                mis.append(f'{a} >phys {b} (fuel {F[0]:+.2f}%, TLa {T[0]:+.2f}, TLh {H[0]:+.2f}) but {obj} prefers {b}: {R.fmt(*O)}')
            elif O[1][0] > 0:
                agree += 1
out.append(f'physically dominant ordered pairs: {npairs}; objective agrees significantly in {agree} (pair x objective) cases; MISALIGNMENTS {len(mis)}:')
out += ['  ' + m for m in mis]
off = 'always'
if off in P:
    out.append('feasibility vs always-SUMO (fuel upper < 0, TLa upper < +0.5, TLh upper < +0.5):')
    for k in P:
        if k == off:
            continue
        F = R.crossed(np.array([100 * (P[k][s]['fuel_agent'] / P[off][s]['fuel_agent'] - 1) for s in seeds]), dr)
        T = R.crossed(np.array([P[k][s]['timeloss_agent'] - P[off][s]['timeloss_agent'] for s in seeds]), dr)
        H = R.crossed(np.array([P[k][s]['timeloss_human'] - P[off][s]['timeloss_human'] for s in seeds]), dr)
        out.append(f'  {k:28s} fuel % {R.fmt(*F)}; TLa {R.fmt(*T)}; TLh upper {H[2]:+.2f} -> {"FEASIBLE" if F[2] < 0 and T[2] < 0.5 and H[2] < 0.5 else "not feasible"}')
txt = '\n'.join(out) + '\n'; (D / 'reward_alignment.txt').write_text(txt); (D / 'reward_alignment.json').write_text(json.dumps(dict(summary=summ, misalignments=mis, physical_pairs=npairs), indent=1)); print(txt)
