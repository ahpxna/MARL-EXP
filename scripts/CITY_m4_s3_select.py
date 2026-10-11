#!/usr/bin/env python3
"""M4 stage 3b DEV q selection (PROTOCOL_CITY_M4_STAGE3_20261004; the F1 §0 / M3 §6 rule, mechanical).  Rows in spider/s3b/dev (DEV 100-109):
R_<k> = F0 + no SPaT (== σ*), Fq<q>_<k> = F0 + forecast-K closed-loop table at q, lights k = 11, 111.  Cube [light 2, traffic 10], R.crossed.
Feasible (M3-2): city / agent / human TL upper < +0.5, teleports <= R + 0.1, unfinished <= R.  Locked q = the feasible q with the best agent fuel
point; if none is feasible, the best agent fuel point, marked INFEASIBLE.  Writes spider/s3b/prov/locked.json and spider/report_m4_s3b_select.txt."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
SP = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider'; S = list(range(100, 110)); K = (11, 111); QS = ('0.1', '0.2', '0.3', '0.5')
if __name__ == '__main__':
    DV = Path(sys.argv[sys.argv.index('--dir') + 1]) if '--dir' in sys.argv else SP / 's3b/dev'   # test hook
    Rt = rows(DV); dr = R.draws((len(K), len(S))); out = ['== M4 stage 3b DEV q selection (frozen rule F0, forecast-K closed-loop, spider DEV 100-109)']; score = {}
    for q in QS:
        c = lambda key, pct: np.array([[100 * (Rt[f'Fq{q}_{k}'][s][key] / Rt[f'R_{k}'][s][key] - 1) if pct else Rt[f'Fq{q}_{k}'][s][key] - Rt[f'R_{k}'][s][key] for s in S] for k in K])
        f = R.crossed(c('fuel_agent', True), dr); tl = {k_: R.crossed(c(k_, False), dr) for k_ in ('timeloss', 'timeloss_agent', 'timeloss_human')}
        tel = np.mean([Rt[f'Fq{q}_{k}'][s]['teleports'] for k in K for s in S]); tel0 = np.mean([Rt[f'R_{k}'][s]['teleports'] for k in K for s in S])
        unf = sum(Rt[f'Fq{q}_{k}'][s]['unfinished'] for k in K for s in S); unf0 = sum(Rt[f'R_{k}'][s]['unfinished'] for k in K for s in S)
        ok = all(tl[k_][2] < 0.5 for k_ in tl) and tel <= tel0 + 0.1 and unf <= unf0; score[q] = (ok, f[0])
        out.append(f"  q {q}: agent fuel % {f[0]:+.2f} [{f[1][0]:+.2f}, {f[1][1]:+.2f}] | city TL {tl['timeloss'][0]:+.2f} (up {tl['timeloss'][2]:+.2f}) agent {tl['timeloss_agent'][0]:+.2f} "
                   f"(up {tl['timeloss_agent'][2]:+.2f}) human {tl['timeloss_human'][0]:+.2f} (up {tl['timeloss_human'][2]:+.2f}) | tele {tel:.2f} ({tel0:.2f}) unf {unf} ({unf0}) -> {'FEASIBLE' if ok else 'infeasible'}")
    feas = [q for q in QS if score[q][0]]; best = min(feas or QS, key=lambda q: score[q][1])
    out.append(f'  LOCKED q {best} ({"feasible" if feas else "INFEASIBLE: no candidate meets M3-2"})')
    t = '\n'.join(out) + '\n'; print(t)
    if '--dir' not in sys.argv:
        (SP / 's3b/prov').mkdir(parents=True, exist_ok=True); (SP / 's3b/prov/locked.json').write_text(json.dumps(dict(q=float(best), feasible=bool(feas), score=score)))
        (SP / 'report_m4_s3b_select.txt').write_text(t)
