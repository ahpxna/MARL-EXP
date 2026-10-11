#!/usr/bin/env python3
"""F1 §0 mechanical provider selection (the M3 §6 rule, via CITY_m3_dev_report helpers on the F1 provider dir): per q, M3-1 agent fuel % vs R
and M3-2 feasibility; the feasible q with the best fuel point, else the best fuel point marked INFEASIBLE.  Writes prov/locked.json."""
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_m3_dev_report as DR  # noqa: E402
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
DR.D = Path(__file__).resolve().parents[1] / 'research/city_sim/f1_20261004/prov'
if __name__ == '__main__':
    Rt = rows(DR.D); dr = R.draws((2, 2, len(DR.S))); score = {}; out = ['== F1 §0 provider re-selection (frozen R10, corrected provider, DEV)']
    for q in ('0.1', '0.2', '0.3', '0.5'):
        arm = f'Fc{q}'; f1 = DR.summ(DR.cube(Rt, arm, 'R', 'fuel_agent', True), dr); ok, tl, tel, tel0 = DR.feasible(Rt, arm, dr); score[q] = (ok, f1['p'])
        out.append(f"  q {q}: agent fuel % {f1['p']:+.2f} [{f1['lo']:+.2f}, {f1['hi']:+.2f}] | city TL {tl['timeloss']['p']:+.2f} (up {tl['timeloss']['up']:+.2f}) agent "
                   f"{tl['timeloss_agent']['p']:+.2f} (up {tl['timeloss_agent']['up']:+.2f}) human {tl['timeloss_human']['p']:+.2f} (up {tl['timeloss_human']['up']:+.2f}) -> {'FEASIBLE' if ok else 'infeasible'}")
    best, feas = DR.select(score); out.append(f'  LOCKED provider: q {best} ({"feasible" if feas else "INFEASIBLE"})')
    (DR.D / 'locked.json').write_text(json.dumps(dict(q=float(best), feasible=feas, score=score))); t = '\n'.join(out) + '\n'; (DR.D.parent / 'report_f1_provider.txt').write_text(t); print(t)
