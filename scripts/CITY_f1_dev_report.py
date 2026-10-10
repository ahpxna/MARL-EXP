#!/usr/bin/env python3
"""F1 DEV report (PROTOCOL_CITY_F1 §3; written before any F1 evaluation).  Cubes [run, traffic 15] vs R of the run's light (R rows from §0).
Arms: F1 (4 fine-tuned runs pooled), F1-scratch (4 runs pooled), F0 (frozen dev fleets s13 / s113 under k 0 / 1 with the locked q).
DEV gate: F1 pooled passes agent fuel superiority (upper < 0), city / agent / human TL upper < +0.5, teleports <= R + 0.1, unfinished <= R."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/f1_20261004'; S = [100, 101, 102, 103, 104] + list(range(200, 210))
q = json.loads((D / 'prov/locked.json').read_text())['q']


def block(Rt, items, name, out):
    """items: list of (tag, k)."""
    for t, _ in items:
        if t not in Rt or sorted(Rt[t]) != S:
            raise SystemExit(f'INCOMPLETE {t}')
    dr = R.draws((len(items), len(S))); res = {}
    for key, pct in (('fuel_agent', True), ('timeloss', False), ('timeloss_agent', False), ('timeloss_human', False)):
        c = np.array([[100 * (Rt[t][s][key] / Rt[f'R_k{k}_s13'][s][key] - 1) if pct else Rt[t][s][key] - Rt[f'R_k{k}_s13'][s][key] for s in S] for t, k in items])
        res[key] = R.crossed(c, dr)
    tel = np.mean([Rt[t][s]['teleports'] for t, _ in items for s in S]); tel0 = np.mean([Rt[f'R_k{k}_s13'][s]['teleports'] for _, k in items for s in S])
    unf = sum(Rt[t][s]['unfinished'] for t, _ in items for s in S); unf0 = sum(Rt[f'R_k{k}_s13'][s]['unfinished'] for _, k in items for s in S)
    ok = res['fuel_agent'][2] < 0 and all(res[k][2] < 0.5 for k in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel <= tel0 + 0.1 and unf <= unf0
    f = lambda k: f"{res[k][0]:+.2f} [{res[k][1][0]:+.2f}, {res[k][1][1]:+.2f}] (up {res[k][2]:+.2f})"
    out.append(f"  {name}: agent fuel % {f('fuel_agent')} | city TL {f('timeloss')} | agent TL {f('timeloss_agent')} | human TL {f('timeloss_human')} | tele {tel:.2f} ({tel0:.2f}) unf {unf} ({unf0}) -> {'PASS' if ok else 'FAIL'}")
    return ok


if __name__ == '__main__':
    Rt = rows(D / 'prov'); out = [f'== F1 DEV: RL-H:k original, corrected provider q {q}, DEV traffic (SELECT 100-104 + 200-209); vs R (no SPaT, fleet = σ*)']
    block(Rt, [(f'Fc{q:g}_k{k}_{fl}', k) for k in (0, 1) for fl in ('s13', 's113')], 'F0 (frozen R10)', out)
    g = block(Rt, [(f'EV_F1_s{fl}_k{k}', k) for fl, k in (('13', 0), ('113', 1), ('13', 1), ('113', 0))], 'F1 (fine-tuned, 4 runs)', out)
    block(Rt, [(f'EV_F1s_s{sd}_k{k}', k) for sd in (13, 113) for k in (0, 1)], 'F1-scratch (4 runs)', out)
    out.append(f'  F1 DEV GATE -> {"PASS: confirmation per §4" if g else "FAIL"}'); t = '\n'.join(out) + '\n'; (D / 'report_f1_dev.txt').write_text(t); print(t)
