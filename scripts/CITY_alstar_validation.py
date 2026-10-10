#!/usr/bin/env python3
"""A-L* VALIDATION (PROTOCOL_CITY_B6 decision tree Branch P: "the best guard chosen on SELECT, judged on VALIDATION"; prepared 04/10/2026
wake 8 before job 047 ran).  Stage `plan`: reads job 047 (SELECT), picks the guard with the lowest point agent-TL difference vs always-SUMO
under RL-H (same rule as CITY_wave2_report_v2.ralstar) and prints CITY_eval5 config lines for VALIDATION 200-209: RL-H_0..3 x F* t0..t3 x
{chosen guard, none} + always-SUMO under each RL-H_i.  Stage `judge`: AL*-2 (agent TL superiority upper < 0, fuel NI upper < +2 %) and
AL*-3 (human-vehicle TL NI upper < +0.5) for the chosen guard on VALIDATION, crossed bootstrap light-seed x fleet-seed x traffic-seed."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

W = R.W; T = [0, 1, 2, 3]; VAL = list(range(200, 210))


def rows(d):
    Rt = {}
    for g in Path(d).glob('*.json'):
        x = json.loads(g.read_text())
        if isinstance(x, dict) and 'rows' in x:
            for r in x['rows']:
                Rt[(g.stem, r['seed'])] = r
    return Rt


def plan():
    N = (W / '047' / 'FSTAR.txt').read_text().split('=')[1].strip(); Rt = rows(W / '047')
    tag = lambda t, L, gd: f"{N}_t{t}_{L}_{gd}".replace(':', '-').replace('+', 'P')
    best = min(('none', 'fallback', 'clip', 'green+oos'), key=lambda gd: np.mean([Rt[(tag(t, f'RL-H:{i}', gd), s)]['timeloss_agent'] - Rt[(f'OFF_RL-H-{i}', s)]['timeloss_agent']
                                                                                for i in T for t in T for s in R.SEL]))
    (W / '048').mkdir(parents=True, exist_ok=True); (W / '048' / 'CHOSEN.txt').write_text(f'F*={N}\nguard={best}\n')
    seeds = ' '.join(map(str, VAL))
    for i in T:
        for t in T:
            for gd in sorted({best, 'none'}):
                print(f"--light RL-H:{i} --fleet U:{N}_t{t} --guard {gd} --support-from L-ACT:0 --seeds {seeds} --tag {tag(t, f'RL-H:{i}', gd)}")
        print(f"--light RL-H:{i} --fleet L-ACT:0 --guard always --seeds {seeds} --tag OFF_RL-H-{i}")


def judge():
    c = dict(l.split('=') for l in (W / '048' / 'CHOSEN.txt').read_text().split())
    N, gd = c['F*'], c['guard']; Rt = rows(W / '048')
    tag = lambda t, L: f"{N}_t{t}_{L}_{gd}".replace(':', '-').replace('+', 'P')
    cube = lambda k, pct=False: np.array([[[(100 * (Rt[(tag(t, f'RL-H:{i}'), s)][k] / Rt[(f'OFF_RL-H-{i}', s)][k] - 1)) if pct else
                                            (Rt[(tag(t, f'RL-H:{i}'), s)][k] - Rt[(f'OFF_RL-H-{i}', s)][k]) for s in VAL] for t in T] for i in T])
    dr = R.draws((4, 4, 10)); T_, F_, H_ = R.crossed(cube('timeloss_agent'), dr), R.crossed(cube('fuel_agent', True), dr), R.crossed(cube('timeloss_human'), dr)
    out = [f'== A-L* VALIDATION 200-209: F* = {N}, guard chosen on SELECT = {gd}; comparator always-SUMO under the same RL-H light',
           f'AL*-2 agent TL {R.fmt(*T_)}; agent fuel % {R.fmt(*F_)} -> {"SUPPORTED (benefit kept under the light upgrade)" if T_[2] < 0 and F_[2] < 2.0 else "NOT SUPPORTED"}',
           f'AL*-3 human-vehicle TL {R.fmt(*H_)} -> {"SUPPORTED" if H_[2] < 0.5 else "NOT SUPPORTED"}']
    (W / 'report_v2_alstar_validation.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    {'plan': plan, 'judge': judge}[sys.argv[1]]()
