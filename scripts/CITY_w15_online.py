#!/usr/bin/env python3
"""W15-3b (PROTOCOL_CITY_WAVE15_20261007, Amendment A3): online calibration under model shift (Krauss-calibrated FRESH2 TSI deployed in an
IDM world), safe successive elimination.  Because the simulator is deterministic, every arm was run on every day (rows <dir>/days/<ARM>_t<k>);
the algorithm below sees only the rows of the arm it plays on each day, which is exactly equivalent to running it online.
  Arms: OFF (R, no SPaT) and A1 (1,0.25,0.1), A2 (1,0.5,0.1), A3 (1.5,0,0.1), A4 (1,0.25,0.5), A5 (1,0.5,0.5); a day = one traffic seed
  (1200-1239), fleet s1013, the five FRESH2 light checkpoints; a day's outcome = mean over the five lights of agent fuel and agent TL.
  Round-robin over the active arms (OFF included).  After each round, a non-OFF arm with >= 2 days is eliminated if the one-sided 90 % Welch
  lower bound of (agent TL - OFF agent TL) exceeds +0.5 s/veh, or if its mean agent fuel is not below OFF's.  Stop when one non-OFF arm remains
  or the 40 days are used; output the remaining non-OFF arm with the lowest mean fuel, or OFF.
  choose <dir>  -> <dir>/online.json, report_online.txt          report <dir>  evaluation 1240-1259 (all arms, all fleets) -> report_eval.txt
W15_SMOKE=1: t14, days 700-705 / 860."""
import json, math, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
cmd, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W15_SMOKE') == '1'
LT = (14,) if SM else (14, 15, 16, 17, 18); DAYS = list(range(700, 706)) if SM else list(range(1200, 1240))
FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313'); ES = [860] if SM else list(range(1240, 1260))
ARMS = ['OFF', 'A1', 'A2', 'A3', 'A4', 'A5']
if cmd == 'choose':
    Rt = rows(D / 'days'); day = lambda a, s: (float(np.mean([Rt[f'{a}_t{k}'][s]['fuel_agent'] for k in LT])), float(np.mean([Rt[f'{a}_t{k}'][s]['timeloss_agent'] for k in LT])))  # noqa: E731
    active = list(ARMS); obs = {a: [] for a in ARMS}; log = []; i = 0; t90 = 1.2816
    while i < len(DAYS):
        for a in list(active):
            if i >= len(DAYS):
                break
            s = DAYS[i]; obs[a].append(day(a, s)); log.append(f'day {s}: {a} fuel {obs[a][-1][0]:.0f} agentTL {obs[a][-1][1]:.2f}'); i += 1
        off = np.array(obs['OFF'])
        for a in [x for x in active if x != 'OFF']:
            x = np.array(obs[a])
            if len(x) >= 2 and len(off) >= 2:
                d = x[:, 1].mean() - off[:, 1].mean(); se = math.sqrt(x[:, 1].var(ddof=1) / len(x) + off[:, 1].var(ddof=1) / len(off)); lb = d - t90 * se
                if lb > 0.5 or x[:, 0].mean() >= off[:, 0].mean():
                    active.remove(a); log.append(f'  eliminate {a} after {len(x)} days: TL diff {d:+.2f} (90% lower {lb:+.2f}), fuel ratio {x[:, 0].mean() / off[:, 0].mean():.4f}')
        if len([x for x in active if x != 'OFF']) <= 1:
            break
    rest = [x for x in active if x != 'OFF']; ch = min(rest, key=lambda a: np.mean([o[0] for o in obs[a]])) if rest else 'OFF'
    out = ['== W15-3b online calibration (IDM world; Krauss-calibrated providers)', *log, f'days used {i}; remaining {active}; CHOICE {ch}']
    (D / 'online.json').write_text(json.dumps(dict(choice=ch, days_used=i, remaining=active), indent=1)); (D / 'report_online.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
else:
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
    Rt = rows(D / 'eval'); ch = json.loads((D / 'online.json').read_text())['choice']
    out = [f'== W15-3b evaluation on fresh IDM traffic {ES[0]}-{ES[-1]} (all fleets; one-sided 95 %); online choice {ch}']
    for a in ARMS[1:]:
        for x in ('', 'P5'):
            r = V.paired(Rt, K(a + x), K('OFF' + x), LT, FL, ES)
            ok, tl = V.limits(r, V.tele(Rt, K(a + x), LT, FL, ES), V.tele(Rt, K('OFF' + x), LT, FL, ES))
            out.append(V.line(f'{a}{x} - OFF{x}' + ('  <- online choice' if a == ch and not x else ''), r) + f'  | all limits {ok}')
    (D / 'report_eval.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
