#!/usr/bin/env python3
"""W12-4 DCA-task report (PROTOCOL_CITY_WAVE12_20261006, Amendment A3).  Fresh grid4 880-899, lights t4-t8 x fleets s213-s513 x 20.
(a) each DCA arm (DCAS = information arm, DCAR = raw arm; DEV-selected checkpoints) meets every M3 limit vs R (one-sided 95 %);
(b) TSI2 vs each arm: W1 iff the arm is feasible and TSI2 - DCAx fuel upper < 0; W2 iff fuel upper < +0.5 pp and agent TL upper < 0;
otherwise no ordering; (c) the DEV budget curve (report_dev.txt).  Usage: CITY_w12_dcas_report.py   (W12_SMOKE=<dir> W12_SEED=<s>)"""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W12_SMOKE')); D = Path(os.environ['W12_SMOKE']) if SM else ROOT / 'research/city_sim/w12_20261006/dcas'
S = [int(os.environ.get('W12_SEED', 880))] if SM else list(range(880, 900)); LT = (4,) if SM else (4, 5, 6, 7, 8)
FL = ('s213',) if SM else ('s213', 's313', 's413', 's513'); Rt = rows(D / 'conf')
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
sel = json.loads((D / 'dev' / 'selection.json').read_text())
out = ['== W12-4 DCA-task (DC-Ada search; DCAS = with TSI\'s speed-binned counts, DCAR = raw input; full horizon; DEV-selected budgets '
       + ', '.join(f'{k} b{v["choice"]}' for k, v in sel.items()) + '; fresh grid4 880-899)']
feas = {}
for a in ('TSI2', 'DCAS', 'DCAR'):
    r = V.paired(Rt, K(a), K('R'), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K(a), LT, FL, S), V.tele(Rt, K('R'), LT, FL, S)); feas[a] = ok
    out += [V.line(f'{a} - R', r), f'  (a) {a}: all M3 limits (incl. teleports, unfinished): {ok}; {tl}']
for a in ('DCAS', 'DCAR'):
    d = V.paired(Rt, K('TSI2'), K(a), LT, FL, S); fu, ta = d['fuel_agent'], d['timeloss_agent']
    w = ('W1: TSI better on fuel against a feasible competitor' if feas[a] and fu['up'] < 0 else
         'W2: fuel within +0.5 pp with lower agent time loss' if fu['up'] < 0.5 and ta['up'] < 0 else 'no ordering')
    out += [V.line(f'TSI2 - {a}', d), f'  (b) TSI2 vs {a}: {w}' + ('' if feas[a] else f' ({a} infeasible under (a))')]
(D / 'report_dcas.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
