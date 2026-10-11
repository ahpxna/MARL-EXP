#!/usr/bin/env python3
"""W12-2 S1 report (PROTOCOL_CITY_WAVE12_20261006, Amendment A2): spider open-loop replay of recorded R and TSI schedules (ReplayK) with
sigma* (SIG), the attempt-4 forecast (FC) and exact future switches (ORC); self-checks KH-1 (SIG on REC_R == REC_R) and KH-1b (FC on REC_T ==
REC_T); paired contrasts over signals 11 / 111 x seeds.  Usage: CITY_w12_s1_report.py   (W12_SMOKE=<dir> W12_SEED=<s>)"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W12_SMOKE')); D = Path(os.environ['W12_SMOKE']) if SM else ROOT / 'research/city_sim/w12_20261006/s1'
S = [int(os.environ.get('W12_SEED', 1170))] if SM else list(range(1170, 1190)); LK = (11,) if SM else (11, 111)
Rt = rows(D / 'conf'); out = ['== W12-2 S1: spider oracle replay (ReplayK; signals 11 / 111; traffic 1170-1189)']
def same(a, b):
    bad = [(k, s) for k in LK for s in S if abs(Rt[f'{a}_{k}'][s]['timeloss'] - Rt[f'{b}_{k}'][s]['timeloss']) > 1e-9 or abs(Rt[f'{a}_{k}'][s]['fuel'] - Rt[f'{b}_{k}'][s]['fuel']) > 1e-6]
    return not bad, bad
k1, b1 = same('SIG_R', 'REC_R'); k2, b2 = same('FC_T', 'REC_T')
out.append(f'  KH-1  SIG on REC_R == REC_R: {"PASS" if k1 else "FAIL " + str(b1[:4])}')
out.append(f'  KH-1b FC on REC_T == REC_T: {"PASS" if k2 else "FAIL (FC_T approximate) " + str(b2[:4])}')
K = lambda a: (lambda l, f: f'{a}_{l}')  # noqa: E731
M = ('fuel_agent', 'timeloss_agent', 'timeloss_human')
res = {}
for sch in ('R', 'T'):
    for a, b in (('ORC', 'SIG'), ('FC', 'SIG'), ('ORC', 'FC')):
        r = V.paired(Rt, K(f'{a}_{sch}'), K(f'{b}_{sch}'), LK, ('x',), S); res[(sch, a, b)] = r
        out.append(V.line(f'{"R" if sch == "R" else "TSI"} schedule: {a} - {b}', r))
o, f = res[('T', 'ORC', 'SIG')]['timeloss_agent'], res[('T', 'FC', 'SIG')]['timeloss_agent']
if o['up'] <= 0 and f['up'] > 0:
    rd = 'forecast error is an important cause of the residual agent cost (exact timing removes it on the TSI schedule)'
elif o['low'] > 0:
    rd = 'a harm beyond forecast error exists (exact timing still costs agent time); this does NOT establish following/holding'
else:
    rd = 'no attribution'
out.append(f'  W12-2 S1 READING (TSI schedule): {rd}')
(D / 'report_s1.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
