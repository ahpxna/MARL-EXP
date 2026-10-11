#!/usr/bin/env python3
"""W12-3 S2a report (PROTOCOL_CITY_WAVE12_20261006, Amendment A4): closed-loop targeted vs matched-random release on one-lane spider
(signals 11 / 111 x 1170-1189).  KR-1: mode none reproduces TSIK.  Usage: CITY_w12_s2_report.py   (W12_SMOKE=<dir> W12_SEED=<s>)"""
import os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W12_SMOKE')); D = Path(os.environ['W12_SMOKE']) if SM else ROOT / 'research/city_sim/w12_20261006/s2'
S = [int(os.environ.get('W12_SEED', 1170))] if SM else list(range(1170, 1190)); LK = (11,) if SM else (11, 111)
Rt = rows(D / 'conf'); K = lambda a: (lambda l, f: f'{a}_{l}')  # noqa: E731
out = ['== W12-3 S2a: closed-loop release of gliding agents with a human follower within 50 m (TREL) vs matched-rate random release (RREL); one-lane spider']
a, b = Rt['KR_none_11'], Rt['KR_tsik_11']; s0 = sorted(a)[0]
kr = abs(a[s0]['timeloss'] - b[s0]['timeloss']) < 1e-9 and abs(a[s0]['fuel'] - b[s0]['fuel']) < 1e-6
out.append(f'  KR-1 release mode none == TSIK (signal 11, seed {s0}): {"PASS" if kr else "FAIL"}')
for arm in ('TREL', 'RREL'):
    g = sum(Rt[f'{arm}_{k}'][s]['rel_glide_s'] for k in LK for s in S); r = sum(Rt[f'{arm}_{k}'][s]['rel_released'] for k in LK for s in S)
    out.append(f'  {arm}: released {r} of {g} glide-seconds ({r / max(1, g):.3f})')
for x, y in (('TSIK', 'R'), ('TREL', 'R'), ('RREL', 'R'), ('TREL', 'TSIK'), ('RREL', 'TSIK'), ('TREL', 'RREL')):
    out.append(V.line(f'{x} - {y}', V.paired(Rt, K(x), K(y), LK, ('x',), S)))
for arm in ('R', 'TSIK', 'TREL', 'RREL'):
    out.append(f'  mean green {arm}: ' + ', '.join(f'{k} {np.mean([Rt[f"{arm}_{k}"][s]["green_mean"] for s in S]):.2f}' for k in LK))
d1 = V.paired(Rt, K('TREL'), K('RREL'), LK, ('x',), S); d2 = V.paired(Rt, K('TREL'), K('R'), LK, ('x',), S); d3 = V.paired(Rt, K('TREL'), K('TSIK'), LK, ('x',), S)
ev = d1['timeloss_agent']['up'] < 0 and d2['fuel_agent']['up'] < 0 and d3['timeloss_agent']['up'] < 0
out.append(f'  W12-3 S2a READING: {"following events drive part of the residual cost (targeted beats matched random, keeps fuel, improves on TSIK)" if ev else "no evidence that following events drive the residual cost"}')
(D / 'report_s2.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
