#!/usr/bin/env python3
"""Calibration-view false-alarm rate of the Mahalanobis gates of scripts/MARL_e3_fallback_eval_v2.py (03/10/2026 14:2x EDT;
PROTOCOL_E3_FALLBACK_MAHAL_20261003 Amendment 1).  Read-only on the #3 calibration files; uses the gate function itself and
reports, per receiver, the weighted share of calibration views it flags, and for FB_Mq the mass AT the threshold (ties / float)."""
import json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_fallback_eval_v2 import mahalanobis_gate
out = {}
for net, arms, seeds in (('4x4', ('relayCK1_st', 'relayCage_st'), range(10)), ('3x3', ('relayCK1_st', 'relay6Cage_st'), range(5))):
    for arm in arms:
        for s in seeds:
            cal = json.loads((ROOT / f'research/marl_budget/e3_fallback_20261002/{net}/cal_{arm}_s{s}/calib.json').read_text())
            tot = sum(c for _, c in cal['counts']); r = {}
            for name, g in (('FB_M', mahalanobis_gate(cal, 0.99)), ('FB_M95', mahalanobis_gate(cal, 0.95)), ('FB_Mq', mahalanobis_gate(cal, 0.99, True))):
                r[name] = sum(c for k, c in cal['counts'] if g(k, 0, 0)) / tot
            out[f'{net}/{arm}_s{s}'] = r
for k, v in out.items():
    print(k, {n: round(x, 4) for n, x in v.items()})
agg = {n: (min(v[n] for v in out.values()), max(v[n] for v in out.values())) for n in ('FB_M', 'FB_M95', 'FB_Mq')}
print('range over receivers:', {n: (round(a, 4), round(b, 4)) for n, (a, b) in agg.items()})
(ROOT / 'research/marl_budget/e3_fallback_mahal_20261003/calib_false_alarm.json').write_text(json.dumps(out, indent=1))
