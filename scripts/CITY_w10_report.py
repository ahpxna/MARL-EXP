#!/usr/bin/env python3
"""Wave-10 reports (PROTOCOL_CITY_WAVE10_20261005).  Usage: CITY_w10_report.py dca3 | diag     (W10_SMOKE=<dir> W10_SEED=<s>: smoke)"""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W10_SMOKE')); W = Path(os.environ['W10_SMOKE']) if SM else ROOT / 'research/city_sim/w10_20261005'


def order(d):
    f, t = d['fuel_agent'], d['timeloss_agent']
    if f['up'] <= 0 and t['up'] <= 0 and (f['up'] < 0 or t['up'] < 0):
        return 'TSI better'
    if f['low'] >= 0 and t['low'] >= 0 and (f['low'] > 0 or t['low'] > 0):
        return 'comparator better'
    return 'no ordering'


def dca3():
    D = W / 'dca3'; S = [int(os.environ.get('W10_SEED', 840))] if SM else list(range(840, 860))
    LT = (4,) if SM else (4, 5, 6, 7, 8); FL = ('s213',) if SM else ('s213', 's313', 's413', 's513'); Rt = rows(D / 'conf')
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
    out = ['== W10-1 DCA3 (corrected DC-Ada port: equal 1350 s horizon for references and candidates, author initialisation, output bound; '
           'lights t4-t8 x fleets s213-s513 x fresh traffic 840-859)', '  ' + (W / 'dca3' / 'check' / 'kw10_1.txt').read_text().strip().replace('\n', ' | ')]
    for a in ('TSI2', 'DCA3', 'DCA3X4'):
        r = V.paired(Rt, K(a), K('R'), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K(a), LT, FL, S), V.tele(Rt, K('R'), LT, FL, S))
        out += [V.line(f'{a} - R', r), f'  {a}: all M3 limits (incl. teleports, unfinished): {ok}; {tl}']
        if a == 'DCA3':
            v_a = ok
    d = V.paired(Rt, K('TSI2'), K('DCA3'), LT, FL, S); out += [V.line('TSI2 - DCA3', d), f'  (b) ordering (one-sided 95 %): {order(d)}']
    d4 = V.paired(Rt, K('TSI2'), K('DCA3X4'), LT, FL, S); out += [V.line('TSI2 - DCA3X4', d4), f'  (c) ordering vs 4x budget (secondary): {order(d4)}']
    for b, nm in (('tune', 'dca3'), ('tune4', 'dca3')):
        try:
            th = {l: json.loads((D / b / f'{nm}_t{l}.json').read_text()) for l in LT}
            out.append(f'  {b}: ' + '; '.join(f't{l} rollouts {th[l]["rollouts"]}/{th[l]["budget"]} horizon {th[l]["horizon_s"]} accepted {th[l]["accepted"]} |theta| {th[l]["param_norm"]:.3f}' for l in LT))
        except FileNotFoundError as e:
            out.append(f'  {b}: missing {e}')
    out.append(f'  W10-1 (a) DCA3 MEETS EVERY M3 LIMIT (alpha 0.05 one-sided): {"PASS" if v_a else "FAIL"}')
    (D / 'report_dca3.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    dict(dca3=dca3)[sys.argv[1]]()
