#!/usr/bin/env python3
"""W21-E report (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-E): TSI-G (BIS) and TSI's default (TG, AH) in the W17 field-matched world, on
W21-A's R / SV rows (<dir>/conf).  D21-E1[f] (alpha 0.05/4): BIS - R meets every limit; D21-E2[f] (secondary, same alpha): the time limits
alone (city / agent / human uppers < +0.5, teleports <= R + 0.1, unfinished <= R).  Descriptive (95 %): BIS - SV, TG - R, RWV control,
mechanism (mean green / served-lane halting under R, SV, BIS).  Checks: w17_world tag on every row; KM13-1b.  Usage: CITY_w21e_report.py <dir>"""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]); SM = os.environ.get('W21_SMOKE') == '1'; SFX = '_smoke' if SM else ''
K0 = {'AH': 34, 'SRL': 84, 'RDQ': 89, 'RMP': 94, 'RWV': 99}; THR = ['AH', 'SRL', 'RDQ', 'RMP']
KEEP = os.environ.get('W21_FAMS', ' '.join(K0)).split()
SL = (0,) if SM else (0, 1, 2, 3, 4); FS = ('s2213',) if SM else ('s2213', 's2313', 's2413', 's2513'); S = [860] if SM else list(range(1420, 1440))
Q2 = 100 - 5 / 4; L = lambda f: tuple(K0[f] + j for j in SL); K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
Rt = rows(D / 'conf')
for key, rr in Rt.items():
    for s, r in rr.items():
        if not r.get('w17_world'):
            sys.exit(f'W21-E FAIL: {key} seed {s} not tagged w17_world')
        if not 0.98 <= r['modes_ratio_all'] <= 1.02:
            sys.exit(f'KM13-1b FAIL {key} seed {s}')
cal = json.loads((D / 'twin_calib_w17.json').read_text())
fid = [l for l in (D / 'check' / 'kw21e_twin_t34.txt').read_text().splitlines() if 'KW20-3' in l] if (D / 'check' / 'kw21e_twin_t34.txt').exists() else []
out = [f'== W21-E: TSI-G and TSI in the W17 field-matched world (lights {SL}, fleets {FS}, fresh {S[0]}-{S[-1]})',
       'rows tagged w17_world: PASS; KM13-1b PASS', f'CREEP chosen in this world: {cal["creep"]} s (twin / real halted vehicle-seconds {cal["grid"][str(cal["creep"])]["ratio"]:.3f})'] + [x[:300] for x in fid]
res = dict(creep=cal['creep'])


def mech(f, a):
    return tuple(float(np.mean([Rt[K(a)(l, fl)][s][m] for l in L(f) for fl in FS for s in S])) for m in ('green_mean', 'mean_halting'))


def tlimits(r, ta, tb):
    return all(r[k]['up'] < 0.5 for k in ('timeloss', 'timeloss_agent', 'timeloss_human')) and ta[0] <= tb[0] + 0.1 and ta[1] <= tb[1]


for f in [x for x in K0 if x in KEEP]:
    q = Q2 if f in THR else 95.0; e = {}
    r = V.paired(Rt, K('BIS'), K('R'), L(f), FS, S, q=q); ta, tb = V.tele(Rt, K('BIS'), L(f), FS, S), V.tele(Rt, K('R'), L(f), FS, S)
    ok, tl = V.limits(r, ta, tb); okt = tlimits(r, ta, tb); e.update(BIS_R=r, E1=ok, E2=okt)
    bs = V.paired(Rt, K('BIS'), K('SV'), L(f), FS, S); e['BIS_SV'] = bs
    m = {a: mech(f, a) for a in ('R', 'SV', 'BIS')}; e['mech'] = m
    out += [f'-- {f} (lights t{L(f)[0]}-t{L(f)[-1]})', V.line(f'BIS - R ({q:.2f} %)', r), f'  {tl}; every limit: {ok}; time limits only: {okt}',
            V.line('BIS - SV (95 %)', bs),
            '  mechanism (mean green s / served-lane halting): ' + ', '.join(f'{a} {v[0]:.2f} / {v[1]:.2f}' for a, v in m.items())]
    if f in THR:
        out.append(f'  D21-E1[{f}] TSI-G meets every limit: {"SHOWN" if ok else "NOT SHOWN"}; D21-E2[{f}] TSI-G meets the time limits: {"SHOWN" if okt else "NOT SHOWN"}')
    if f == 'AH':
        g = V.paired(Rt, K('TG'), K('R'), L(f), FS, S); okg, tlg = V.limits(g, V.tele(Rt, K('TG'), L(f), FS, S), tb)
        e['TG_R'] = g; out += [V.line('TG - R, TSI default adapter (95 %, descriptive)', g), f'  {tlg}; every limit: {okg}; time limits only: {tlimits(g, V.tele(Rt, K("TG"), L(f), FS, S), tb)}']
    res[f] = e
(D / f'report_w21e{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w21e{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
