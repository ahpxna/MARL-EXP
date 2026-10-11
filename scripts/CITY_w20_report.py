#!/usr/bin/env python3
"""W20 report (PROTOCOL_CITY_WAVE20_20261009).  Rows: <W20>/gate (OFF_t0_h, GATE_t<k>_h; H4), <W20>/conf (R / SV / BIS [P5] for the W20
lights 84-103; BIS [P5] for the W19 AH lights 34-38) and <W19>/conf (R / SV / TG [P5] of AH, registered in W19).
  D20-1[f], f in SRL, RDQ, RMP (alpha 0.05/3 each): DiD agent time loss (SV - R)_f - (SV - R)_RWV, lower bound > 0: publication harms the
           benchmark's threshold representation more than the threshold-free control (RESCO wave).
  D20-2[f], f in AH, SRL, RDQ, RMP (alpha 0.05/4 each): BIS - R meets every limit (agent fuel upper < 0 under HBEFA4 and PHEMlight5,
           time-loss uppers < +0.5, teleports <= R + 0.1, unfinished <= R): TSI-G repairs the frozen signal without retraining.
  Descriptive (95 %): gates; SV - R; BIS - SV; BIS - TG (AH); RWV control; mechanism (mean green, served-lane halting under R / SV / BIS).
W20_SMOKE=1: slot 0, fleet s1413, seed 860.   Usage: CITY_w20_report.py <W20 dir> <W19 dir>"""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D, D19 = Path(sys.argv[1]), Path(sys.argv[2]); SM = os.environ.get('W20_SMOKE') == '1'
K0 = {'AH': 34, 'SRL': 84, 'RDQ': 89, 'RMP': 94, 'RWV': 99}; THR = ['SRL', 'RDQ', 'RMP']
KEEP = os.environ.get('W20_FAMS', 'SRL RDQ RMP RWV').split()                # families not excluded as degenerate (the job sets it)
GONE = [f for f in ('SRL', 'RDQ', 'RMP', 'RWV') if f not in KEEP]; K0 = {f: k for f, k in K0.items() if f == 'AH' or f in KEEP}; THR = [f for f in THR if f in KEEP]
SL = (0,) if SM else (0, 1, 2, 3, 4); FS = ('s1413',) if SM else ('s1413', 's1513', 's1613', 's1713'); S = [860] if SM else list(range(1400, 1420))
Q1, Q2 = 100 - 5 / 3, 100 - 5 / 4
L = lambda f: tuple(K0[f] + j for j in SL)  # noqa: E731
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
Rt = rows(D / 'conf'); R19 = rows(D19 / 'conf')
for key, v in R19.items():
    if key.split('_t')[0] in ('R', 'RP5', 'SV', 'SVP5', 'TG', 'TGP5') and any(f'_t{k}_' in key for k in L('AH')):
        assert key not in Rt, key; Rt[key] = v
G = rows(D / 'gate')
for f in K0:
    for k in L(f):
        G[f'OFFG_t{k}_h'] = G['OFF_t0_h']
arms = lambda f: ('R', 'SV', 'BIS') + (('TG',) if f == 'AH' else ())  # noqa: E731
for f in K0:
    for a in arms(f):
        for l in L(f):
            for fl in FS:
                for s in S:
                    h, p = Rt[K(a)(l, fl)][s], Rt[K(a + 'P5')(l, fl)][s]
                    if any(h[t] != p[t] for t in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                        print('KM13-1a/1b FAIL', a, l, fl, s); sys.exit(1)
out = [f'== W20: benchmark representations and TSI-G (lights {SL}, fleets {FS}, fresh {S[0]}-{S[-1]})', 'KM13-1a PASS, KM13-1b PASS']
if GONE:
    out.append(f'EXCLUDED as degenerate (a green never completed in the traces; registered rule): {GONE}' + ('; D20-1 not computable without RWV' if 'RWV' in GONE else ''))
res = {}


def cmp(a, b, f, q):
    r = V.paired(Rt, K(a), K(b), L(f), FS, S, q=q); r5 = V.paired(Rt, K(a + 'P5'), K(b + 'P5'), L(f), FS, S, q=q)
    ok, tl = V.limits(r, V.tele(Rt, K(a), L(f), FS, S), V.tele(Rt, K(b), L(f), FS, S))
    return ok and r5['fuel_agent']['up'] < 0, r, r5, tl


def mech(f, a):
    return tuple(float(np.mean([Rt[K(a)(l, fl)][s][m] for l in L(f) for fl in FS for s in S])) for m in ('green_mean', 'mean_halting'))


for f in ['AH'] + THR + (['RWV'] if 'RWV' in KEEP else []):
    e = {}
    if f != 'AH':
        g = V.paired(G, K('GATE'), K('OFFG'), L(f), ('h',), S); e['gate'] = g['timeloss']
        out += [f'-- {f} (lights t{L(f)[0]}-t{L(f)[-1]})', V.line('light gate GATE - FT, all SUMO drivers (95 %)', g)]
    else:
        out.append(f'-- AH (W19 lights t{L(f)[0]}-t{L(f)[-1]}; R / SV / TG rows from W19)')
    pairs = [('SV', 'R', 95.0), ('BIS', 'R', Q2 if f in ['AH'] + THR else 95.0), ('BIS', 'SV', 95.0)] + ([('BIS', 'TG', 95.0)] if f == 'AH' else [])
    for a, b, q in pairs:
        ok, r, r5, tl = cmp(a, b, f, q); e[f'{a}-{b}'] = dict(meets=ok, H4=r, P5=r5)
        out += [V.line(f'{a} - {b} (H4, {q:.2f} %)', r), V.line(f'{a}P5 - {b}P5', r5), f'  {tl}; every limit met: {ok}']
    m = {a: mech(f, a) for a in ('R', 'SV', 'BIS')}; e['mech'] = m
    out.append('  mechanism (mean green s / served-lane halting): ' + ', '.join(f'{a} {m[a][0]:.2f} / {m[a][1]:.2f}' for a in m))
    if f in THR and 'RWV' in KEEP:
        dd = V.did(Rt, K('SV'), K('R'), L(f), K('SV'), K('R'), L('RWV'), FS, S, q=Q1); e['did_vs_RWV'] = dd
        d1 = dd['timeloss_agent']['low'] > 0; e['D20_1'] = d1
        out += [V.line(f'DiD (SV - R)_{f} - (SV - R)_RWV ({Q1:.2f} %; "low" = lower bound)', dd) + f' | agent TL lower {dd["timeloss_agent"]["low"]:+.2f}',
                f'  D20-1[{f}] publication harms this representation more than the threshold-free control: {"SHOWN" if d1 else "NOT SHOWN"}']
    if f in ['AH'] + THR:
        e['D20_2'] = e['BIS-R']['meets']
        out.append(f'  D20-2[{f}] TSI-G repairs the frozen signal (BIS - R meets every limit): {"SHOWN" if e["D20_2"] else "NOT SHOWN"}')
    res[f] = e
sfx = '_smoke' if SM else ''
(D / f'report_w20{sfx}.txt').write_text('\n'.join(out) + '\n'); (D / f'w20{sfx}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
