#!/usr/bin/env python3
"""W13-2 / W13-3 selection (PROTOCOL_CITY_WAVE13_20261006).  FRESH2 lights t14-t18, TUNE 660-663, development fleet L11_s13.
Grid (A, B) in C x q in {0.1, 0.5}; agent fuel vs R in % (ratio of TUNE means) under HBEFA4 (H4) and PHEMlight5 (P5); time losses vs R
(points; identical under both models).  S = {agent TL <= 0, city TL <= 0, human TL <= 0}.
  R13-F   argmin over S of fuel_H4                       -> <dir>/tune/choice_F.json
  R13-RB  argmin over S of max(fuel_H4, fuel_P5)         -> <dir>/tune/choice_RB.json
Fallback (S empty): min agent TL.  Ties: smaller A + B, then q = 0.5.
KM13-1a: every P5 row equals its H4 twin in timeloss (3), n, teleports, unfinished and action_digest; else exit 1 (no choice written).
Rows: q = 0.5 H4 from w8_20261005/fresh2/tune (reused), the rest from <dir>/tune.   Usage: CITY_w13_select.py [<dir>]  (W13_SMOKE=1: t14, 660)"""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'research/city_sim/w13_20261006'; F2 = ROOT / 'research/city_sim/w8_20261005/fresh2'
SM = os.environ.get('W13_SMOKE') == '1'
LT = (14,) if SM else (14, 15, 16, 17, 18); S = [660] if SM else [660, 661, 662, 663]
GRID = [(1, 0), (1.5, 0), (2, 0), (1, 0.25), (1.5, 0.25), (2, 0.25), (1, 0.5), (1.5, 0.5), (2, 0.5), (3, 0.5)]
tag = lambda t, a, b: f'T_t{t}_a{a:g}_b{b:g}'.replace('.', 'p')  # noqa: E731
Rn = rows(D / 'tune'); Ro = {} if SM else rows(F2 / 'tune'); Rt = {**Ro, **Rn}
if SM:                                  # smoke: the q = 0.5 H4 twins were produced in the smoke directory under the same tags
    pass
TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')


def name(t, a, b, q, em):
    base = f'R_t{t}' if a is None else tag(t, a, b) + ('_q01' if q == 0.1 else '')
    return base + ('_P5' if em == 'P5' else '')


bad = []; out = ['== W13 selection (FRESH2 lights, TUNE ' + ','.join(map(str, S)) + ')']
for t in LT:
    keys = [(None, None, 0.5)] + [(a, b, q) for a, b in GRID for q in (0.5, 0.1)]
    for a, b, q in keys:
        h, p = name(t, a, b, q, 'H4'), name(t, a, b, q, 'P5')
        for s in S:
            x, y = Rt[h][s], Rt[p][s]
            for k in TW:
                if x.get(k) != y.get(k):
                    bad.append(f'{h} vs {p} s{s} {k}: {x.get(k)} != {y.get(k)}')
if bad:
    print('KM13-1a FAIL (P5 rows differ from their H4 twins in dynamics):'); print('\n'.join(bad[:20])); sys.exit(1)
out.append(f'KM13-1a PASS: every P5 row equals its H4 twin in time losses, n, teleports, unfinished and action digest ({len(LT)} lights)')
chF, chRB, tables = {}, {}, {}
for t in LT:
    R = {em: Rt[name(t, None, None, 0.5, em)] for em in ('H4', 'P5')}; tab = {}
    for a, b in GRID:
        for q in (0.5, 0.1):
            X = {em: Rt[name(t, a, b, q, em)] for em in ('H4', 'P5')}
            fu = {em: float(100 * (np.mean([X[em][s]['fuel_agent'] for s in S]) / np.mean([R[em][s]['fuel_agent'] for s in S]) - 1)) for em in ('H4', 'P5')}
            tl = {k: float(np.mean([X['H4'][s][k] - R['H4'][s][k] for s in S])) for k in ('timeloss', 'timeloss_agent', 'timeloss_human')}
            tab[f'{a:g},{b:g},{q:g}'] = dict(fuel_H4=fu['H4'], fuel_P5=fu['P5'], **tl)
    ok = [c for c, v in tab.items() if v['timeloss_agent'] <= 0 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
    tie = lambda c: (float(c.split(',')[0]) + float(c.split(',')[1]), 0 if c.endswith(',0.5') else 1)  # noqa: E731
    pick = lambda f: (min(ok, key=lambda c: (f(tab[c]),) + tie(c)) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'],) + tie(c)))  # noqa: E731
    cF = pick(lambda v: v['fuel_H4']); cRB = pick(lambda v: max(v['fuel_H4'], v['fuel_P5']))
    rule = 'qualified' if ok else 'fallback: min agent TL'
    chF[t] = dict(choice=cF, qualified=ok, rule=rule); chRB[t] = dict(choice=cRB, qualified=ok, rule=rule); tables[t] = tab
    out.append(f't{t}: {len(ok)} qualified | R13-F {cF} (H4 {tab[cF]["fuel_H4"]:+.2f}, P5 {tab[cF]["fuel_P5"]:+.2f}, agent {tab[cF]["timeloss_agent"]:+.2f})'
               f' | R13-RB {cRB} (H4 {tab[cRB]["fuel_H4"]:+.2f}, P5 {tab[cRB]["fuel_P5"]:+.2f}, agent {tab[cRB]["timeloss_agent"]:+.2f}) | {rule}')
    for c, v in sorted(tab.items(), key=lambda kv: max(kv[1]['fuel_H4'], kv[1]['fuel_P5'])):
        out.append(f'    {c:>12}: H4 {v["fuel_H4"]:+.2f}  P5 {v["fuel_P5"]:+.2f}  agent {v["timeloss_agent"]:+.2f}  city {v["timeloss"]:+.2f}  human {v["timeloss_human"]:+.2f}'
                   + ('  *' if c in ok else ''))
for p, d in (('choice_F.json', chF), ('choice_RB.json', chRB), ('tables.json', tables)):
    (D / 'tune' / p).write_text(json.dumps(d, indent=1))
(D / 'tune' / 'report_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
