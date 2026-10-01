#!/usr/bin/env python3
"""Overnight seed expansion, development panel (ledger L-186 plan; this report 30/09 23:5x EDT, ledger L-190).
Reads only finished outputs (manifest.json present); re-run as more finish.  Uses MARL_e3_music_report.paired (waiting-time
ratio, cluster bootstrap over the 64 traffic seeds, 128 paired episodes).
  1. Bar variation: Z' = distill_none_rep_s (seed 100 + s) vs Z = distill_none_s, same teacher and recipe.
  2. Each relay student X_s in {relay6_st, relay6B8_st, relay6Clow_st, relay6Cage_st} on the satrot grid, six cells
     (order agefirst / prefix x condition iid / cap4 / low), against the same-seed Z and against Z'.
     A cell is a WIN if the 95 % upper bound < 0, a LOSS if the lower bound > 0.
"""
import json, os, sys
sys.path.insert(0, 'scripts')
import numpy as np
from MARL_e3_music_report import paired
D = 'research/marl_budget/e3_codesign_eval_20260929'; R = 'research/marl_budget/e3_satrot_eval_20260930'
OUT = 'research/marl_budget/e3_overnight_report_20260930.json'


def rows(p, rule):
    if not os.path.exists(os.path.join(os.path.dirname(p), 'manifest.json')):
        return None
    return {r['episode']: r for r in json.load(open(p)) if r['rule'] == rule}


CELLS = [(o, c, cap, rule) for o in ('agefirst', 'prefix') for (c, cap, rule) in (('iid', 'iid', 'prefix'), ('cap4', 'iid', 'cap4'), ('low', 'low', 'prefix'))]
out = dict(bar={}, students={})
print('== 1. bar variation: Z\' (seed 100+s) vs Z')
for s in range(10):
    Z = rows(f'{D}/distill_none_s{s}/rows.json', 'none'); Zr = rows(f'{D}/distill_none_rep_s{s}/rows.json', 'none')
    if Z and Zr:
        out['bar'][s] = paired(Zr, Z)
        print(f'  s{s}: {out["bar"][s][0]:+.2f} [{out["bar"][s][1]:+.2f}, {out["bar"][s][2]:+.2f}]')
print('== 2. relay students vs same-seed Z (and vs Z\')')
for fam in ('relay6_st', 'relay6B8_st', 'relay6Clow_st', 'relay6Cage_st'):
    for s in range(10):
        Z = rows(f'{D}/distill_none_s{s}/rows.json', 'none'); Zr = rows(f'{D}/distill_none_rep_s{s}/rows.json', 'none')
        if not Z:
            continue
        res = {}
        for (o, c, cap, rule) in CELLS:
            X = rows(f'{R}/{fam}_s{s}_{o}_{cap}/rows.json', rule)
            if X:
                res[f'{o}/{c}'] = dict(vsZ=paired(X, Z), vsZrep=paired(X, Zr) if Zr else None)
        if not res:
            continue
        out['students'][f'{fam}_s{s}'] = res
        line = []
        for o in ('agefirst', 'prefix'):
            v = [res[f'{o}/{c}']['vsZ'] for c in ('iid', 'cap4', 'low') if f'{o}/{c}' in res]
            w = sum(x[2] < 0 for x in v); l = sum(x[1] > 0 for x in v)
            line.append(f'{o}: ' + ' '.join(f'{x[0]:+.2f}[{x[1]:+.2f},{x[2]:+.2f}]' for x in v) + f'  win {w}/{len(v)} loss {l}')
        print(f'  {fam}_s{s}  ' + ' | '.join(line))
print('== 3. family summary (age-first and prefix orders, vs Z): mean over cells and seeds; seeds with all 3 cells WIN')
summ = {}
for fam in ('relay6_st', 'relay6B8_st', 'relay6Clow_st', 'relay6Cage_st'):
    for o in ('agefirst', 'prefix'):
        vals, allwin, nseed = [], 0, 0
        for k, res in out['students'].items():
            if not k.startswith(fam + '_s'):
                continue
            v = [res[f'{o}/{c}']['vsZ'] for c in ('iid', 'cap4', 'low') if f'{o}/{c}' in res]
            if len(v) < 3:
                continue
            nseed += 1; vals += [x[0] for x in v]; allwin += int(all(x[2] < 0 for x in v))
        if nseed:
            summ[f'{fam}/{o}'] = dict(seeds=nseed, mean=round(float(np.mean(vals)), 2), all3win=allwin)
            print(f'  {fam:14s} {o:8s} seeds {nseed}  mean {np.mean(vals):+.2f}%  all-3-cells-win {allwin}/{nseed}')
out['summary'] = summ
json.dump(out, open(OUT, 'w'), indent=1)
print('wrote', OUT)
