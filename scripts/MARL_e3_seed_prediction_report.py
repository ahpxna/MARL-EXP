#!/usr/bin/env python3
"""Scores the L-179 prediction (written 30/09 19:0x, BEFORE any relay result for seeds 6-9 existed).
G_s = mean over iid / cap4 / low of relay6Cage_st_s + age-first vs the same-seed zero-byte student (development panel).
H_s = BYTEBUDGET (raw teacher + 3 B) vs the zero-byte student (already measured, L-160 / L-170).
Rule: (a) among s6-s9, s7 has the most negative G; (b) s6, s8, s9 each have G > -1.5 %; (c) Spearman(H, G) >= 0.5 over
all seeds with both numbers.  All three -> supported."""
import json, sys, os
sys.path.insert(0, 'scripts')
import numpy as np
from MARL_e3_music_report import paired
C = 'research/marl_budget/e3_codesign_eval_20260929'; R = 'research/marl_budget/e3_satrot_eval_20260930'
def rows(p, rule):
    if not os.path.exists(os.path.join(os.path.dirname(p), 'manifest.json')): return None
    return {r['episode']: r for r in json.load(open(p)) if r['rule'] == rule}
G, H, cells = {}, {}, {}
for s in range(10):
    Z = rows(f'{C}/distill_none_s{s}/rows.json', 'none'); BB = rows(f'{C}/bb_set_full_s{s}/rows.json', 'prefix')
    v = []
    for cond, cap, rule in (('iid', 'iid', 'prefix'), ('cap4', 'iid', 'cap4'), ('low', 'low', 'prefix')):
        X = rows(f'{R}/relay6Cage_st_s{s}_agefirst_{cap}/rows.json', rule)
        if X: v.append(paired(X, Z))
    if len(v) == 3: G[s] = float(np.mean([x[0] for x in v])); cells[s] = v
    if BB: H[s] = paired(BB, Z)[0]
for s in sorted(cells):
    print(f's{s}: G = {G[s]:+.2f}  cells ' + ' '.join(f'{x[0]:+.2f}[{x[1]:+.2f},{x[2]:+.2f}]' for x in cells[s]) + (f'  H = {H[s]:+.2f}' if s in H else '  H n/a'))
new = [6, 7, 8, 9]
a = min(new, key=lambda s: G[s]) == 7
b = all(G[s] > -1.5 for s in (6, 8, 9))
both = sorted(set(G) & set(H))
from scipy.stats import spearmanr
rho = float(spearmanr([H[s] for s in both], [G[s] for s in both]).correlation)
c = rho >= 0.5
print(f'(a) s7 most negative among s6-s9: {a}  ({ {s: round(G[s], 2) for s in new} })')
print(f'(b) s6, s8, s9 each > -1.5 %: {b}')
print(f'(c) Spearman(H, G) over {both}: {rho:.2f} >= 0.5: {c}')
print('VERDICT:', 'SUPPORTED' if (a and b and c) else 'NOT SUPPORTED')
json.dump(dict(G=G, H=H, rho=rho, a=a, b=b, c=c, verdict=bool(a and b and c)), open('research/marl_budget/e3_seed_prediction_report_20260930.json', 'w'), indent=1)
