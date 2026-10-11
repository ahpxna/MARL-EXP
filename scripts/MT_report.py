#!/usr/bin/env python3
"""Midtown report (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010, MT-A3/A4/A5): every arm on test days 0-4 from
research/city_sim/midtown_transfer_20261010/eval5/*.json (COMPLETE files only; missing arms are listed, never imputed).
Per arm: mean time loss / time stopped (waiting) / fuel / teleports / unfinished over all (seed, day) runs, the spread of the per-seed
5-day means, and — for light arms that share the grid lights' seeds k = 59..63 — the paired difference to the transferred grid light
(MTR_LG_t<k>, same k, same day) with a percentile bootstrap over the 25 (k, day) pairs (2 000 draws, seed 0).  Descriptive.
Usage: MT_report.py [out.txt]"""
import json, sys
from pathlib import Path
import numpy as np

import os
ROOT = Path(__file__).resolve().parents[1]
E5 = Path(os.environ['MT_EVAL_DIR']) if os.environ.get('MT_EVAL_DIR') else ROOT / 'research/city_sim/midtown_transfer_20261010/eval5'
PFX = os.environ.get('MT_TAG_PREFIX', 'MTR')                     # MT-C: the full-map tests use MTF_*
OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'research/city_sim/midtown_transfer_20261010/report_mt.txt'
DAYS = [0, 1, 2, 3, 4]; K = [59, 60, 61, 62, 63]; FS = [1413, 1513, 1613, 1713]
ARMS = [('FT (SUMO fixed-time)', [f'{PFX}_FT']), ('ACT (SUMO actuated)', [f'{PFX}_ACT']),
        ('LIGHT grid-trained, transferred', [f'{PFX}_LG_t{k}' for k in K]), ('LIGHT Midtown-trained MT-A3 (teleports on)', [f'{PFX}_LM_t{k}' for k in K]),
        ('LIGHT grid-trained, max green 50 s (MT-D)', [f'{PFX}_LGc_t{k}' for k in K]),
        ('LIGHT grid-trained + actuated on the other signals (MT-E)', [f'{PFX}_LGar_t{k}' for k in K]),
        ('LIGHT Midtown A4: shared from scratch, teleports off', [f'{PFX}_A4_t{k}' for k in K]),
        ('LIGHT Midtown A5-ft: shared fine-tuned from grid', [f'{PFX}_A5ft_t{k}' for k in K]),
        ('LIGHT Midtown A5-lg: grid shared + gated local', [f'{PFX}_A5lg_t{k}' for k in K]),
        ('LIGHT Midtown A5-ln: grid shared + local (no gate)', [f'{PFX}_A5ln_t{k}' for k in K]),
        ('LIGHT Midtown A5-lo: local only', [f'{PFX}_A5lo_t{k}' for k in K]),
        ('FT + grid fleet (exact SPaT)', [f'{PFX}_FG_s{s}' for s in FS]), ('FT + Midtown fleet (exact SPaT)', [f'{PFX}_FM_s{s}' for s in FS]),
        ('grid lights + grid fleets (adapted forecast)', [f'{PFX}_BG_t{k}_s{s}' for k in K for s in FS]),
        ('grid lights + grid fleets, max green 50 s (MT-D)', [f'{PFX}_BGc_t{k}_s{s}' for k in K for s in FS]),
        ('grid lights + grid fleets + actuated on the other signals (MT-E)', [f'{PFX}_BGar_t{k}_s{s}' for k in K for s in FS]),
        ('… same, forecast re-fitted on the full map (MT-F, interface only)', [f'{PFX}_BGFar_t{k}_s{s}' for k in K for s in FS]),
        ('grid lights + Midtown fleets (adapted forecast)', [f'{PFX}_BM_t{k}_s{s}' for k in K for s in FS]),
        ('grid lights + grid fleets, forecast re-fitted on Midtown (interface only)', [f'{PFX}_BGF_t{k}_s{s}' for k in K for s in FS]),
        ('A4 lights + Midtown fleets, own Midtown forecast', [f'{PFX}_BMM_a4_t{k}_s{s}' for k in K for s in FS]),
        ('A5-ft lights + Midtown fleets, own Midtown forecast', [f'{PFX}_BMM_ft_t{k}_s{s}' for k in K for s in FS])]
MET = [('timeloss', 'TL s'), ('waiting', 'stop s'), ('fuel', 'fuel g'), ('teleports', 'tele'), ('unfinished', 'unfin')]


def load(tag):
    f = E5 / f'{tag}.json'
    if not f.exists():
        return None
    d = json.loads(f.read_text())
    if d.get('status') != 'COMPLETE':
        return None
    r = {x['seed']: x for x in d['rows']}
    return r if sorted(r) == DAYS else None


def val(row, k):
    return row[k] / 1000.0 if k == 'fuel' else row[k]


lines = [f'Midtown report [{PFX}, {E5.name}] — test days 0-4 (SUMO, 4 800 random trips/h, base plan osm, two-green AI lights); means over every (seed, day) run', '']
lines.append(f'{"arm":58s} {"runs":>5s} ' + ' '.join(f'{n:>8s}' for _, n in MET) + '   per-seed TL means')
lg = {k: load(f'{PFX}_LG_t{k}') for k in K}
pairs = []
for name, tags in ARMS:
    R = {t: load(t) for t in tags}; have = {t: r for t, r in R.items() if r is not None}
    if not have:
        lines.append(f'{name:58s}   missing ({len(tags)} files)'); continue
    runs = [r[dd] for r in have.values() for dd in DAYS]
    per = [np.mean([r[dd]['timeloss'] for dd in DAYS]) for r in have.values()]
    miss = '' if len(have) == len(tags) else f'  [{len(tags) - len(have)} of {len(tags)} missing]'
    lines.append(f'{name:58s} {len(runs):5d} ' + ' '.join(f'{np.mean([val(x, k) for x in runs]):8.1f}' for k, _ in MET)
                 + '   ' + ' '.join(f'{p:.0f}' for p in per[:20]) + miss)
    if tags[0].startswith(tuple(f'{PFX}_{x}' for x in ('LM', 'A4', 'A5', 'LGc', 'LGar'))) and all(lg.values()):
        diffs = [have[t][dd]['timeloss'] - lg[int(t.split('_t')[-1])][dd]['timeloss'] for t in have for dd in DAYS]
        rng = np.random.default_rng(0); bs = [np.mean(rng.choice(diffs, len(diffs))) for _ in range(2000)]
        pairs.append(f'  {name:56s} TL − LIGHT-grid (same k, same day): {np.mean(diffs):+7.2f} s  [{np.percentile(bs, 2.5):+.2f}, {np.percentile(bs, 97.5):+.2f}]  n={len(diffs)}')
lines += ['', 'Paired with the transferred grid light (negative = the Midtown-trained light is faster):'] + (pairs or ['  (none yet)'])
gate = []
for k in K:
    f = ROOT / f'research/city_sim/midtown_transfer_20261010/retrain/moe_lg/RL-H_t{k}.log.json'
    if f.exists():
        L = json.loads(f.read_text()); g = [x['gate'] for x in L if x.get('gate') is not None]
        if g:
            gate.append(f't{k}: first {g[0]:.3f}, last {g[-1]:.3f}')
lines += ['', 'A5-lg gate (mean over the last 2 000 decisions of each episode): ' + ('; '.join(gate) if gate else 'no logs yet')]
OUT.write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))
