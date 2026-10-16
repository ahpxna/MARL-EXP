#!/usr/bin/env python3
"""W21-L report (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-L): fleets trained on the full Midtown map (MTL) against the grid fleets.
<dir>: MTL_SV_t<k>_s<f> and MTL_R_t59_s<f1> rows, fleets/*.log.json (training curves); <W21-B dir>: MTW_R / MTW_SV rows (grid fleets).
  KW21-L1  MTL_R (Midtown fleet without SPaT) = MTW_R (grid fleet without SPaT) on t59, first fleet seed: R is fleet-independent
  per family (B2D, AH): SVm - R and SVgrid - R (agent / human time loss, agent fuel), and SVm - SVgrid; 95 % bootstrap over lights x
  fleets x days.  Reading: avoided if SVm - R agent TL upper < +0.5 with fuel saved; reduced if below half of the grid fleets' cost.
Usage: CITY_w21l_report.py <dir> <W21-B dir> "<fleets>" "<B2D lights>" "<AH lights>" "<days>" """
import json, os, sys
from pathlib import Path
import numpy as np
D, B = Path(sys.argv[1]), Path(sys.argv[2]); FS, LB, LA, DAYS = ([int(x) for x in a.split()] for a in sys.argv[3:7])
SM = os.environ.get('W21_SMOKE') == '1'; SFX = '_smoke' if SM else ''
F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports', 'unfinished', 'action_digest')


def L(p):
    d = json.loads(Path(p).read_text())
    if d.get('status') != 'COMPLETE':
        sys.exit(f'INCOMPLETE {p}')
    return {r['seed']: r for r in d['rows']}


out = [f'== W21-L: fleets trained on the full Midtown map (fleets {FS}; B2D {LB}; AH {LA}; days {DAYS})']; res = {}
a, b = L(D / f'MTL_R_t59_s{FS[0]}.json'), L(B / f'MTW_R_t59_s{FS[0]}.json')
same = sum(all(a[d][f] == b[d][f] for f in F) for d in DAYS) if not SM else None
out.append(f'KW21-L1 Midtown-fleet R = grid-fleet R (t59, s{FS[0]}): ' + (f'{same} of {len(DAYS)} days identical' if not SM else 'skipped in smoke'))
for s in FS:
    lg = D / 'fleets' / f'MTL_s{s}.log.json'
    if lg.exists():
        rows = json.loads(lg.read_text()); r = [x['mean_r'] for x in rows]
        out.append(f'  training s{s}: {len(rows)} episodes, mean reward first 10 {np.mean(r[:10]):.3f}, last 10 {np.mean(r[-10:]):.3f}, teleports last 10 {np.mean([x["teleports"] for x in rows[-10:]]):.1f}')
rng = np.random.default_rng(0)


def cube(tag, src, ks, m, ref='R'):
    M = np.zeros((len(ks), len(FS), len(DAYS)))
    for i, k in enumerate(ks):
        for j, s in enumerate(FS):
            x = L(src / f'{tag}_t{k}_s{s}.json'); r = L(B / f'MTW_{ref}_t{k}_s{s}.json') if ref else None
            for n, d in enumerate(DAYS):
                M[i, j, n] = (100 * (x[d][m] / r[d][m] - 1) if m == 'fuel_agent' else x[d][m] - r[d][m]) if r else x[d][m]
    return M


def boot(M):
    bs = [M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]), rng.integers(0, M.shape[2], M.shape[2]))].mean() for _ in range(2000)]
    return float(M.mean()), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


fmt = lambda v: f'{v[0]:+.2f} [{v[1]:+.2f}, {v[2]:+.2f}]'  # noqa: E731
for fam, ks in (('B2D', LB), ('AH', LA)):
    e = {}; out.append(f'-- {fam} (lights {ks})')
    for lab, tag, src in (('SVm (Midtown fleets) - R', 'MTL_SV', D), ('SVgrid (grid fleets, W21-B) - R', 'MTW_SV', B)):
        r = {m: boot(cube(tag, src, ks, m)) for m in ('timeloss_agent', 'timeloss_human', 'fuel_agent')}; e[tag] = r
        out.append(f'  {lab}: agent TL {fmt(r["timeloss_agent"])} s/veh, human TL {fmt(r["timeloss_human"])}, agent fuel {fmt(r["fuel_agent"])} %')
    dm = {}
    for m in ('timeloss_agent', 'fuel_agent'):
        A_, G_ = cube('MTL_SV', D, ks, m, ref=None), cube('MTW_SV', B, ks, m, ref=None)
        dm[m] = boot(100 * (A_ / G_ - 1) if m == 'fuel_agent' else A_ - G_)
    e['SVm_minus_SVgrid'] = dm; out.append(f'  SVm - SVgrid: agent TL {fmt(dm["timeloss_agent"])} s/veh, agent fuel {fmt(dm["fuel_agent"])} %')
    up = e['MTL_SV']['timeloss_agent'][2]; pt = e['MTL_SV']['timeloss_agent'][0]; g = e['MTW_SV']['timeloss_agent'][0]; fu = e['MTL_SV']['fuel_agent'][2]
    out.append('  reading: ' + ('the Midtown-trained fleets AVOID the trade (agent TL upper < +0.5, fuel saved)' if up < 0.5 and fu < 0 else
                                ('the trade is REDUCED (below half of the grid fleets\' cost)' if pt < 0.5 * g else 'the trade is NOT reduced by training on the map')))
    res[fam] = e
(D / f'report_w21l{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w21l{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
