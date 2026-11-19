#!/usr/bin/env python3
"""W21-L0 report (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-L0): the untrained W21-L init (SV0) against the grid fleets (SVgrid, W21-B)
and the Midtown-trained fleets (SVm, W21-L).
  KW21-L0b  the four fleet seeds' SV0 cells on t59 are identical in every field (zero residual -> seed-independent rule); then SV0 cells of
            the other lights (s<first> only) are replicated across the fleet axis.  Refuses otherwise (re-run the runner with ALL=1).
  per family: SV0 - R (agent / human time loss, agent fuel), D_rule = SV0 - SVgrid, D_train = SVm - SV0; 95 % crossed bootstrap over
  lights x fleets x days (2 000 draws, seed 0); registered reading on agent time loss.
Usage: CITY_w21l0_report.py <dir> <W21-B dir> <W21-L dir> "<fleets>" "<B2D lights>" "<AH lights>" "<days>" """
import json, os, sys
from pathlib import Path
import numpy as np
D, B, LD = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]); FS, LB, LA, DAYS = ([int(x) for x in a.split()] for a in sys.argv[4:8])
SM = os.environ.get('W21_SMOKE') == '1'; SFX = '_smoke' if SM else ''
SKIP = {'tag', 'src', 'source', 'wall', 'elapsed', 't_wall', 'time', 'fleet', 'fleet_spec'}


def L(p):
    d = json.loads(Path(p).read_text())
    if d.get('status') != 'COMPLETE':
        sys.exit(f'INCOMPLETE {p}')
    return {r['seed']: r for r in d['rows']}


out = [f'== W21-L0: untrained W21-L init (zero residual = GLOSA-L∘σ*) on the full Midtown map (fleets {FS}; B2D {LB}; AH {LA}; days {DAYS})']
for s in FS:
    f = D / 'fleets' / f'init_s{s}.out'
    if f.exists():
        out += [ln for ln in f.read_text().splitlines() if ln.startswith('saved')][:1]
base = L(D / f'MTL0_SV_t59_s{FS[0]}.json'); diff = []
for s in FS[1:]:
    x = L(D / f'MTL0_SV_t59_s{s}.json')
    for d in DAYS:
        diff += [f's{s} day {d} {k}' for k in base[d] if k not in SKIP and x[d].get(k) != base[d][k]]
ok = not diff
out.append(f'KW21-L0b four seeds identical on t59 ({len(FS)} seeds x {len(DAYS)} days): ' + ('PASS' if ok else f'FAIL ({len(diff)} differing fields, e.g. {diff[:4]})'))
if not ok:
    (D / f'report_w21l0{SFX}.txt').write_text('\n'.join(out) + '\nrefused: re-run the runner with ALL=1\n'); print('\n'.join(out)); sys.exit(1)
rng = np.random.default_rng(0)


def row(tag, src, k, s):
    p = src / f'{tag}_t{k}_s{s}.json'
    if tag == 'MTL0_SV' and not p.exists():
        p = src / f'{tag}_t{k}_s{FS[0]}.json'                       # replicated across the fleet axis (KW21-L0b)
    return L(p)


def cube(a, sa, b, sb, ks, m):
    M = np.zeros((len(ks), len(FS), len(DAYS)))
    for i, k in enumerate(ks):
        for j, s in enumerate(FS):
            x, r = row(a, sa, k, s), row(b, sb, k, s)
            for n, d in enumerate(DAYS):
                M[i, j, n] = 100 * (x[d][m] / r[d][m] - 1) if m == 'fuel_agent' else x[d][m] - r[d][m]
    return M


def boot(M):
    bs = [M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]), rng.integers(0, M.shape[2], M.shape[2]))].mean() for _ in range(2000)]
    return float(M.mean()), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


fmt = lambda v: f'{v[0]:+.2f} [{v[1]:+.2f}, {v[2]:+.2f}]'  # noqa: E731
res = {'KW21-L0b': ok}
for fam, ks in (('B2D', LB), ('AH', LA)):
    if not ks:
        continue
    e = {}; out.append(f'-- {fam} (lights {ks})')
    for lab, a, sa, b, sb, ms in (('SV0 (untrained init) - R', 'MTL0_SV', D, 'MTW_R', B, ('timeloss_agent', 'timeloss_human', 'fuel_agent')),
                                  ('SVgrid - R (W21-B)', 'MTW_SV', B, 'MTW_R', B, ('timeloss_agent', 'fuel_agent')),
                                  ('SVm - R (W21-L)', 'MTL_SV', LD, 'MTW_R', B, ('timeloss_agent', 'fuel_agent')),
                                  ('D_rule = SV0 - SVgrid', 'MTL0_SV', D, 'MTW_SV', B, ('timeloss_agent', 'timeloss_human', 'fuel_agent')),
                                  ('D_train = SVm - SV0', 'MTL_SV', LD, 'MTL0_SV', D, ('timeloss_agent', 'timeloss_human', 'fuel_agent'))):
        r = {m: boot(cube(a, sa, b, sb, ks, m)) for m in ms}; e[lab.split()[0]] = r
        out.append(f'  {lab}: agent TL {fmt(r["timeloss_agent"])} s/veh' + (f', human TL {fmt(r["timeloss_human"])}' if 'timeloss_human' in r else '')
                   + f', agent fuel {fmt(r["fuel_agent"])} %')
    dr, dt = e['D_rule']['timeloss_agent'], e['D_train']['timeloss_agent']
    rule_neg, train_neg = dr[2] < 0, dt[2] < 0; train_zero = dt[1] <= 0 <= dt[2]; rule_zero_or_up = dr[2] >= 0
    rd = ('both: dropping the grid residual and learning the map' if rule_neg and train_neg else
          'the gain is dropping the grid residual' if rule_neg and train_zero else
          'the gain is learning the map' if train_neg and rule_zero_or_up else 'unresolved')
    out.append(f'  reading: {rd}'); e['reading'] = rd; res[fam] = e
if SM:
    out.append('(smoke: truncated episodes against full-length W21-B / W21-L rows; numbers meaningless, pipeline check only)')
(D / f'report_w21l0{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w21l0{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
