#!/usr/bin/env python3
"""W21-F report (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-F): the forecast alone (SV) against R on recorded Salt Lake demand, with
F1-4's TG and HARM rows (copied from git into <dir>/f14) on the same cells.  KW21-F1: the rerun R equals F1-4's R (time losses, fuel,
teleports, unfinished, action digest; skipped in smoke).  Descriptive, 95 % bootstrap over fleets x days.  Usage: CITY_w21f_report.py <dir>"""
import json, os, sys
from pathlib import Path
import numpy as np
D = Path(sys.argv[1]); SM = os.environ.get('W21_SMOKE') == '1'; SFX = '_smoke' if SM else ''
FS = (13,) if SM else (13, 113)
L = lambda p: {r['seed']: r for r in json.loads(Path(p).read_text())['rows']} if json.loads(Path(p).read_text()).get('status') == 'COMPLETE' else sys.exit(f'INCOMPLETE {p}')  # noqa: E731
A = {a: {s: L(D / 'conf' / f'{a}_t11_s{s}.json') for s in FS} for a in ('R', 'SV')}
A.update({f'{a}14': {s: L(D / 'f14' / f'{a}_t11_s{s}.json') for s in FS} for a in ('R', 'TG', 'HARM')})
DAYS = sorted(A['R'][FS[0]]); out = [f'== W21-F: forecast alone on recorded Salt Lake demand (400S & 200W, RLW t11, fleets {FS}, {len(DAYS)} CONF days)']
F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports', 'unfinished', 'action_digest')
if not SM:
    bad = [(s, d, f) for s in FS for d in DAYS for f in F if A['R'][s][d][f] != A['R14'][s][d][f]]
    out.append('KW21-F1 rerun R = F1-4 R: ' + ('PASS' if not bad else f'FAIL {bad[:6]}'))
rng = np.random.default_rng(0)


def d(a, b, m, pct=False):
    M = np.array([[100 * (A[a][s][x][m] / A[b][s][x][m] - 1) if pct else A[a][s][x][m] - A[b][s][x][m] for x in DAYS] for s in FS])
    bs = [M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]))].mean() for _ in range(2000)]
    return f'{M.mean():+.2f} [{np.percentile(bs, 2.5):+.2f}, {np.percentile(bs, 97.5):+.2f}]'


ref = 'R'
for a in ('SV', 'TG14', 'HARM14'):
    if SM and a != 'SV':
        continue
    out.append(f'  {a} - R: agent TL {d(a, ref, "timeloss_agent")} s/veh | city TL {d(a, ref, "timeloss")} | human TL {d(a, ref, "timeloss_human")} | agent fuel {d(a, ref, "fuel_agent", True)} %')
for a in ('R', 'SV') + (() if SM else ('TG14', 'HARM14')):
    g = np.mean([A[a][s][x]['green_mean'] for s in FS for x in DAYS]); h = np.mean([A[a][s][x]['mean_halting'] for s in FS for x in DAYS])
    out.append(f'  {a}: mean green {g:.2f} s, served-lane halting {h:.2f}')
(D / f'report_w21f{SFX}.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
