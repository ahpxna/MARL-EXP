#!/usr/bin/env python3
"""W13-1b report (PROTOCOL_CITY_WAVE13_20261006): agent fuel by driving mode, arm - R, under HBEFA4 (H4) and PHEMlight5 (P5).
Rows <dir>/diag: D<arm>[P5]_t<k>_s1013 (seeds 800-803; arms R, HYB, TSI, F1B) and DRFT[P5]_s1013 / DPLFT[P5]_s1013 (FT, seeds 820-823).
Per arm and model the quantity is agent fuel per agent trip in each (acceleration class x speed band) cell, grid mg / number of agent trips
(from the run's window counts), averaged over lights and seeds; the cells add up to the agent fuel per trip (up to the KM13-1b ratio).
Checks: KM13-1b (grid / tripinfo in [0.98, 1.02] on every row); KM13-1a (P5 dynamics == H4); KM13-1c (H4 D-rows == W8-2 rows for R, TSI,
F1B on seeds 800-803).  Registered reading on Delta_P5(TSI - R) (see protocol).  Usage: CITY_w13_diag_report.py [<dir>] (W13_SMOKE=1)"""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'research/city_sim/w13_20261006'; F2 = ROOT / 'research/city_sim/w8_20261005/fresh2'
SM = os.environ.get('W13_SMOKE') == '1'
LT = (14,) if SM else (14, 15, 16, 17, 18); S = [800] if SM else [800, 801, 802, 803]; SF = [820] if SM else [820, 821, 822, 823]
AC = ('a<-0.1', '|a|<=0.1', 'a>0.1'); SB = ('v<0.1', '0.1-2', '2-5', '5-10', '>=10')
Rt = rows(D / 'diag'); out = ['== W13-1b fuel by driving mode (agents; mg per agent trip; FRESH2 t14-t18 x s1013 x 800-803; FT contrast s1013 x 820-823)']
bad = [f'{k} s{s}: {r.get("modes_ratio_all")}' for k, v in Rt.items() for s, r in v.items() if not (r.get('modes_ratio_all') and 0.98 <= r['modes_ratio_all'] <= 1.02)]
if bad:
    print('KM13-1b FAIL:', bad[:10]); sys.exit(1)
out.append(f'KM13-1b PASS on {sum(len(v) for v in Rt.values())} rows (grid / tripinfo in [0.98, 1.02])')
TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished')
for k in [k for k in Rt if 'P5' in k]:
    h = k.replace('P5', '')
    for s in Rt[k]:
        if any(Rt[k][s][q] != Rt[h][s][q] for q in TW):
            print('KM13-1a FAIL', k, s); sys.exit(1)
out.append('KM13-1a PASS (every P5 row equals its H4 twin in time losses, n, teleports, unfinished)')
if not SM:
    W8 = rows(F2 / 'conf'); mism = []
    for arm, w8 in (('R', 'R'), ('TSI', 'TSI'), ('F1B', 'F1B')):
        for t in LT:
            a, b = Rt[f'D{arm}_t{t}_s1013'], W8[f'{w8}_t{t}_s1013']
            mism += [f'{arm} t{t} s{s}' for s in S if any(a[s][q] != b[s][q] for q in ('timeloss', 'fuel', 'fuel_agent', 'n'))]
    if mism:
        print('KM13-1c FAIL', mism[:10]); sys.exit(1)
    out.append('KM13-1c PASS (H4 diagnostic rows equal the W8-2 rows for R, TSI, F1B)')


def per_trip(r):
    """agent grid fuel (mg) per agent trip; agent trips from fuel_agent and the agent grid total is not available -> use the cohort counts."""
    na = sum(w[0] for w in r['window_counts_sums'].values())
    return np.array([[c[0] for c in row] for row in r['modes']['agent']]) / max(1, na), na


def mean_grid(keys, seeds):
    return np.mean([per_trip(Rt[k][s])[0] for k in keys for s in seeds], axis=0)


def table(title, A, B):
    d = A - B; out.append(f'  {title}: total {d.sum() / 1000:+.1f} g/trip (A {A.sum() / 1000:.1f}, R {B.sum() / 1000:.1f})')
    out.append('      ' + ''.join(f'{x:>10}' for x in SB))
    for i, ac in enumerate(AC):
        out.append(f'  {ac:>9} ' + ''.join(f'{d[i, j] / 1000:>+10.2f}' for j in range(5)))
    return d


res = {}
for em, sfx in (('HBEFA4', ''), ('PHEMlight5', 'P5')):
    out.append(f'-- {em}')
    Rg = mean_grid([f'DR{sfx}_t{t}_s1013' for t in LT], S)
    for arm in ('HYB', 'TSI', 'F1B'):
        res[(arm, em)] = table(f'{arm} - R', mean_grid([f'D{arm}{sfx}_t{t}_s1013' for t in LT], S), Rg)
    res[('PLFT', em)] = table('FT: fleet - sigma* (exact SPaT)', mean_grid([f'DPLFT{sfx}_s1013'], SF), mean_grid([f'DRFT{sfx}_s1013'], SF))
d5 = res[('TSI', 'PHEMlight5')]; d4 = res[('TSI', 'HBEFA4')]; pos = d5[d5 > 0].sum()
reacc = d5[2, 2:][d5[2, 2:] > 0].sum(); slow = d5[1, 1:3][d5[1, 1:3] > 0].sum(); idle4 = d4[:, 0].sum(); idle5 = d5[:, 0].sum()
reading = ('re-acceleration' if pos > 0 and reacc > 0.5 * pos else 'slow running' if pos > 0 and slow > 0.5 * pos else
           'idle credit' if idle4 < 0 and abs(idle4) > abs(d4.sum()) and abs(idle5) < 0.5 * abs(idle4) else 'mixed')
out += [f'Reading on Delta_P5(TSI - R): positive part {pos / 1000:+.2f} g/trip; re-acceleration cells (a>0.1, v>=2) {reacc / 1000:+.2f}; '
        f'slow running cells (|a|<=0.1, 0.1<=v<5) {slow / 1000:+.2f}; idle cells H4 {idle4 / 1000:+.2f} vs P5 {idle5 / 1000:+.2f}; total H4 {d4.sum() / 1000:+.2f}, '
        f'P5 {d5.sum() / 1000:+.2f}', f'REGISTERED READING: {reading}']
(D / 'diag' / 'report_diag.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
