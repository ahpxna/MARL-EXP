#!/usr/bin/env python3
"""W19 reports (PROTOCOL_CITY_WAVE19_20261008).  Rows: <dir>/gate (OFF_t0_h FT all SUMO drivers; GATE_t<k>_h light k, all SUMO drivers; H4)
and <dir>/conf (R / SV / TG [P5]_t<k>_s<fleet>: fleet without SPaT / forecast q0.1 without adapter / forecast + adapter 1, 0.25).
  stage 1  families B1H, B2H against AH (observation).   D19-1[f] (alpha 0.025 each): SV - R meets every limit (agent fuel upper < 0 under
           HBEFA4 and PHEMlight5, time-loss uppers < +0.5, teleports <= R + 0.1, unfinished <= R): the signal needs no light-side adapter.
           D19-2[f] (alpha 0.025 each): DiD agent time loss (SV - R)_f - (SV - R)_AH, upper < 0: the service harms f's fleet less.
  stage 2  families AD, B1D, B2D against AH (reward), same decisions at alpha 0.05 / 3 each.
  stage 3  families S05, S2, R1, R100 against AH (scale constants), descriptive (95 %), traffic 1400-1409.
Every family: light gate (city time loss vs FT, all SUMO drivers), SV - R, TG - R, TG - SV (HBEFA4 / PHEMlight5), mechanism (mean green,
mean served-lane halting under R and SV).  KM13-1a / 1b on every conf row pair.  W19_SMOKE=1: slot 0, fleet s1413, seed 860."""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
stage, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W19_SMOKE') == '1'
K0 = {'AH': 34, 'B1H': 39, 'B2H': 44, 'AD': 49, 'B1D': 54, 'B2D': 59, 'S05': 64, 'S2': 69, 'R1': 74, 'R100': 79}
FAM = {'1': ['B1H', 'B2H'], '2': ['AD', 'B1D', 'B2D'], '3': ['S05', 'S2', 'R1', 'R100']}[stage]
if SM and os.environ.get('W19_FAMS'):                                  # smoke only: a subset of the stage's families
    FAM = os.environ['W19_FAMS'].split()
Q = {'1': 97.5, '2': 100 - 5 / 3, '3': 95.0}[stage]
SL = (0,) if SM else (0, 1, 2, 3, 4); FS = ('s1413',) if SM else ('s1413', 's1513', 's1613', 's1713')
S = [860] if SM else list(range(1400, 1410 if stage == '3' else 1420))
L = lambda f: tuple(K0[f] + j for j in SL)  # noqa: E731
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
hasTG = lambda f: not f.startswith('B2')  # noqa: E731
Rt = rows(D / 'conf'); G = rows(D / 'gate')
Rt = {k: {s: v[s] for s in S if s in v} for k, v in Rt.items()}; G = {k: {s: v[s] for s in S if s in v} for k, v in G.items()}   # the stage's seeds (stage 3: 1400-1409 of rows that have 1400-1419)
for k in [K0[f] + j for f in ['AH'] + FAM for j in SL]:
    G[f'OFFG_t{k}_h'] = G['OFF_t0_h']
for f in ['AH'] + FAM:
    for a in ('R', 'SV') + (('TG',) if hasTG(f) else ()):
        for l in L(f):
            for fl in FS:
                for s in S:
                    h, p = Rt[K(a)(l, fl)][s], Rt[K(a + 'P5')(l, fl)][s]
                    if any(h[t] != p[t] for t in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                        print('KM13-1a/1b FAIL', a, l, fl, s); sys.exit(1)
out = [f'== W19 stage {stage}: families {FAM} against AH (lights {SL}, fleets {FS}, fresh {S[0]}-{S[-1]}; one-sided level {Q:.3f} %)',
       'KM13-1a PASS, KM13-1b PASS']
res = {}


def meets(a, b, f, q):
    r = V.paired(Rt, K(a), K(b), L(f), FS, S, q=q); r5 = V.paired(Rt, K(a + 'P5'), K(b + 'P5'), L(f), FS, S, q=q)
    ok, tl = V.limits(r, V.tele(Rt, K(a), L(f), FS, S), V.tele(Rt, K(b), L(f), FS, S))
    return ok and r5['fuel_agent']['up'] < 0, r, r5, tl


def mech(f, a):
    g = [Rt[K(a)(l, fl)][s]['green_mean'] for l in L(f) for fl in FS for s in S]; h = [Rt[K(a)(l, fl)][s]['mean_halting'] for l in L(f) for fl in FS for s in S]
    return float(np.mean(g)), float(np.mean(h))


for f in ['AH'] + FAM:
    q = 95.0 if f == 'AH' else Q; e = dict()
    g = V.paired(G, K('GATE'), K('OFFG'), L(f), ('h',), S, q=95.0)
    out += [f'-- {f} (lights t{L(f)[0]}-t{L(f)[-1]})', V.line('light gate GATE - FT, all SUMO drivers (95 %)', g)]
    e['gate_city_tl'] = g['timeloss']; e['gate_pass'] = g['timeloss']['up'] < 0
    for a, b in (('SV', 'R'),) + ((('TG', 'R'), ('TG', 'SV')) if hasTG(f) else ()):
        ok, r, r5, tl = meets(a, b, f, q)
        out += [V.line(f'{a} - {b} (H4, {q:.1f} %)', r), V.line(f'{a}P5 - {b}P5', r5), f'  {tl}; every limit met: {ok}']
        e[f'{a}-{b}'] = dict(meets=ok, H4=r, P5=r5)
    (gR, hR), (gS, hS) = mech(f, 'R'), mech(f, 'SV'); e['mech'] = dict(green_R=gR, green_SV=gS, halt_R=hR, halt_SV=hS)
    out.append(f'  mechanism: mean green R {gR:.2f} s -> SV {gS:.2f} s ({100 * (gS / gR - 1):+.1f} %); mean served-lane halting R {hR:.2f} -> SV {hS:.2f}')
    if f != 'AH':
        dd = V.did(Rt, K('SV'), K('R'), L(f), K('SV'), K('R'), L('AH'), FS, S, q=Q)
        out.append(V.line(f'DiD (SV - R)_{f} - (SV - R)_AH', dd)); e['did'] = dd
        if stage in ('1', '2'):
            d1 = e['SV-R']['meets']; d2 = dd['timeloss_agent']['up'] < 0
            out += [f'  D19-1[{f}] the signal needs no light-side adapter (SV - R meets every limit): {"SHOWN" if d1 else "NOT SHOWN"}',
                    f'  D19-2[{f}] the service harms this signal\'s fleet less than RL-H\'s (DiD agent TL upper < 0): {"SHOWN" if d2 else "NOT SHOWN"}']
            e['D19_1'], e['D19_2'] = d1, d2
    else:
        out.append(f'  R19-A (replication, 95 %): SV - R meets every limit: {e["SV-R"]["meets"]} (expected False); TG - R: {e["TG-R"]["meets"]} (expected True)')
    res[f] = e
sfx = '_smoke' if SM else ''
(D / f'report_w19_s{stage}{sfx}.txt').write_text('\n'.join(out) + '\n'); (D / f'w19_s{stage}{sfx}.json').write_text(json.dumps(res, indent=1, default=float))
print('\n'.join(out))
