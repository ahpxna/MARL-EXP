#!/usr/bin/env python3
"""POST-HOC re-analysis of W22-A (C-259; not registered): the size-based decision with window-weighted per-day tau (E2) instead of the
registered green-pooled per-signal-day tau (E1), which LeanCityOwnerTestV1.estimator_le_window_contrast shows is biased downward when
control windows are rare.  Same rows, same rule (delta 0.5 s, Student-t 95 % after n = 2..10 days; CS descriptive), same truth labels.
Also E1 / E2 / E4 tau for W22 (grid4, days 1400-1409) and W22-C (W17).  Writes <a dir>/report_w22a_posthoc.txt and w22a_posthoc.json."""
import json, math
from pathlib import Path
import numpy as np
B = Path('research/city_sim/w22_20261017'); SRC = {'w19': Path('research/city_sim/w19_20261008/conf'), 'w20': Path('research/city_sim/w20_20261009/conf'),
                                                  'w17': Path('research/city_sim/w21_20261015/w17/conf')}
T975 = [None, 12.706, 4.303, 3.182, 2.776, 2.571, 2.447, 2.365, 2.306, 2.262]; DELTA, ALPHA = 0.5, 0.05


def L(p):
    return {r['seed']: r for r in json.load(open(p))['rows']}


def tau(win, kind):
    acc = {}
    for tid, w, _na, _da, nl, dl, _t, _c, a in win:
        if nl > 0:
            acc.setdefault(str(tid), {0: [], 1: []})[a].append((nl, dl))
    out = []
    for s in acc.values():
        if s[0] and s[1]:
            m = [sum(d for n, d in s[g]) / sum(n for n, d in s[g]) if kind == 'E1' else float(np.mean([d / n for n, d in s[g]])) for g in (0, 1)]
            out.append(m[1] - m[0])
    return float(np.mean(out)) if out else float('nan')


def decide(x, kind):
    x = [v for v in x if not math.isnan(v)]
    for n in range(2, len(x) + 1):
        m, sd = float(np.mean(x[:n])), float(np.std(x[:n], ddof=1))
        h = T975[n - 1] * sd / math.sqrt(n) if kind == 't' else sd * math.sqrt((n + 1) * math.log((n + 1) / ALPHA ** 2)) / n
        if m - h > DELTA:
            return 'exposed', n
        if m + h < DELTA:
            return 'not exposed', n
    return 'undecided', None


out = ['== POST HOC (not registered): W22-A decisions with the window-weighted per-day tau (E2); registered E1 table in report_w22a.txt']; res = {}
FAMS = [('RMP', range(94, 99), 'w20'), ('SRL', range(84, 89), 'w20'), ('RDQ', range(89, 94), 'w20'), ('AH', range(34, 39), 'w19'), ('RWV', range(99, 104), 'w20')]
for fam, ks, src in FAMS:
    out.append(f'-- {fam}'); res[fam] = {}
    for p in (50, 80, 95):
        U = []
        for k in ks:
            for s in (1413, 1513):
                S = L(B / 'a' / f'SWBp{p}_t{k}_s{s}.json'); R = L(SRC[src] / f'R_t{k}_s{s}.json'); V = L(SRC[src] / f'SV_t{k}_s{s}.json')
                days = range(1410, 1420); x = [tau(S[d]['w22_win']['rows'], 'E2') for d in days]
                truth = float(np.mean([V[d]['green_mean'] - R[d]['green_mean'] for d in days])); lab = 'exposed' if truth > DELTA else 'not exposed'
                U.append(dict(tau=float(np.nanmean(x)), lab=lab, t=decide(x, 't'), cs=decide(x, 'cs')))
        e = {}
        for kd in ('t', 'cs'):
            labs = [u[kd][0] for u in U]; ns = [u[kd][1] for u in U if u[kd][1]]
            e[kd] = dict(exposed=labs.count('exposed'), not_exposed=labs.count('not exposed'), undecided=labs.count('undecided'),
                         wrong=sum(u[kd][0] not in ('undecided', u['lab']) for u in U), median=float(np.median(ns)) if ns else None, max=max(ns) if ns else None)
        res[fam][p] = e
        out.append(f'  p {p / 100:.2f}: tau E2 {np.mean([u["tau"] for u in U]):+.2f} | t-rule: exposed {e["t"]["exposed"]}, not {e["t"]["not_exposed"]}, undecided '
                   f'{e["t"]["undecided"]}, WRONG {e["t"]["wrong"]}, days median {e["t"]["median"]} max {e["t"]["max"]} | CS: exposed {e["cs"]["exposed"]}, not '
                   f'{e["cs"]["not_exposed"]}, undecided {e["cs"]["undecided"]}, wrong {e["cs"]["wrong"]}, median {e["cs"]["median"]}')
out.append('== tau by estimator (E1 registered pooled per signal-day; E2 window-weighted per day; E4 window-weighted, each signal pooled over all days)')
for lab, d, fs, days, fams in (('W22 grid4 SWB p 0.5', B / 'panel', (1413, 1513), range(1400, 1410), [('RMP', range(94, 99), 'w20'), ('AH', range(34, 39), 'w19'), ('RWV', range(99, 104), 'w20')]),
                                ('W22-C W17 SWB p 0.5', B / 'w17', (2213, 2313), range(1420, 1430), [('RMP', range(94, 99), 'w17'), ('AH', range(34, 39), 'w17'), ('RWV', range(99, 104), 'w17')])):
    for fam, ks, src in fams:
        e1, e2, e4, tr = [], [], [], []
        for k in ks:
            for s in fs:
                S = L(d / f'SWB_t{k}_s{s}.json'); R = L(SRC[src] / f'R_t{k}_s{s}.json'); V = L(SRC[src] / f'SV_t{k}_s{s}.json'); allw = []
                for dd in days:
                    w = S[dd]['w22_win']['rows']; e1.append(tau(w, 'E1')); e2.append(tau(w, 'E2')); allw += [[f'{r[0]}'] + r[1:] for r in w]
                    tr.append(V[dd]['green_mean'] - R[dd]['green_mean'])
                e4.append(tau(allw, 'E2'))
        out.append(f'  {lab} {fam}: E1 {np.nanmean(e1):+.2f}, E2 {np.nanmean(e2):+.2f}, E4 {np.mean(e4):+.2f}; truth {np.mean(tr):+.2f}')
(B / 'a' / 'report_w22a_posthoc.txt').write_text('\n'.join(out) + '\n'); (B / 'a' / 'w22a_posthoc.json').write_text(json.dumps(res, indent=1)); print('\n'.join(out))
