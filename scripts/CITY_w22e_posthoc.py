#!/usr/bin/env python3
"""POST-HOC analyses of existing W22 rows (17/10/2026; not registered, no new run).  Writes research/city_sim/w22_20261017/e/report_w22e_posthoc.txt.
 (i)  exposure-mapping regression on switchback windows: window mean green (late greens, window-weighted) on own assignment Z(j,w), own previous
      window Z(j,w-1) and neighbours' mean Z(nb(j),w), with signal x run fixed effects; implied all-vs-none green change b_own + b_prev + b_nbr
      against the global SV - R green change.  grid4 (W22 panel, W22-A p 0.5) and W17 (W22-C).
 (ii) day-level randomisation from the SV / R rows: each day SV or R w.p. 0.5 (unpaired days), estimate = mean SV days - mean R days; its sd
      over 2 000 random assignments, for n = 10 and 20 days, against the global effect.
 (iii) A/B decomposition: control spillover C_p - R against p x (humans' global change SV - R); treated spillover T_p - SV against (1 - p);
      two-share linear extrapolation GTE_hat = T1_hat - C0_hat from MIX at p1 < p2 against GTE (W22-B grid4)."""
import json
from pathlib import Path
import numpy as np
B = Path('research/city_sim/w22_20261017'); OUT = B / 'e'; OUT.mkdir(exist_ok=True)
SRC = {'w19': Path('research/city_sim/w19_20261008/conf'), 'w20': Path('research/city_sim/w20_20261009/conf'), 'w17': Path('research/city_sim/w21_20261015/w17/conf')}
G4 = [('RMP', range(94, 99), 'w20'), ('AH', range(34, 39), 'w19'), ('RWV', range(99, 104), 'w20')]
W17F = [('RMP', range(94, 99), 'w17'), ('AH', range(34, 39), 'w17'), ('RWV', range(99, 104), 'w17')]
_C = {}


def L(p):
    p = str(p)
    if p not in _C:
        _C[p] = {r['seed']: r for r in json.load(open(p))['rows']}
    return _C[p]


rng = np.random.default_rng(0); out = []


def nbrs(t):
    c, r = t[0], int(t[1]); n = []
    for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        cc, rr = chr(ord(c) + dc), r + dr
        if 'A' <= cc <= 'D' and 0 <= rr <= 3:
            n.append(f'{cc}{rr}')
    return n


def prep(win):
    """one run's windows -> within-signal demeaned (y, X) arrays (signal x run fixed effects)."""
    Y, X = [], []
    for win in [win]:
        Z = {(r[0], r[1]): r[8] for r in win}; grp = {}
        for tid, w, _na, _da, nl, dl, _t, _c, a in win:
            if nl <= 0 or (tid, w - 1) not in Z:
                continue
            nb = [Z[(x, w)] for x in nbrs(tid) if (x, w) in Z]
            grp.setdefault(tid, []).append((dl / nl, a, Z[(tid, w - 1)], np.mean(nb) if nb else 0.5))
        for rows in grp.values():
            if len(rows) < 3:
                continue
            A = np.array(rows, float); A = A - A.mean(axis=0); Y += list(A[:, 0]); X += list(A[:, 1:])
    return np.array(Y), np.array(X).reshape(-1, 3)


def regress(preps):
    Y = np.concatenate([p[0] for p in preps]); X = np.concatenate([p[1] for p in preps]); b, *_ = np.linalg.lstsq(X, Y, rcond=None); return b, len(Y)


out.append('== (i) exposure-mapping regression of switchback windows (POST HOC): coefficients own / previous window / neighbours, implied total vs truth')
for lab, d, fs, days, fams, tag in (('grid4 W22 days 1400-1409', B / 'panel', (1413, 1513), range(1400, 1410), G4, 'SWB'),
                                    ('grid4 W22-A p 0.5 days 1410-1419', B / 'a', (1413, 1513), range(1410, 1420), G4 + [('SRL', range(84, 89), 'w20'), ('RDQ', range(89, 94), 'w20')], 'SWBp50'),
                                    ('W17 W22-C days 1420-1429', B / 'w17', (2213, 2313), range(1420, 1430), W17F, 'SWB')):
    for fam, ks, src in fams:
        units = [(k, s) for k in ks for s in fs]; P = {u: [prep(L(d / f'{tag}_t{u[0]}_s{u[1]}.json')[dd]['w22_win']['rows']) for dd in days] for u in units}
        b, n = regress([x for u in units for x in P[u]]); bs = []
        for _ in range(1000):                                              # bootstrap over units (policy x fleet)
            bs.append(regress([x for i in rng.integers(0, len(units), len(units)) for x in P[units[i]]])[0].sum())
        tr = np.mean([L(SRC[src] / f'SV_t{k}_s{s}.json')[dd]['green_mean'] - L(SRC[src] / f'R_t{k}_s{s}.json')[dd]['green_mean'] for k in ks for s in fs for dd in days])
        out.append(f'  {lab} {fam}: own {b[0]:+.2f}, prev {b[1]:+.2f}, nbr {b[2]:+.2f} -> total {b.sum():+.2f} [{np.percentile(bs, 2.5):+.2f}, {np.percentile(bs, 97.5):+.2f}] '
                   f'vs truth {tr:+.2f} (windows {n})')
out.append('== (ii) day-level randomisation from SV / R rows (unpaired days; POST HOC): estimate sd over random assignments, vs |GTE|')
for lab, fs, fams, days in (('grid4', (1413, 1513), G4, list(range(1400, 1420))), ('W17', (2213, 2313), W17F, list(range(1420, 1440)))):
    for fam, ks, src in fams:
        units = [(L(SRC[src] / f'SV_t{k}_s{s}.json'), L(SRC[src] / f'R_t{k}_s{s}.json')) for k in ks for s in fs]
        gte = np.mean([sv[d]['timeloss_agent'] - r[d]['timeloss_agent'] for sv, r in units for d in days])
        for n in (10, 20):
            est = []
            for _ in range(2000):
                sv, r = units[rng.integers(0, len(units))]; dd = rng.choice(days, n, replace=False); z = rng.random(n) < 0.5
                if z.all() or (~z).all():
                    continue
                est.append(np.mean([sv[d]['timeloss_agent'] for d, t in zip(dd, z) if t]) - np.mean([r[d]['timeloss_agent'] for d, t in zip(dd, z) if not t]))
            est = np.array(est); out.append(f'  {lab} {fam} n={n} days: mean {est.mean():+.2f} (GTE {gte:+.2f}), sd {est.std():.2f}, |GTE|/sd {abs(gte) / est.std():.1f}')
out.append('== (iii) A/B decomposition (POST HOC, W22-B grid4): C_p - R vs p*H (H = humans SV - R), T_p - SV vs (1-p); two-share extrapolation')
for fam, ks, src in G4:
    fs = (1413, 1513); days = range(1400, 1410)
    R = {(k, s): L(SRC[src] / f'R_t{k}_s{s}.json') for k in ks for s in fs}; V = {(k, s): L(SRC[src] / f'SV_t{k}_s{s}.json') for k in ks for s in fs}
    H = np.mean([V[u][d]['timeloss_human'] - R[u][d]['timeloss_human'] for u in R for d in days]); GTE = np.mean([V[u][d]['timeloss_agent'] - R[u][d]['timeloss_agent'] for u in R for d in days])
    TP, CP = {}, {}
    for p in (10, 30, 50, 70, 90):
        X = {u: L((B / 'panel' / f'MIX_t{u[0]}_s{u[1]}.json') if p == 50 else (B / 'b' / f'MIXp{p}_t{u[0]}_s{u[1]}.json')) for u in R}
        TP[p] = np.mean([X[u][d]['w22']['tl_T'] for u in R for d in days]); CP[p] = np.mean([X[u][d]['w22']['tl_C'] for u in R for d in days])
    T1 = np.mean([V[u][d]['timeloss_agent'] for u in R for d in days]); C0 = np.mean([R[u][d]['timeloss_agent'] for u in R for d in days])
    out.append(f'  {fam}: H (humans SV - R) {H:+.2f}; GTE {GTE:+.2f}')
    out.append('     C_p - R  : ' + '  '.join(f'p{p / 100:.1f} {CP[p] - C0:+.2f} (pH {p / 100 * H:+.2f})' for p in TP))
    out.append('     T_p - SV : ' + '  '.join(f'p{p / 100:.1f} {TP[p] - T1:+.2f}' for p in TP))
    for p1, p2 in ((30, 70), (10, 90), (30, 50), (50, 70)):
        a1, a2 = p1 / 100, p2 / 100; t1 = TP[p2] + (1 - a2) * (TP[p2] - TP[p1]) / (a2 - a1); c0 = CP[p1] - a1 * (CP[p2] - CP[p1]) / (a2 - a1)
        out.append(f'     two-share ({a1:.1f}, {a2:.1f}): GTE_hat {t1 - c0:+.2f} vs GTE {GTE:+.2f} (naive A/B at 0.5: {TP[50] - CP[50]:+.2f})')
for lab, fams, fs, days in (('W17 (W22-C, p 0.5)', W17F, (2213, 2313), range(1420, 1430)),):
    for fam, ks, src in fams:
        R = {(k, s): L(SRC[src] / f'R_t{k}_s{s}.json') for k in ks for s in fs}; V = {(k, s): L(SRC[src] / f'SV_t{k}_s{s}.json') for k in ks for s in fs}
        X = {u: L(B / 'w17' / f'MIX_t{u[0]}_s{u[1]}.json') for u in R}
        H = np.mean([V[u][d]['timeloss_human'] - R[u][d]['timeloss_human'] for u in R for d in days])
        cp = np.mean([X[u][d]['w22']['tl_C'] - R[u][d]['timeloss_agent'] for u in R for d in days])
        out.append(f'  {lab} {fam}: C_0.5 - R {cp:+.2f} vs 0.5 H {0.5 * H:+.2f} (H {H:+.2f})')
(OUT / 'report_w22e_posthoc.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
