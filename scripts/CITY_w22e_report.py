#!/usr/bin/env python3
"""W22-E report (PROTOCOL_CITY_WAVE22_20261017, Amendment W22-E).
  E1  two-share extrapolation from MIX at (0.3, 0.7): T1_hat = T(.7) + .3 (T(.7) - T(.3)) / .4, C0_hat = C(.3) - .3 (C(.7) - C(.3)) / .4,
      GTE_hat = T1_hat - C0_hat against GTE = SV - R agent time loss; per (light, fleet, day) then crossed bootstrap 95 % (2 000, seed 0);
      pair (0.5, 0.7) descriptive.  grid4 SRL / RDQ (MIX p 0.5 in <dir>/g4) and W17 RMP / AH / RWV (MIX p 0.5 from W22-C, w22_20261017/w17).
  E2  naive per-vehicle A/B at p 0.5: bias = (T - C) - GTE (grid4 SRL / RDQ).   E4  control spillover C(p) - R against the sign of H.
  E3  W17 NSW: network green contrast = mean over treated windows minus control windows of the window's network-mean green (greens >= 60 s
      into a window, window-weighted), against the global SV - R green change and the per-signal SWB tau (W22-C).
Usage: CITY_w22e_report.py <dir> "<grid4 FAM:k0-k1 ...>" "<grid4 fleets>" "<grid4 days>" "<W17 FAM:k0-k1 ...>" "<W17 fleets>" "<W17 days>" """
import json, os, sys
from pathlib import Path
import numpy as np
D = Path(sys.argv[1]); GF = [x.split(':') for x in sys.argv[2].split()]; GS = [int(x) for x in sys.argv[3].split()]; GD = [int(x) for x in sys.argv[4].split()]
WF = [x.split(':') for x in sys.argv[5].split()]; WS = [int(x) for x in sys.argv[6].split()]; WD = [int(x) for x in sys.argv[7].split()]
SM = os.environ.get('W22_SMOKE') == '1'; SFX = '_smoke' if SM else ''; B = Path('research/city_sim/w22_20261017')
G20 = Path('research/city_sim/w20_20261009/conf'); G19 = Path('research/city_sim/w19_20261008/conf'); A17 = Path('research/city_sim/w21_20261015/w17/conf')
rng = np.random.default_rng(0)
_C = {}


def L(p):
    p = str(p)
    if p not in _C:
        d = json.loads(Path(p).read_text())
        if d.get('status') != 'COMPLETE':
            sys.exit(f'INCOMPLETE {p}')
        _C[p] = {r['seed']: r for r in d['rows']}
    return _C[p]


def boot(M):
    bs = [np.nanmean(M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]), rng.integers(0, M.shape[2], M.shape[2]))]) for _ in range(2000)]
    return float(np.nanmean(M)), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


fmt = lambda v: f'{v[0]:+.2f} [{v[1]:+.2f}, {v[2]:+.2f}]'  # noqa: E731
contains0 = lambda v: v[1] <= 0 <= v[2]  # noqa: E731
out = ['== W22-E: two-share extrapolation, naive A/B for SRL / RDQ, W17 network switchback']; res = {}


def two_share(T3, C3, T7, C7, a1=0.3, a2=0.7):
    t1 = T7 + (1 - a2) * (T7 - T3) / (a2 - a1); c0 = C3 - a1 * (C7 - C3) / (a2 - a1); return t1 - c0


for world, fams, fs, days, gt, mix50 in (('grid4', GF, GS, GD, None, D / 'g4'), ('W17', WF, WS, WD, A17, B / 'w17' if not SM else D / 'w17')):
    for fam, kr in fams:
        k0, k1 = (int(x) for x in kr.split('-')); ks = list(range(k0, k1 + 1)); src = gt or (G19 if k0 < 84 else G20)
        sub = D / ('g4' if world == 'grid4' else 'w17'); shape = (len(ks), len(fs), len(days))
        GTE, E37, E57, DM, H = (np.zeros(shape) for _ in range(5)); SC = {30: np.zeros(shape), 50: np.zeros(shape), 70: np.zeros(shape)}
        for i, k in enumerate(ks):
            for j, s in enumerate(fs):
                R, V = L(src / f'R_t{k}_s{s}.json'), L(src / f'SV_t{k}_s{s}.json')
                X = {30: L(sub / f'MIXp30_t{k}_s{s}.json'), 70: L(sub / f'MIXp70_t{k}_s{s}.json'),
                     50: L(sub / f'MIXp50_t{k}_s{s}.json') if world == 'grid4' else (L(mix50 / f'MIX_t{k}_s{s}.json') if not SM else None)}
                for n, d in enumerate(days):
                    g = V[d]['timeloss_agent'] - R[d]['timeloss_agent']; GTE[i, j, n] = g; H[i, j, n] = V[d]['timeloss_human'] - R[d]['timeloss_human']
                    w = {p: X[p][d]['w22'] for p in X if X[p] is not None}
                    E37[i, j, n] = two_share(w[30]['tl_T'], w[30]['tl_C'], w[70]['tl_T'], w[70]['tl_C']) - g
                    if 50 in w:
                        E57[i, j, n] = two_share(w[50]['tl_T'], w[50]['tl_C'], w[70]['tl_T'], w[70]['tl_C'], 0.5, 0.7) - g
                        DM[i, j, n] = (w[50]['tl_T'] - w[50]['tl_C']) - g; SC[50][i, j, n] = w[50]['tl_C'] - R[d]['timeloss_agent']
                    SC[30][i, j, n] = w[30]['tl_C'] - R[d]['timeloss_agent']; SC[70][i, j, n] = w[70]['tl_C'] - R[d]['timeloss_agent']
        e = dict(GTE=boot(GTE), H=boot(H), two_share_37_bias=boot(E37), two_share_57_bias=boot(E57), naive_bias=boot(DM),
                 spill_C={p: boot(SC[p]) for p in SC})
        h = e['H'][0]; sgn = all(np.sign(e['spill_C'][p][0]) == np.sign(h) for p in (30, 50, 70))
        out += [f'-- {world} {fam} (t{k0}-t{k1}); GTE {fmt(e["GTE"])} s/veh; H (humans SV - R) {fmt(e["H"])}',
                f'  E1 two-share (0.3, 0.7) bias {fmt(e["two_share_37_bias"])} -> ' + ('RECOVERS GTE (interval contains 0)' if contains0(e['two_share_37_bias']) else 'biased'),
                f'     two-share (0.5, 0.7) bias {fmt(e["two_share_57_bias"])} (descriptive)',
                f'  naive A/B (p 0.5) bias {fmt(e["naive_bias"])} -> ' + ('no bias shown' if contains0(e['naive_bias']) else ('OVERSTATES' if e['naive_bias'][1] > 0 else 'UNDERSTATES')),
                f'  E4 control spillover C(p) - R: ' + ', '.join(f'p {p / 100:.1f} {fmt(e["spill_C"][p])}' for p in (30, 50, 70)) + f' -> sign = sign(H): {sgn}']
        if world == 'W17':
            TAU = np.zeros(shape); GR = np.zeros(shape)
            for i, k in enumerate(ks):
                for j, s in enumerate(fs):
                    N = L(sub / f'NSW_t{k}_s{s}.json'); R, V = L(src / f'R_t{k}_s{s}.json'), L(src / f'SV_t{k}_s{s}.json')
                    for n, d in enumerate(days):
                        acc = {}
                        for tid, w, _na, _da, nl, dl, _t, _c, a in N[d]['w22_win']['rows']:
                            if nl > 0:
                                acc.setdefault(w, [a, []])[1].append(dl / nl)
                        g1 = [np.mean(v[1]) for v in acc.values() if v[0] == 1]; g0 = [np.mean(v[1]) for v in acc.values() if v[0] == 0]
                        TAU[i, j, n] = (np.mean(g1) - np.mean(g0)) if g1 and g0 else np.nan; GR[i, j, n] = V[d]['green_mean'] - R[d]['green_mean']
            e['NSW_green'] = boot(TAU); e['green_truth'] = boot(GR); sw = None
            rep = (B / 'w17' / 'w22.json'); sw = json.loads(rep.read_text())[fam]['tau'][0] if rep.exists() and fam in json.loads(rep.read_text()) else float('nan')
            ok = e['NSW_green'][0] > sw and e['NSW_green'][1] <= e['green_truth'][0] <= e['NSW_green'][2]
            out.append(f'  E3 NSW network green contrast {fmt(e["NSW_green"])} s vs truth {fmt(e["green_truth"])} and per-signal SWB tau {sw:+.2f} -> '
                       + ('HELD (larger than SWB tau, interval contains the truth)' if ok else 'not held'))
        res[f'{world}_{fam}'] = e
if SM:
    out.append('(smoke: truncated runs against full-length ground truth; numbers meaningless, pipeline check only)')
(D / f'report_w22e{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w22e{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
