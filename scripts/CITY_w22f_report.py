#!/usr/bin/env python3
"""W22-F reports (PROTOCOL_CITY_WAVE22_20261017, Amendment W22-F).  One script, four parts; each refuses incomplete rows.
  f1 <dir>   same-day two shares (S2D): per day the two-share formula on the measured windows, averaged over days, against the truth
             (SV - R agent time loss, equal-weight mean of the 900-1800 and 2700-3600 departure windows); crossed bootstrap over lights x fleets x
             day pairs; F1b: unit-level sd of the 10-day mean error (per-day sd / sqrt 10).
  f2 <dir>   other W19 families: naive bias (p 0.5), two-share (0.3, 0.7) bias, control spillover sign, bias / (-H).
  f3 <dir>   switch transient (green by 60-s offset bin), halting shares by signal / upstream assignment (SWB vs none), vehicles in the network.
  f4 <dir>   Midtown: KW22-F4 identity (all / none = W21-B MTW_SV / MTW_R), per-passage truth, AREA two-way FE (+ buffered), MIX contrast.
Usage: CITY_w22f_report.py f1|f2|f3|f4 <dir>   (W22_SMOKE=1 for smoke dirs)"""
import json, os, sys
from pathlib import Path
import numpy as np
PART, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W22_SMOKE') == '1'; SFX = '_smoke' if SM else ''
G20 = Path('research/city_sim/w20_20261009/conf'); G19 = Path('research/city_sim/w19_20261008/conf'); A17 = Path('research/city_sim/w21_20261015/w17/conf')
MTW = Path('research/city_sim/w21_20261015/midtown')
rng = np.random.default_rng(0); _C = {}


def L(p):
    p = str(p)
    if p not in _C:
        d = json.loads(Path(p).read_text())
        if d.get('status') != 'COMPLETE':
            sys.exit(f'INCOMPLETE {p}')
        _C[p] = {r['seed']: r for r in d['rows']}
    return _C[p]


def boot3(M, B=2000):
    bs = [np.nanmean(M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]), rng.integers(0, M.shape[2], M.shape[2]))]) for _ in range(B)]
    return float(np.nanmean(M)), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


def boot1(x, B=2000):
    x = np.asarray(x, float); bs = [np.nanmean(x[rng.integers(0, len(x), len(x))]) for _ in range(B)]
    return float(np.nanmean(x)), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


fmt = lambda v: f'{v[0]:+.2f} [{v[1]:+.2f}, {v[2]:+.2f}]'  # noqa: E731
c0 = lambda v: v[1] <= 0 <= v[2]  # noqa: E731
ts = lambda T3, C3, T7, C7, a1=0.3, a2=0.7: (T7 + (1 - a2) * (T7 - T3) / (a2 - a1)) - (C3 - a1 * (C7 - C3) / (a2 - a1))  # noqa: E731
out = []; res = {}
if SM:
    G4D, W7D, G4F, W7F = [1400], [1420], (1413,), (2213,)
else:
    G4D, W7D, G4F, W7F = list(range(1400, 1410)), list(range(1420, 1430)), (1413, 1513), (2213, 2313)
srcg = lambda k: G19 if k < 84 else G20  # noqa: E731

if PART == 'f1':
    out.append('== W22-F F1: same-day two shares (vt:1800); measured departures [900, 1800) and [2700, 3600); truth = equal-weight SV - R over them')
    cells = [('grid4', f, ks, D / 'g4', G4F, G4D, None) for f, ks in (('RMP', range(94, 99)), ('AH', range(34, 39)), ('RWV', range(99, 104)), ('SRL', range(84, 89)), ('RDQ', range(89, 94)))] + \
            [('W17', f, ks, D / 'w17', W7F, W7D, A17) for f, ks in (('RMP', range(94, 99)), ('AH', range(34, 39)), ('RWV', range(99, 104)))]
    if SM:
        cells = [cells[0], cells[5]]; cells = [(w, f, range(ks[0], ks[0] + 1), d, fs, ds, s) for w, f, ks, d, fs, ds, s in cells]
    for world, fam, ks, d, fs, days, src in cells:
        pairs = [days[i:i + 2] for i in range(0, len(days), 2)] if len(days) > 1 else [days]
        E = np.full((len(ks), len(fs), len(pairs)), np.nan); unit_sd = []
        for i, k in enumerate(ks):
            for j, s in enumerate(fs):
                R, V = L((src or srcg(k)) / f'R_t{k}_s{s}.json'), L((src or srcg(k)) / f'SV_t{k}_s{s}.json'); X = L(d / f'S2D_t{k}_s{s}.json')
                errs = []
                for dd in days:
                    v = X[dd]['w22']['vt']; A, Bw = v['a'], v['b']
                    m = lambda z, o: (z[o + 1] / z[o]) if z[o] else np.nan  # noqa: E731
                    shares = {v['pa']: A, v['pb']: Bw}; S3, S7 = shares[0.3], shares[0.7]
                    est = ts(m(S3, 0), m(S3, 2), m(S7, 0), m(S7, 2))
                    def wmean(row, w):
                        x = row['window_counts_sums'].get(str(w)); return x[1] / x[0] if x and x[0] else np.nan
                    tr = np.nanmean([wmean(V[dd], w) - wmean(R[dd], w) for w in (900, 2700)])
                    errs.append(est - tr)
                errs = np.array(errs); unit_sd.append(np.nanstd(errs, ddof=1) / np.sqrt(np.sum(~np.isnan(errs))) if len(errs) > 1 else np.nan)
                for n, pr in enumerate(pairs):
                    E[i, j, n] = np.nanmean([errs[days.index(x)] for x in pr])
        b = boot3(E); sd = float(np.nanmean(unit_sd)); res[f'{world}_{fam}'] = dict(bias=b, unit_sd=sd)
        out.append(f'  {world} {fam}: S2D bias {fmt(b)} -> ' + ('F1a HELD (contains 0)' if c0(b) else 'F1a FAILED') +
                   f' | unit-level sd of the 10-day mean error {sd:.2f} s/veh -> ' + ('F1b HELD (< 0.79)' if sd < 0.79 else 'F1b not below 0.79'))

elif PART == 'f2':
    H0 = {'B1H': -0.12, 'B2H': -0.31, 'AD': -0.84, 'B1D': -0.06, 'B2D': -0.06, 'S05': -1.18, 'S2': -1.17, 'R1': -1.23, 'R100': -1.11}
    K0 = {'B1H': 39, 'B2H': 44, 'AD': 49, 'B1D': 54, 'B2D': 59, 'S05': 64, 'S2': 69, 'R1': 74, 'R100': 79}
    strong = ('AD', 'S05', 'S2', 'R1', 'R100'); weak = ('B1H', 'B1D', 'B2D')
    fams = list(K0) if not SM else ['AD']
    out.append('== W22-F F2: other W19 families (MIX p 0.3 / 0.5 / 0.7), grid4 days 1400-1409')
    for fam in fams:
        ks = list(range(K0[fam], K0[fam] + (5 if not SM else 1))); shape = (len(ks), len(G4F), len(G4D))
        GT, NB, TS, SC5, SC7, H = (np.zeros(shape) for _ in range(6))
        for i, k in enumerate(ks):
            for j, s in enumerate(G4F):
                R, V = L(G19 / f'R_t{k}_s{s}.json'), L(G19 / f'SV_t{k}_s{s}.json'); X = {p: L(D / f'MIXp{p}_t{k}_s{s}.json') for p in (30, 50, 70)}
                for n, dd in enumerate(G4D):
                    g = V[dd]['timeloss_agent'] - R[dd]['timeloss_agent']; w = {p: X[p][dd]['w22'] for p in X}
                    GT[i, j, n] = g; H[i, j, n] = V[dd]['timeloss_human'] - R[dd]['timeloss_human']
                    NB[i, j, n] = (w[50]['tl_T'] - w[50]['tl_C']) - g; TS[i, j, n] = ts(w[30]['tl_T'], w[30]['tl_C'], w[70]['tl_T'], w[70]['tl_C']) - g
                    SC5[i, j, n] = w[50]['tl_C'] - R[dd]['timeloss_agent']; SC7[i, j, n] = w[70]['tl_C'] - R[dd]['timeloss_agent']
        e = dict(GTE=boot3(GT), H=boot3(H), naive=boot3(NB), two=boot3(TS), sc5=boot3(SC5), sc7=boot3(SC7)); h = H0[fam]
        if fam in strong:
            ra = 'F2a HELD' if e['naive'][1] > 0 else 'F2a FAILED'; ratio = e['naive'][0] / (-h); rb = f'bias/(-H) {ratio:.2f} -> ' + ('F2b HELD' if 0.5 <= ratio <= 3.0 else 'F2b FAILED')
            rd = 'F2d HELD' if (e['sc5'][0] < 0 and e['sc7'][0] < 0) else 'F2d FAILED'
        elif fam in weak:
            ra = 'F2a HELD (no bias shown)' if c0(e['naive']) else 'F2a FAILED'; rb = ''; rd = ''
        else:
            ra = '(no prediction)'; rb = ''; rd = ''
        rc = 'F2c HELD' if c0(e['two']) else 'F2c FAILED'
        out += [f'-- {fam} (t{ks[0]}-t{ks[-1]}): GTE {fmt(e["GTE"])}; H {fmt(e["H"])} (registered {h:+.2f})',
                f'  naive A/B bias {fmt(e["naive"])} -> {ra} {rb}', f'  two-share (0.3, 0.7) bias {fmt(e["two"])} -> {rc}',
                f'  control spillover p 0.5 {fmt(e["sc5"])}, p 0.7 {fmt(e["sc7"])} {rd}']
        res[fam] = e

elif PART == 'f3':
    out.append('== W22-F F3: switch transient, halting shares by signal / upstream assignment, vehicles in the network')
    cells = [('grid4', 'RMP', range(94, 99), D / 'g4', G4F, G4D[:4]), ('grid4', 'AH', range(34, 39), D / 'g4', G4F, G4D[:4]),
             ('W17', 'RMP', range(94, 99), D / 'w17', W7F, W7D[:4]), ('W17', 'AH', range(34, 39), D / 'w17', W7F, W7D[:4])]
    if SM:
        cells = [(w, f, range(ks[0], ks[0] + 1), d, fs, ds[:1]) for w, f, ks, d, fs, ds in cells[:1]]
    excess = {}
    for world, fam, ks, d, fs, days in cells:
        ex_T, ex_C, h_sw0, h_none, h_zi1, h_zi0, veh = [], [], [], [], [], [], {'SWB': [], 'ALL': [], 'NONE': []}
        for k in ks:
            for s in fs:
                S, A, N = L(d / f'P2SWB_t{k}_s{s}.json'), L(d / f'P2ALL_t{k}_s{s}.json'), L(d / f'P2NONE_t{k}_s{s}.json')
                for dd in days:
                    bins = S[dd]['w22_p2']['bins']
                    for z, acc in ((1, ex_T), (0, ex_C)):
                        b0 = [(x[3], x[4]) for x in bins if x[5] == z and x[2] == 0]; bl = [(x[3], x[4]) for x in bins if x[5] == z and x[2] >= 1]
                        if b0 and bl:
                            acc.append(sum(y for _, y in b0) / sum(n for n, _ in b0) - sum(y for _, y in bl) / sum(n for n, _ in bl))
                    ps = S[dd]['w22_p2']['passages']; pn = N[dd]['w22_p2']['passages']
                    share = lambda rows: (sum(r[4] for r in rows) / sum(r[3] for r in rows)) if rows and sum(r[3] for r in rows) else np.nan  # noqa: E731
                    sw0 = [r for r in ps if r[1] == 0]; h_sw0.append(share(sw0)); h_none.append(share(pn))
                    h_zi1.append(share([r for r in sw0 if r[2] == 1])); h_zi0.append(share([r for r in sw0 if r[2] == 0]))
                    for lab, X in (('SWB', S), ('ALL', A), ('NONE', N)):
                        vv = X[dd]['w22_p2']['vehicles']; veh[lab].append(sum(x[1] for x in vv) / max(1, sum(x[2] for x in vv)))
        e = dict(excess_T=boot1(ex_T), excess_C=boot1(ex_C), halt_sw_control=boot1(h_sw0), halt_none=boot1(h_none),
                 halt_diff=boot1(np.array(h_sw0) - np.array(h_none)), halt_zi1=boot1(h_zi1), halt_zi0=boot1(h_zi0),
                 halt_zi_diff=boot1(np.array(h_zi1) - np.array(h_zi0)), veh={k: float(np.mean(v)) for k, v in veh.items()})
        excess[(world, fam)] = e['excess_T'][0]; res[f'{world}_{fam}'] = e
        out += [f'-- {world} {fam}: first-60-s greens minus later greens: treated windows {fmt(e["excess_T"])} s, control windows {fmt(e["excess_C"])} s',
                f'  halting share on approaches: SWB control windows {e["halt_sw_control"][0]:.4f} vs none run {e["halt_none"][0]:.4f}, difference {e["halt_diff"][0]:+.4f} '
                f'[{e["halt_diff"][1]:+.4f}, {e["halt_diff"][2]:+.4f}]',
                f'  within SWB control windows, upstream treated minus upstream control: {e["halt_zi_diff"][0]:+.4f} [{e["halt_zi_diff"][1]:+.4f}, {e["halt_zi_diff"][2]:+.4f}]',
                f'  vehicles in the network (mean): none {e["veh"]["NONE"]:.1f}, SWB {e["veh"]["SWB"]:.1f}, all {e["veh"]["ALL"]:.1f}']
    if not SM:
        a = excess[('W17', 'RMP')] > 0 and excess[('W17', 'RMP')] > excess[('grid4', 'RMP')]
        out.append('F3a ' + ('HELD' if a else 'FAILED') + f": W17 RMP treated-window excess {excess[('W17', 'RMP')]:+.2f} vs grid4 {excess[('grid4', 'RMP')]:+.2f}")
        b = all(res[f'{w}_RMP']['halt_diff'][2] < 0 and res[f'{w}_RMP']['halt_zi_diff'][2] < 0 for w in ('grid4', 'W17'))
        out.append('F3b ' + ('HELD' if b else 'FAILED') + ' (MPLight, both worlds: SWB control-window halting below the none run, and lower when upstream treated)')

elif PART == 'f4':
    out.append('== W22-F F4: area randomisation on the full Midtown map (MT-E setting), days 0-4')
    F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel', 'waiting', 'teleports', 'unfinished', 'action_digest')
    fams = [('AH', range(34, 39)), ('B2D', range(59, 64))] if not SM else [('AH', range(34, 35))]
    days = [0, 1, 2, 3, 4] if not SM else [0]; fs = (1413, 1513) if not SM else (1413,)
    nid = tot = 0
    for fam, ks in fams:
        for k in ks:
            for s in fs:
                for arm, ref in (('ALL', 'MTW_SV'), ('NONE', 'MTW_R')):
                    if SM:
                        continue
                    X, Y = L(D / f'{arm}_t{k}_s{s}.json'), L(MTW / f'{ref}_t{k}_s{s}.json')
                    for dd in days:
                        tot += 1; nid += all(X[dd].get(f) == Y[dd].get(f) for f in F)
    out.append(f'KW22-F4 all / none = W21-B MTW_SV / MTW_R: {nid} of {tot} (row, day) identical' + (' -> PASS' if nid == tot and tot else (' (smoke: skipped)' if SM else ' -> FAIL')))
    for fam, ks in fams:
        U = [(k, s) for k in ks for s in fs]; GT, AR, ARb, MX = [], [], [], []
        for k, s in U:
            A, N, AA, M = (L(D / f'{x}_t{k}_s{s}.json') for x in ('ALL', 'NONE', 'AREA', 'MIX'))
            pooled = lambda p3, sel=None: (sum(v[0] for t, v in p3.items() if sel is None or t in sel) / max(1, sum(v[1] for t, v in p3.items() if sel is None or t in sel)))  # noqa: E731
            g = np.mean([pooled(A[dd]['w22_p3']) - pooled(N[dd]['w22_p3']) for dd in days]); GT.append(g)
            ar = AA[days[0]]['w22']['area']; strip = ar['strip']; coord = ar['coord']
            lo = {}; hi = {}
            for t, gix in strip.items():
                lo[gix] = min(lo.get(gix, 1e18), coord[t]); hi[gix] = max(hi.get(gix, -1e18), coord[t])
            inner = {t for t, gix in strip.items() if lo[gix] + 0.1 * (hi[gix] - lo[gix]) <= coord[t] <= hi[gix] - 0.1 * (hi[gix] - lo[gix])}
            def twfe(sel):
                Y, Dm, Gs, Ds = [], [], [], []
                for n, dd in enumerate(days):
                    p3 = AA[dd]['w22_p3']; tr = set(AA[dd]['w22']['area']['treated'])
                    for gix in range(4):
                        ts_ = {t for t, x in strip.items() if x == gix and (sel is None or t in sel)}
                        Y.append(pooled(p3, ts_)); Dm.append(1.0 if gix in tr else 0.0); Gs.append(gix); Ds.append(n)
                Y, Dm = np.array(Y), np.array(Dm); X = [Dm] + [np.array([1.0 if x == gg else 0.0 for x in Gs]) for gg in range(4)] + [np.array([1.0 if x == dd else 0.0 for x in Ds]) for dd in range(1, len(days))]
                b, *_ = np.linalg.lstsq(np.column_stack(X), Y, rcond=None); return b[0]
            AR.append(twfe(None) - g); ARb.append(twfe(inner) - g)
            mx = []
            for dd in days:
                p3 = M[dd]['w22_p3']; tT = sum(v[4] for v in p3.values()) / max(1, sum(v[5] for v in p3.values())); tC = sum(v[6] for v in p3.values()) / max(1, sum(v[7] for v in p3.values()))
                mx.append(tT - tC)
            MX.append(np.mean(mx) - g)
        e = dict(GTE=boot1(GT), area_bias=boot1(AR), area_buffered_bias=boot1(ARb), mix_bias=boot1(MX)); res[fam] = e
        out += [f'-- {fam}: per-passage fleet delay GTE (all - none) {fmt(e["GTE"])} s',
                f'  AREA (strip x day fixed effects) bias {fmt(e["area_bias"])}; buffered (inner 80 % of each strip) bias {fmt(e["area_buffered_bias"])} (descriptive)',
                f'  MIX (per-vehicle A/B) bias {fmt(e["mix_bias"])}']
        if not SM:
            if fam == 'AH':
                out.append('  F4a ' + ('HELD' if not c0(e['mix_bias']) else 'FAILED') + ' (MIX biased for AH); F4b ' +
                           ('HELD' if (c0(e['area_bias']) and abs(e['area_bias'][0]) < abs(e['mix_bias'][0])) else 'FAILED') + ' (AREA contains 0 and |AREA| < |MIX|)')
            else:
                out.append('  F4a ' + ('HELD' if c0(e['mix_bias']) else 'FAILED') + ' (MIX unbiased for B2D); F4b ' + ('HELD' if c0(e['area_bias']) else 'FAILED') + ' (AREA contains 0)')
if SM:
    out.append('(smoke: truncated runs; numbers meaningless, pipeline check only)')
(D / f'report_w22{PART}{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w22{PART}{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
