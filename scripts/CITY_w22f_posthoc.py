#!/usr/bin/env python3
"""W22-F post-hoc audit (PROTOCOL_CITY_WAVE22_20261017, after the W22-F result note).  Reads existing rows only; no simulation.
  f1  same-day two shares: per-day errors by order (0.3 first on even days, 0.7 first on odd days); the registered F1b statistic
      (per-day sd / sqrt 10) next to the order-stratified sd of the 10-day mean (the design is 5 + 5 balanced, so a fixed order term
      cancels in the mean but inflates the pooled per-day sd); C-262's unpaired emulation recomputed per cell (2 000 random 5 / 5 splits
      of the W22-B / W22-E MIX p 0.3 / 0.7 full-day rows; truth = 10-day mean SV - R).
  f3  net burn-in effect on the registered green contrast: (first-60-s excess in treated windows) - (same in control windows), per
      unit-day, for the C-263 reading (a positive value means the 60-s burn-in removes more treated than control green).
  f4  AREA on Midtown: the no-interference imputation Y* (strip-day outcome from the all run if the strip is treated, else from the none
      run) under the realised assignment, its TWFE error (design + effect heterogeneity, no interference), AREA - Y* (interference and
      run noise), placebos (the realised assignment on the none rows and on the all rows), and the design distribution of the Y* error over
      2 000 random assignment sequences (each day 2 of 4 strips), common to all units because the strips are drawn per day.
Usage: CITY_w22f_posthoc.py f1|f3|f4"""
import json, sys
from pathlib import Path
import numpy as np
PART = sys.argv[1]; rng = np.random.default_rng(0); _C = {}
W22 = Path('research/city_sim/w22_20261017'); G20 = Path('research/city_sim/w20_20261009/conf'); G19 = Path('research/city_sim/w19_20261008/conf')
A17 = Path('research/city_sim/w21_20261015/w17/conf')


def L(p):
    p = str(p)
    if p not in _C:
        d = json.loads(Path(p).read_text())
        if d.get('status') != 'COMPLETE':
            sys.exit(f'INCOMPLETE {p}')
        _C[p] = {r['seed']: r for r in d['rows']}
    return _C[p]


def boot1(x, B=2000):
    x = np.asarray(x, float); x = x[~np.isnan(x)]; bs = [np.mean(x[rng.integers(0, len(x), len(x))]) for _ in range(B)]
    return float(np.mean(x)), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


fmt = lambda v: f'{v[0]:+.2f} [{v[1]:+.2f}, {v[2]:+.2f}]'  # noqa: E731
ts = lambda T3, C3, T7, C7, a1=0.3, a2=0.7: (T7 + (1 - a2) * (T7 - T3) / (a2 - a1)) - (C3 - a1 * (C7 - C3) / (a2 - a1))  # noqa: E731
srcg = lambda k: G19 if k < 84 else G20  # noqa: E731
out = []; res = {}

if PART == 'f1':
    out.append('== W22-F F1 post hoc: S2D noise by order; registered statistic vs order-stratified; C-262 unpaired emulation per cell')
    G4D, W7D, G4F, W7F = list(range(1400, 1410)), list(range(1420, 1430)), (1413, 1513), (2213, 2313)
    fams = (('RMP', range(94, 99)), ('AH', range(34, 39)), ('RWV', range(99, 104)), ('SRL', range(84, 89)), ('RDQ', range(89, 94)))
    unp = {'RMP': W22 / 'b', 'AH': W22 / 'b', 'RWV': W22 / 'b', 'SRL': W22 / 'e/g4', 'RDQ': W22 / 'e/g4'}
    cells = [('grid4', f, ks, W22 / 'f/f1/g4', G4F, G4D, None, unp[f]) for f, ks in fams] + \
            [('W17', f, ks, W22 / 'f/f1/w17', W7F, W7D, A17, W22 / 'e/w17') for f, ks in fams[:3]]
    for world, fam, ks, d, fs, days, src, ud in cells:
        reg, strat, mean_even, mean_odd, c262, tsd, esd = [], [], [], [], [], [], []
        splits = [rng.permutation(len(days))[:5] for _ in range(2000)]
        unit_split_err = []
        for k in ks:
            for s in fs:
                R, V = L((src or srcg(k)) / f'R_t{k}_s{s}.json'), L((src or srcg(k)) / f'SV_t{k}_s{s}.json'); X = L(d / f'S2D_t{k}_s{s}.json')
                errs, order, trs, ests = [], [], [], []
                for dd in days:
                    v = X[dd]['w22']['vt']; sh = {v['pa']: v['a'], v['pb']: v['b']}; S3, S7 = sh[0.3], sh[0.7]
                    est = ts(S3[1] / S3[0], S3[3] / S3[2], S7[1] / S7[0], S7[3] / S7[2])
                    wm = lambda row, w: row['window_counts_sums'][str(w)][1] / row['window_counts_sums'][str(w)][0]  # noqa: E731
                    tr = np.mean([wm(V[dd], w) - wm(R[dd], w) for w in (900, 2700)])
                    errs.append(est - tr); order.append(0 if v['pa'] == 0.3 else 1); trs.append(tr); ests.append(est)
                errs, order = np.array(errs), np.array(order); tsd.append(np.std(trs, ddof=1) / np.sqrt(len(trs))); esd.append(np.std(ests, ddof=1) / np.sqrt(len(ests)))
                reg.append(np.std(errs, ddof=1) / np.sqrt(len(errs)))
                ve, vo = np.var(errs[order == 0], ddof=1), np.var(errs[order == 1], ddof=1)
                strat.append(np.sqrt((ve + vo) / 2) / np.sqrt(len(errs))); mean_even.append(errs[order == 0].mean()); mean_odd.append(errs[order == 1].mean())
                # C-262: unpaired days from the full-day MIX p 0.3 / 0.7 rows (W22-E files are named MIXp30 / MIXp70 in both folders)
                M3, M7 = L(ud / f'MIXp30_t{k}_s{s}.json'), L(ud / f'MIXp70_t{k}_s{s}.json')
                T3 = np.array([M3[x]['w22']['tl_T'] for x in days]); C3 = np.array([M3[x]['w22']['tl_C'] for x in days])
                T7 = np.array([M7[x]['w22']['tl_T'] for x in days]); C7 = np.array([M7[x]['w22']['tl_C'] for x in days])
                g = np.mean([V[x]['timeloss_agent'] - R[x]['timeloss_agent'] for x in days])
                e = []
                for sp in splits:
                    a = np.zeros(len(days), bool); a[sp] = True
                    e.append(ts(T3[a].mean(), C3[a].mean(), T7[~a].mean(), C7[~a].mean()) - g)
                unit_split_err.append(e); c262.append(np.std(e))
        U = np.array(unit_split_err)
        r = dict(registered_unit_sd=float(np.mean(reg)), order_stratified_unit_sd=float(np.mean(strat)),
                 order_term=boot1(np.array(mean_even) - np.array(mean_odd)), c262_unit_sd=float(np.mean(c262)),
                 c262_sd_of_unit_mean=float(np.std(U.mean(axis=0))), c262_mean_error=float(U.mean()),
                 truth_unit_sd=float(np.mean(tsd)), estimate_unit_sd=float(np.mean(esd)))
        res[f'{world}_{fam}'] = r
        out.append(f'  {world} {fam}: unit sd of the 10-day mean error: registered (pooled) {r["registered_unit_sd"]:.2f}, order-stratified '
                   f'{r["order_stratified_unit_sd"]:.2f} | C-262 unpaired 5 + 5 days {r["c262_unit_sd"]:.2f} (mean error {r["c262_mean_error"]:+.2f}, '
                   f'sd of the 10-unit mean {r["c262_sd_of_unit_mean"]:.2f}) | order term (even - odd mean error) {fmt(r["order_term"])} | '
                   f'unit sd of the 10-day mean: windowed truth {r["truth_unit_sd"]:.2f}, S2D estimate {r["estimate_unit_sd"]:.2f}')

elif PART == 'f3':
    out.append('== W22-F F3 post hoc: net burn-in effect = (first-60-s excess, treated windows) - (same, control windows), per unit-day')
    G4D, W7D, G4F, W7F = list(range(1400, 1404)), list(range(1420, 1424)), (1413, 1513), (2213, 2313)
    for world, fam, ks, d, fs, days in (('grid4', 'RMP', range(94, 99), W22 / 'f/g4', G4F, G4D), ('grid4', 'AH', range(34, 39), W22 / 'f/g4', G4F, G4D),
                                        ('W17', 'RMP', range(94, 99), W22 / 'f/w17', W7F, W7D), ('W17', 'AH', range(34, 39), W22 / 'f/w17', W7F, W7D)):
        net, sh0 = [], []
        for k in ks:
            for s in fs:
                S = L(d / f'P2SWB_t{k}_s{s}.json')
                for dd in days:
                    bins = S[dd]['w22_p2']['bins']; ex = {}
                    for z in (1, 0):
                        b0 = [(x[3], x[4]) for x in bins if x[5] == z and x[2] == 0]; bl = [(x[3], x[4]) for x in bins if x[5] == z and x[2] >= 1]
                        ex[z] = sum(y for _, y in b0) / sum(n for n, _ in b0) - sum(y for _, y in bl) / sum(n for n, _ in bl)
                    net.append(ex[1] - ex[0]); sh0.append(sum(x[3] for x in bins if x[2] == 0) / sum(x[3] for x in bins))
        r = dict(net=boot1(net), share_first60=float(np.mean(sh0))); res[f'{world}_{fam}'] = r
        out.append(f'  {world} {fam}: net excess (T - C) {fmt(r["net"])} s; share of greens starting in the first 60 s {r["share_first60"]:.3f}')

elif PART == 'f4':
    out.append('== W22-F F4 post hoc: AREA error decomposed; no-interference imputation Y*; placebos; design distribution (common to all units)')
    D = W22 / 'f/mt'; days = [0, 1, 2, 3, 4]; fs = (1413, 1513)
    seqs = [[tuple(sorted(rng.permutation(4)[:2])) for _ in days] for _ in range(2000)]

    def twfe(Y, Dm):
        Gs = [g for _ in days for g in range(4)]; Ds = [n for n in range(len(days)) for _ in range(4)]
        X = [np.array(Dm, float)] + [np.array([1.0 if x == gg else 0.0 for x in Gs]) for gg in range(4)] + \
            [np.array([1.0 if x == dd else 0.0 for x in Ds]) for dd in range(1, len(days))]
        return np.linalg.lstsq(np.column_stack(X), np.array(Y, float), rcond=None)[0][0]
    for fam, ks in (('AH', range(34, 39)), ('B2D', range(59, 64))):
        rows = dict(area=[], ystar=[], inter=[], pl_none=[], pl_all=[]); design = []
        for k in ks:
            for s in fs:
                A, N, AA = (L(D / f'{x}_t{k}_s{s}.json') for x in ('ALL', 'NONE', 'AREA'))
                strip = AA[0]['w22']['area']['strip']; members = [{t for t, x in strip.items() if x == gg} for gg in range(4)]
                pooled = lambda p3, sel: sum(p3[t][0] for t in sel if t in p3) / max(1, sum(p3[t][1] for t in sel if t in p3))  # noqa: E731
                allsig = set(strip)
                g = np.mean([pooled(A[dd]['w22_p3'], allsig) - pooled(N[dd]['w22_p3'], allsig) for dd in days])
                ya = [[pooled(A[dd]['w22_p3'], members[gg]) for gg in range(4)] for dd in days]
                yn = [[pooled(N[dd]['w22_p3'], members[gg]) for gg in range(4)] for dd in days]
                yr = [[pooled(AA[dd]['w22_p3'], members[gg]) for gg in range(4)] for dd in days]
                tr = [set(AA[dd]['w22']['area']['treated']) for dd in days]
                Dm = [1.0 if gg in tr[n] else 0.0 for n in range(len(days)) for gg in range(4)]
                Ys = [ya[n][gg] if gg in tr[n] else yn[n][gg] for n in range(len(days)) for gg in range(4)]
                area = twfe([yr[n][gg] for n in range(len(days)) for gg in range(4)], Dm) - g; ystar = twfe(Ys, Dm) - g
                rows['area'].append(area); rows['ystar'].append(ystar); rows['inter'].append(area - ystar)
                rows['pl_none'].append(twfe([yn[n][gg] for n in range(len(days)) for gg in range(4)], Dm))
                rows['pl_all'].append(twfe([ya[n][gg] for n in range(len(days)) for gg in range(4)], Dm))
                de = []
                for sq in seqs:
                    Dq = [1.0 if gg in sq[n] else 0.0 for n in range(len(days)) for gg in range(4)]
                    de.append(twfe([ya[n][gg] if gg in sq[n] else yn[n][gg] for n in range(len(days)) for gg in range(4)], Dq) - g)
                design.append(de)
        Dd = np.array(design).mean(axis=0)                     # cell mean of the Y* error for each assignment sequence
        r = {k: boot1(v) for k, v in rows.items()}
        r['design_mean'] = float(Dd.mean()); r['design_sd'] = float(Dd.std()); r['design_q'] = [float(np.percentile(Dd, 2.5)), float(np.percentile(Dd, 97.5))]
        r['realised_ystar_percentile'] = float((Dd < np.mean(rows['ystar'])).mean() * 100)
        res[fam] = r
        out += [f'-- {fam}: AREA bias {fmt(r["area"])} (as reported) = Y* error {fmt(r["ystar"])} (design + heterogeneity, no interference) + '
                f'AREA - Y* {fmt(r["inter"])} (interference + run noise)',
                f'  placebo (realised assignment) on the none rows {fmt(r["pl_none"])}, on the all rows {fmt(r["pl_all"])}',
                f'  design distribution of the cell-mean Y* error over 2 000 assignment sequences: mean {r["design_mean"]:+.2f}, sd {r["design_sd"]:.2f}, '
                f'95 % [{r["design_q"][0]:+.2f}, {r["design_q"][1]:+.2f}]; the realised assignment sits at percentile {r["realised_ystar_percentile"]:.0f}']

(W22 / f'f/posthoc_w22f_{PART}.txt').write_text('\n'.join(out) + '\n'); (W22 / f'f/posthoc_w22f_{PART}.json').write_text(json.dumps(res, indent=1, default=float))
print('\n'.join(out))
