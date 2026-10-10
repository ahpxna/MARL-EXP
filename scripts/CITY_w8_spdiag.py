#!/usr/bin/env python3
"""W8-1 SPDIAG report (PROTOCOL_CITY_WAVE8_20261005): why spider fails.  Descriptive.
  D1 light reaction: mean green_mean / mean_halting of R vs service arms (existing spider rows; grid4 TSI-2 rows for comparison).
  D2 forecast error at the fleet's queries: provider debug rows (time, light, kind, r, features, q0.5 prediction) matched to realized targets
     with CITY_n2k.build on the same run's feature log (as the KS-1 parity); MAE / bias / share |err| > 5 s, by K and kind.
  D3 value of exact timing: oracle (C-61 recipe, open-loop replay of the R run, exact future) minus sigma* on the same replay.
  D4 harm by signal type: service restricted to 2-green or 3-green signals vs R (attempt-1 configuration, TUNE seeds).
Usage: CITY_w8_spdiag.py <diag dir>"""
import glob, json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = ROOT / 'research/city_sim'


def mean_of(Rt, key, f):
    v = [r.get(f) for r in Rt[key].values() if r.get(f) is not None]
    return float(np.mean(v)) if v else float('nan')


def d1(out):
    out.append('D1 light reaction (mean over runs): green_mean (s) / mean_halting')
    sets = [('spider attempt 1', CS / 'sptsi_20261005/conf', ('R', 'HYBK', 'TSIK', 'ADPK'), (11, 111), '{a}_{k}'),
            ('spider attempt 2', CS / 'sptsi_20261005/conf2', ('R', 'HYBK', 'TSIK2', 'ADPK2'), (11, 111), '{a}_{k}'),
            ('spider attempt 3', CS / 'w6_20261005/sp3/conf', ('R', 'SVC3', 'TSIK3', 'ADPK3'), (11, 111), '{a}_{k}')]
    for name, d, arms, L, fmt in sets:
        Rt = rows(d); s = []
        for a in arms:
            ks = [fmt.format(a=a, k=k) for k in L if fmt.format(a=a, k=k) in Rt]
            if ks:
                g = np.mean([mean_of(Rt, k, 'green_mean') for k in ks]); h = np.mean([mean_of(Rt, k, 'mean_halting') for k in ks]); s.append(f'{a} {g:.1f} / {h:.2f}')
        out.append(f'  {name}: ' + '; '.join(s))
    Rt = rows(CS / 'tsi2_20261005/conf'); s = []
    for a in ('R', 'HYB', 'TSI2', 'ADP2'):
        ks = [k for k in Rt if k.startswith(a + '_t')]
        s.append(f'{a} {np.mean([mean_of(Rt, k, "green_mean") for k in ks]):.1f} / {np.mean([mean_of(Rt, k, "mean_halting") for k in ks]):.2f}')
    out.append('  grid4 TSI-2 panel (reference): ' + '; '.join(s))


def d2(D, out):
    import scripts.CITY_n2k as NK
    greens, _ = NK.greens_of_net(); res = {}
    for f in sorted(glob.glob(str(D / 'd2' / 'fl_*' / 'feat_s*.npz'))):
        fd = Path(f).parent; seed = int(Path(f).stem.split('_s')[1]); pr = fd / f'provider_rows_s{seed}.json'
        if not pr.exists():
            continue
        X, Y, W, KEYS = NK.build([f], greens); tm = np.load(f, allow_pickle=True)['times']
        tgt = {(int(tm[i]), tid, kind, r): y for (fi, i, tid, kind, r), y in zip(KEYS, Y)}
        for t, tid, kind, r, row, v in json.load(open(pr)):
            y = tgt.get((int(t), tid, kind, r))
            if y is None:
                continue
            K = len(greens[tid]); res.setdefault((K, kind, r), []).append(v - y); res.setdefault(('all', '', ''), []).append(v - y); res.setdefault((K, '', ''), []).append(v - y)
    out.append('D2 forecast error at queried light-seconds (prediction - realized, s): n | MAE | bias | share |err| > 5 s   (grid4 reference: MAE 3.02 s published, C-109)')
    for k in sorted(res, key=str):
        e = np.array(res[k]); out.append(f'  K={k[0]} kind={k[1]} r={k[2]}: n {len(e)} | MAE {np.mean(np.abs(e)):.2f} | bias {np.mean(e):+.2f} | >5s {np.mean(np.abs(e) > 5):.3f}')


def d3(D, out):
    Rt = rows(D / 'd3'); out.append('D3 value of exact timing (oracle - sigma* on the same open-loop replay; TUNE 1100-1103): agent fuel % / agent TL / human TL')
    for k in (11, 111):
        o, s = Rt.get(f'ORC_{k}'), Rt.get(f'SIG_{k}')
        if not o or not s:
            out.append(f'  RLK{k}: missing'); continue
        S = sorted(set(o) & set(s)); fu = 100 * (np.mean([o[x]['fuel_agent'] for x in S]) / np.mean([s[x]['fuel_agent'] for x in S]) - 1)
        ta = np.mean([o[x]['timeloss_agent'] - s[x]['timeloss_agent'] for x in S]); th = np.mean([o[x]['timeloss_human'] - s[x]['timeloss_human'] for x in S])
        rec = Rt.get(f'REC_{k}'); kh = all(abs(rec[x]['timeloss'] - s[x]['timeloss']) < 1e-9 for x in S) if rec else None
        per = [100 * (o[x]['fuel_agent'] / s[x]['fuel_agent'] - 1) for x in S]
        out.append(f'  RLK{k}: fuel {fu:+.2f} % (per seed {", ".join(f"{p:+.1f}" for p in per)}), agent TL {ta:+.2f}, human TL {th:+.2f}; replay == recorded R (KH-1): {kh}')
    out.append('  grid4 reference: exact timing on the replayed learned-light schedule -6.57 % fuel (C-72 D-dir, delta 0), -5.60 % (X3, C-107)')


def d4(D, out):
    Rt = rows(D / 'd4'); out.append('D4 harm by signal type (vs R, TUNE 1100-1103, mean over seeds): agent fuel % / city TL / agent TL / human TL')
    for k in (11, 111):
        R = Rt.get(f'R_{k}')
        for a in ('FULL', 'K2ONLY', 'K3ONLY'):
            X = Rt.get(f'{a}_{k}')
            if not R or not X:
                out.append(f'  RLK{k} {a}: missing'); continue
            S = sorted(set(R) & set(X)); fu = 100 * (np.mean([X[s]['fuel_agent'] for s in S]) / np.mean([R[s]['fuel_agent'] for s in S]) - 1)
            d = {q: np.mean([X[s][q] - R[s][q] for s in S]) for q in ('timeloss', 'timeloss_agent', 'timeloss_human')}
            out.append(f'  RLK{k} {a}: fuel {fu:+.2f} % | city {d["timeloss"]:+.2f} | agent {d["timeloss_agent"]:+.2f} | human {d["timeloss_human"]:+.2f}')


if __name__ == '__main__':
    D = Path(sys.argv[1]); out = ['== W8-1 SPDIAG: why the method fails on spider (descriptive; PROTOCOL_CITY_WAVE8_20261005)']
    for fn in (lambda: d1(out), lambda: d2(D, out), lambda: d3(D, out), lambda: d4(D, out)):
        try:
            fn()
        except Exception as e:  # report every part that can be computed; a failure is printed, not hidden
            out.append(f'  ERROR in a diagnostic part: {type(e).__name__}: {e}')
    print('\n'.join(out)); (D / 'report_spdiag.txt').write_text('\n'.join(out) + '\n')
