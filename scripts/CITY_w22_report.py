#!/usr/bin/env python3
"""W22 report (PROTOCOL_CITY_WAVE22_20261017).  <dir>: SWB_t<k>_s<f> and MIX_t<k>_s<f> rows (wrapper CITY_w22_assign.py, probe on);
ground truth R / SV rows of the same light, fleet and day from W19 (AH) or W20 (RMP, RWV).
  KW22-3  MIX treated share of fleet vehicles in 0.5 +- 0.05 and withheld queries > 0 in every run; SWB treated window share in 0.5 +- 0.05
  D1 (SWB, owner-observable): per run and signal, tau = mean green duration (greens starting >= burn-in into a window) in treated windows
     minus control windows; run tau = mean over signals with both kinds; family tau = mean over runs.  One-sided Fisher randomisation
     test under the sharp null (window labels re-drawn Bernoulli(0.5), 2 000 draws), alpha = 0.05/3; crossed bootstrap 95 % (descriptive);
     ground truth SV - R mean green (rows' green_mean).  Fisher labels from numpy default_rng(1).
  D2 (MIX): DM = treated - control fleet time loss, GTE = SV - R agent time loss, bias = DM - GTE; spillovers TL_C - R, TL_T - SV;
     crossed bootstrap 95 % over lights x fleets x days (2 000 draws, seed 0).
Usage: CITY_w22_report.py <dir> "<FAM:k0-k1:src ...>" "<fleets>" "<days>"   (src = w19 | w20)"""
import hashlib, json, os, sys
from pathlib import Path
import numpy as np
D = Path(sys.argv[1]); FAMS = [x.split(':') for x in sys.argv[2].split()]; FS = [int(x) for x in sys.argv[3].split()]; DAYS = [int(x) for x in sys.argv[4].split()]
SM = os.environ.get('W22_SMOKE') == '1'; SFX = '_smoke' if SM else ''
SRC = {'w19': Path('research/city_sim/w19_20261008/conf'), 'w20': Path('research/city_sim/w20_20261009/conf')}
ALPHA = 0.05 / 3; B = 2000


def L(p):
    d = json.loads(Path(p).read_text())
    if d.get('status') != 'COMPLETE':
        sys.exit(f'INCOMPLETE {p}')
    return {r['seed']: r for r in d['rows']}


def U(*k):
    return int.from_bytes(hashlib.sha256('|'.join(map(str, k)).encode()).digest()[:8], 'big') / 2 ** 64


def run_tau(win, relabel=None):
    """win rows [tid, w, n_all, dur_all, n_late, dur_late, nT, nC, assign]; relabel(tid, w) -> 0/1 replaces the assignment."""
    acc = {}
    for tid, w, _na, _da, nl, dl, _t, _c, a in win:
        g = relabel(tid, w) if relabel else a
        s = acc.setdefault(tid, [0, 0.0, 0, 0.0]); s[2 * g] += nl; s[2 * g + 1] += dl
    t = [s[3] / s[2] - s[1] / s[0] for s in acc.values() if s[0] > 0 and s[2] > 0]
    return float(np.mean(t)) if t else float('nan')


def prep(win):
    tids = sorted({r[0] for r in win}); ix = {t: i for i, t in enumerate(tids)}
    return (np.array([ix[r[0]] for r in win], int), np.array([r[4] for r in win], float), np.array([r[5] for r in win], float),
            np.array([r[8] for r in win], float), len(tids))


def tau_arr(T_, NL, DL, G, K):
    n1, d1 = np.bincount(T_, NL * G, K), np.bincount(T_, DL * G, K); n0, d0 = np.bincount(T_, NL * (1 - G), K), np.bincount(T_, DL * (1 - G), K)
    ok = (n1 > 0) & (n0 > 0)
    return float(np.mean(d1[ok] / n1[ok] - d0[ok] / n0[ok])) if ok.any() else float('nan')


rng = np.random.default_rng(0)


def boot(M):
    bs = [np.nanmean(M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]), rng.integers(0, M.shape[2], M.shape[2]))]) for _ in range(B)]
    return float(np.nanmean(M)), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


fmt = lambda v: f'{v[0]:+.3f} [{v[1]:+.3f}, {v[2]:+.3f}]'  # noqa: E731
out = [f'== W22: owner-side identification (SWB) and per-vehicle A/B bias (MIX); families {[f[0] for f in FAMS]}; fleets {FS}; days {DAYS}']
res = {}; shares = []; wshares = []; withheld_zero = 0
for fam, kr, src in FAMS:
    k0, k1 = (int(x) for x in kr.split('-')); ks = list(range(k0, k1 + 1)); G = SRC[src]
    S = {(k, s): L(D / f'SWB_t{k}_s{s}.json') for k in ks for s in FS}; X = {(k, s): L(D / f'MIX_t{k}_s{s}.json') for k in ks for s in FS}
    R = {(k, s): L(G / f'R_t{k}_s{s}.json') for k in ks for s in FS}; V = {(k, s): L(G / f'SV_t{k}_s{s}.json') for k in ks for s in FS}
    shape = (len(ks), len(FS), len(DAYS)); TAU = np.zeros(shape); GRN = np.zeros(shape); DM = np.zeros(shape); GTE = np.zeros(shape)
    SC = np.zeros(shape); ST = np.zeros(shape)
    for i, k in enumerate(ks):
        for j, s in enumerate(FS):
            for n, d in enumerate(DAYS):
                sw, mx, r, v = S[k, s][d], X[k, s][d], R[k, s][d], V[k, s][d]
                TAU[i, j, n] = run_tau(sw['w22_win']['rows']); GRN[i, j, n] = v['green_mean'] - r['green_mean']
                w = mx['w22']; DM[i, j, n] = w['tl_T'] - w['tl_C']; GTE[i, j, n] = v['timeloss_agent'] - r['timeloss_agent']
                SC[i, j, n] = w['tl_C'] - r['timeloss_agent']; ST[i, j, n] = w['tl_T'] - v['timeloss_agent']
                shares.append(w['n_T'] / max(1, w['n_T'] + w['n_C'])); withheld_zero += w['withheld'] == 0
                wa = [x[8] for x in sw['w22_win']['rows']]; wshares.append(np.mean(wa) if wa else np.nan)
    tau = float(np.nanmean(TAU)); cnt = 0; frng = np.random.default_rng(1)       # Fisher labels: Bernoulli(0.5) per (signal, window), numpy seed 1
    runs = [prep(S[k, s][d]['w22_win']['rows']) for k in ks for s in FS for d in DAYS]
    assert all(abs(tau_arr(*r[:3], r[3], r[4]) - TAU.flat[i]) < 1e-9 or (np.isnan(TAU.flat[i])) for i, r in enumerate(runs)), 'vectorised tau != run_tau'
    for b in range(B):
        tb = np.nanmean([tau_arr(T_, NL, DL, (frng.random(len(T_)) < 0.5).astype(float), K) for T_, NL, DL, _A, K in runs]); cnt += tb >= tau
    p = (1 + cnt) / (1 + B); det = tau > 0 and p < ALPHA
    e = dict(tau=boot(TAU), tau_p=p, green_truth=boot(GRN), DM=boot(DM), GTE=boot(GTE), bias=boot(DM - GTE), spill_C=boot(SC), spill_T=boot(ST))
    out += [f'-- {fam} (lights t{k0}-t{k1})',
            f'  D1 tau (treated - control windows, mean green s): {fmt(e["tau"])}, Fisher one-sided p = {p:.4f} (alpha {ALPHA:.4f}) -> '
            + ('the owner DETECTS the response' if det else 'not detected'),
            f'     ground truth SV - R mean green: {fmt(e["green_truth"])} s',
            f'  D2 per-vehicle A/B DM (treated - control fleet TL): {fmt(e["DM"])} s/veh; GTE = SV - R: {fmt(e["GTE"])}',
            f'     bias = DM - GTE: {fmt(e["bias"])} -> ' + (('the A/B test UNDERSTATES the harm' if e['bias'][2] < 0 else 'the A/B test OVERSTATES the harm')
                                                         if (e['bias'][2] < 0 or e['bias'][1] > 0) else 'no bias shown'),
            f'     spillover on control vehicles TL_C - R: {fmt(e["spill_C"])}; treated TL_T - SV: {fmt(e["spill_T"])}']
    e.update(detected=bool(det)); res[fam] = e
sh, ws = float(np.mean(shares)), float(np.nanmean(wshares)); ok3 = abs(sh - 0.5) <= 0.05 and abs(ws - 0.5) <= 0.05 and withheld_zero == 0
out.insert(1, f'KW22-3 MIX treated share {sh:.3f}, runs with no withheld query {withheld_zero}; SWB treated window share {ws:.3f} -> ' + ('PASS' if ok3 else 'FAIL'))
res['KW22-3'] = dict(share=sh, window_share=ws, withheld_zero=withheld_zero, ok=ok3)
if SM:
    out.append('(smoke: truncated runs against full-length ground-truth rows; numbers meaningless, pipeline check only)')
(D / f'report_w22{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w22{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
if not ok3 and not SM:
    sys.exit(1)
