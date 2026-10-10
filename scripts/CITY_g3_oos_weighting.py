#!/usr/bin/env python3
"""E5-G3 (PROTOCOL_E3_E12_E14_G3_G6_20261004, frozen 01:21 EDT 04/10): out-of-support mass vs weighted out-of-support mass as
predictors of the mismatch penalty, on the C0 EXACT Z tables (frozen rerun research/city_sim/c0_g3_frozen_20261004, byte-identical
to c0_v3's tables and panels).  Controllers Z*_T (10 lights), pairs (T, D), T != D (90); target
Delta(T, D) = mean regret(Z*_T on D's panel) - mean regret(Z*_D on D's panel).  Per decision step of Z*_T driving on D's panel
(OOS: tau >= hi_T, where the table clips tau to hi_T - 1):
  RAW    share of OOS steps                                                   (deployable)
  SENS   share of OOS steps where the controller's action at (x, v, colour) is not constant over tau in [0, hi_T - 1]   (deployable)
  STAKES mean of 1[OOS] (max_a Q_T - min_a Q_T) at the clipped state          (deployable)
  ORACLE mean of 1[OOS] A_D(s, a_T), D's own table's advantage loss            (diagnostic, not deployable)
Fit / test: H1 = {FT, EXT, A1, A3, A5}, H2 = {ACT, CUT, A2, A4, A6}; on the fit half pick SENS or STAKES by Spearman with Delta;
on the held-out half compare Spearman(chosen, Delta) with Spearman(RAW, Delta); both directions; bootstrap 1000 draws (panel
episodes resampled within each D, paired across controllers).  G3a SUPPORTED iff in BOTH directions held-out Spearman(chosen) >
Spearman(RAW) with bootstrap lower bound of the difference > 0.
SELF-CHECKS (no manifest otherwise): (1) parity — the diagonal regrets equal the C0 testbed's own rollout of the same table;
(2) Bellman consistency — V_D(s) = min_a Q_D(s, a) at every visited state of the diagonal runs (float32 tolerance);
(3) performance-difference identity over ALL steps — mean sum_t A_D(s_t, a_T) = mean[cost_T - 1{timeout}(TIMEOUT - V_D(s_T))]
    - mean V_D(s0) up to sampling noise (the timeout term is the exact correction for the 150 s horizon); the run fails if a pair
    with |Delta| > 1 has |residual| > max(10 % |Delta|, 4 SE); (4) panel / table / testbed sha256 recorded and unchanged."""
from __future__ import annotations
import argparse, hashlib, json, time
from multiprocessing import Pool
from pathlib import Path
import sys
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_c0_testbed as C0  # noqa: E402

PAN = ROOT / 'research/city_sim/c0_g3_frozen_20261004/panels'
LIGHTS = ['FT', 'ACT', 'EXT', 'CUT', 'A1', 'A2', 'A3', 'A4', 'A5', 'A6']
H1, H2 = ['FT', 'EXT', 'A1', 'A3', 'A5'], ['ACT', 'CUT', 'A2', 'A4', 'A6']
NE = None


def set_ne(n):
    global NE
    NE = n


def tables():
    return {L: C0.load_tables(PAN.parent, L)['Z'] for L in LIGHTS}


def panel(L):
    P = C0.load_panel(PAN.parent, L, 'eval')
    if NE:
        P = {k: v[:NE] for k, v in P.items()}
    return P


def run_pair(VT, T, VD, D, P):
    """Roll Z*_T out on D's panel; per-episode accumulators."""
    N = len(P['x0']); x = P['x0'].astype(np.int64).copy(); v = P['v0'].astype(np.int64).copy(); alive = np.ones(N, bool)
    hiT, hiD = VT.shape[3], VD.shape[3]
    acc = {k: np.zeros(N) for k in ('cost', 'steps', 'oos', 'sens', 'stakes', 'oracle', 'adv_all', 'bell')}
    g0, t0_ = P['green'][:, 0].astype(int), P['tau'][:, 0]
    V0 = VD[x + C0.XM, v, g0, np.minimum(t0_, hiD - 1)].astype(np.float64)
    for t in range(C0.T):
        idx = np.flatnonzero(alive)
        if len(idx) == 0:
            break
        g, ta, rs = P['green'][idx, t], P['tau'][idx, t], P['res'][idx, t]; xi, vi = x[idx], v[idx]
        QT = C0.table_q(VT, 'Z', T, xi, vi, g, ta, rs).astype(np.float64); a = QT.argmin(1)
        QD = C0.table_q(VD, 'Z', D, xi, vi, g, ta, rs).astype(np.float64)
        adv = QD[np.arange(len(idx)), a] - QD.min(1)
        vd = VD[xi + C0.XM, vi, g.astype(int), np.minimum(ta, hiD - 1)].astype(np.float64)
        acc['bell'][idx] = np.maximum(acc['bell'][idx], np.abs(QD.min(1) - vd))
        oos = ta >= hiT
        acc['steps'][idx] += 1; acc['oos'][idx] += oos; acc['adv_all'][idx] += adv
        if oos.any():
            o = np.flatnonzero(oos); acc['stakes'][idx[o]] += QT[o].max(1) - QT[o].min(1); acc['oracle'][idx[o]] += adv[o]
            base = a[o]; varies = np.zeros(len(o), bool)
            for tp in range(hiT):
                ap = C0.table_q(VT, 'Z', T, xi[o], vi[o], g[o], np.full(len(o), tp), rs[o]).argmin(1); varies |= ap != base
            acc['sens'][idx[o]] += varies
        x2, v2, c, passed, forced = C0.step(xi, vi, a, P['green'][idx, t + 1])
        acc['cost'][idx] += c; x[idx], v[idx] = x2, v2; alive[idx[passed]] = False
    to = alive.copy()
    VT_end = np.zeros(N)
    if to.any():
        ii = np.flatnonzero(to); gT, tT = P['green'][ii, C0.T].astype(int), P['tau'][ii, C0.T]
        VT_end[ii] = VD[x[ii] + C0.XM, v[ii], gT, np.minimum(tT, hiD - 1)]
    acc['cost'][to] += C0.TIMEOUT
    acc['regret'] = acc['cost'] - P['topt']; acc['timeout'] = to.astype(float)
    acc['pdl_target'] = acc['cost'] - to * (C0.TIMEOUT - VT_end) - V0
    return acc


def work(T):
    V = tables(); out = {}
    for D in LIGHTS:
        P = panel(D); t0 = time.perf_counter(); out[D] = run_pair(V[T], T, V[D], D, P)
        print(f'  {T} on {D}: regret {out[D]["regret"].mean():.2f} oos {out[D]["oos"].sum() / out[D]["steps"].sum():.3f} '
              f'[{time.perf_counter() - t0:.0f}s]', flush=True)
    return T, out


def spearman(x, y):
    rk = lambda z: np.argsort(np.argsort(z, kind='stable'), kind='stable').astype(float)
    x, y = np.asarray(x, float), np.asarray(y, float)
    return float(np.corrcoef(rk(x), rk(y))[0, 1]) if np.std(x) > 0 and np.std(y) > 0 else float('nan')


def kendall(x, y):
    n = len(x); s = 0
    for i in range(n):
        for j in range(i + 1, n):
            s += np.sign(x[i] - x[j]) * np.sign(y[i] - y[j])
    return float(s / (n * (n - 1) / 2))


def stats_of(R, sel=None):
    """Per-pair Delta and predictors; sel = {D: episode index array} for the bootstrap."""
    out = {}
    for T in LIGHTS:
        for D in LIGHTS:
            if T == D:
                continue
            a, d = R[T][D], R[D][D]; ix = sel[D] if sel is not None else slice(None)
            st = a['steps'][ix].sum()
            out[(T, D)] = dict(delta=a['regret'][ix].mean() - d['regret'][ix].mean(), RAW=a['oos'][ix].sum() / st,
                               SENS=a['sens'][ix].sum() / st, STAKES=a['stakes'][ix].sum() / st, ORACLE=a['oracle'][ix].sum() / st)
    return out


def main(a):
    global NE
    NE = a.max_episodes; out = Path(a.out); out.mkdir(parents=True, exist_ok=False); t0 = time.perf_counter()
    sha = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__), ROOT / 'scripts/CITY_c0_testbed.py'] + sorted(PAN.glob('*_tables.npz')) + sorted(PAN.glob('*_eval.npz'))}
    with Pool(a.procs, initializer=set_ne, initargs=(NE,)) as pool:
        R = dict(pool.map(work, LIGHTS))
    # self-check 1: parity with the testbed's own rollout on the diagonal
    V = tables()
    for D in LIGHTS:
        P = panel(D); ref = C0.rollout(C0.table_policy(V[D], 'Z', D), P)['regret']
        if not np.allclose(ref, R[D][D]['regret'], atol=1e-9):
            raise SystemExit(f'SELF-CHECK FAIL parity {D}: {ref.mean()} vs {R[D][D]["regret"].mean()}')
    bell = max(float(R[D][D]['bell'].max()) for D in LIGHTS)
    if bell > 1e-3:
        raise SystemExit(f'SELF-CHECK FAIL Bellman consistency: max |min Q - V| = {bell}')
    S = stats_of(R); pdl = {}; bad = []
    for (T, D), s in S.items():
        diff = R[T][D]['adv_all'] - R[T][D]['pdl_target']; se = diff.std(ddof=1) / np.sqrt(len(diff))
        pdl[f'{T}|{D}'] = dict(resid=float(diff.mean()), se=float(se), delta=float(s['delta']), timeouts=float(R[T][D]['timeout'].mean()))
        if abs(s['delta']) > 1 and abs(diff.mean()) > max(0.1 * abs(s['delta']), 4 * se):
            bad.append((T, D, float(diff.mean()), float(s['delta'])))
    if bad:
        raise SystemExit(f'SELF-CHECK FAIL performance-difference identity: {bad[:5]} ({len(bad)})')
    lines = []; res = dict(pairs={f'{T}|{D}': s for (T, D), s in S.items()}, pdl=pdl, directions={})
    rng = np.random.default_rng(0); N = len(R['ACT']['ACT']['regret'])
    draws = [{D: rng.integers(0, N, N) for D in LIGHTS} for _ in range(a.boot)]; BS = [stats_of(R, sel) for sel in draws]
    ok = True
    for fit, test in ((H1, H2), (H2, H1)):
        pf = [k for k in S if k[0] in fit]; pt = [k for k in S if k[0] in test]
        sp = lambda st, ks, key: spearman([st[k][key] for k in ks], [st[k]['delta'] for k in ks])
        chosen = max(('SENS', 'STAKES'), key=lambda key: sp(S, pf, key))
        d0 = sp(S, pt, chosen) - sp(S, pt, 'RAW'); db = np.array([sp(b, pt, chosen) - sp(b, pt, 'RAW') for b in BS])
        lo, hi = np.percentile(db, [2.5, 97.5]); sup = d0 > 0 and lo > 0; ok &= sup
        tag = f"fit {'H1' if fit is H1 else 'H2'} -> test {'H2' if fit is H1 else 'H1'}"
        res['directions'][tag] = dict(chosen=chosen, fit_spearman={k: sp(S, pf, k) for k in ('RAW', 'SENS', 'STAKES', 'ORACLE')},
                                      test_spearman={k: sp(S, pt, k) for k in ('RAW', 'SENS', 'STAKES', 'ORACLE')},
                                      test_kendall={k: kendall([S[q][k] for q in pt], [S[q]['delta'] for q in pt]) for k in ('RAW', 'SENS', 'STAKES', 'ORACLE')},
                                      diff=float(d0), ci=[float(lo), float(hi)], supported=bool(sup))
        r_ = res['directions'][tag]
        lines.append(f"{tag}: chosen {chosen} (fit Spearman RAW {r_['fit_spearman']['RAW']:+.2f} SENS {r_['fit_spearman']['SENS']:+.2f} STAKES {r_['fit_spearman']['STAKES']:+.2f}); "
                     f"held-out Spearman RAW {r_['test_spearman']['RAW']:+.2f} {chosen} {r_['test_spearman'][chosen]:+.2f} ORACLE {r_['test_spearman']['ORACLE']:+.2f}; "
                     f"difference {d0:+.2f} [{lo:+.2f}, {hi:+.2f}] -> {'holds' if sup else 'fails'}")
    lines.insert(0, f"G3a (weighted beats raw on held-out controllers, both directions): {'SUPPORTED' if ok else 'NOT SUPPORTED'}")
    share = [s['ORACLE'] * R[T][D]['steps'].sum() / len(R[T][D]['steps']) / s['delta'] for (T, D), s in S.items() if s['delta'] > 1]
    lines.append(f"ORACLE out-of-support share of Delta over pairs with Delta > 1: median {np.median(share):.2f}, min {np.min(share):.2f}, max {np.max(share):.2f} (in-support harm = 1 - share)")
    lines.append(f"self-checks: parity PASS (10 diagonals), Bellman max |minQ - V| {bell:.2e}, performance-difference identity PASS (max |resid| / SE "
                 f"{max(abs(p['resid']) / max(p['se'], 1e-12) for p in pdl.values()):.1f})")
    if sha != {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__), ROOT / 'scripts/CITY_c0_testbed.py'] + sorted(PAN.glob('*_tables.npz')) + sorted(PAN.glob('*_eval.npz'))}:
        raise RuntimeError('source changed during run')
    np.savez_compressed(out / 'per_episode.npz', **{f'{T}|{D}|{k}': v for T in R for D in R[T] for k, v in R[T][D].items()})
    (out / 'result.json').write_text(json.dumps(res, indent=1, default=float)); (out / 'report.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), sha256=sha, seconds=time.perf_counter() - t0), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', required=True); p.add_argument('--procs', type=int, default=3); p.add_argument('--boot', type=int, default=1000)
    p.add_argument('--max-episodes', type=int, default=None, help='smoke: first N panel episodes')
    main(p.parse_args())
