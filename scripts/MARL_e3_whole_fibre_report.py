#!/usr/bin/env python3
"""Report of PROTOCOL_E3_WHOLE_FIBRE_PILOT_20261001.md (written 01/10/2026 10:5x EDT, BEFORE the runs).

Per receiver-state: A_eps(w) = {a : V(w,a) >= max_b V(w,b) - eps |V(w, a_exec(w))|}; obstruction O = [intersection over F of
A_eps = empty]; teacher proxies need_cache / need_empty (A_0.25 of the teacher's full-view logits).  Rules K1-K3 and the
direction P exactly as in the protocol.  Secondaries: representability (does some sender's raw / 3 B block split each
conflicting pair), the exact hitting number of F by sender sets, teacher quality, fibre sizes, agreement with need_empty.
"""
from __future__ import annotations
import itertools, json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_whole_fibre_20261001'
EPS = (0.001, 0.005, 0.02); PRIMARY = 0.005; SEEDS = (1, 8)


def acc(w, eps):
    V = {int(k): v for k, v in w['V'].items()}; top = max(V.values()); tol = eps * abs(V[w['a_exec']])
    return {a for a, v in V.items() if v >= top - tol - 1e-9}


def need(L_full, L_other):
    f = np.asarray(L_full); return bool(f[int(np.argmax(L_other))] < f.max() - 0.25 - 1e-9)


def kappa(x, y):
    x = np.asarray(x, bool); y = np.asarray(y, bool); po = np.mean(x == y)
    pe = np.mean(x) * np.mean(y) + (1 - np.mean(x)) * (1 - np.mean(y))
    return float('nan') if pe >= 1 else float((po - pe) / (1 - pe))


def hitting(ws, eps, key):
    senders = sorted(ws[0][key]); As = [acc(w, eps) for w in ws]
    def safe(S):
        cls = {}
        for w, A in zip(ws, As):
            cls.setdefault(tuple(w[key][j] for j in S), []).append(A)
        return all(set.intersection(*c) for c in cls.values())
    for k in range(len(senders) + 1):
        for S in itertools.combinations(senders, k):
            if safe(S):
                return k
    return None                                            # not resolvable by any sender set: representability failure


def load_rows(s):
    rows = []
    for f in sorted((P / f's{s}').glob('rows_shard*.json')):
        rows += json.loads(f.read_text())
    return rows


def main():
    R = {s: load_rows(s) for s in SEEDS}; out = dict(n_states={s: len(R[s]) for s in SEEDS}); L = []
    man_ok = all((P / f's{s}' / f'manifest_shard{h}.json').exists() and
                 json.loads((P / f's{s}' / f'manifest_shard{h}.json').read_text()).get('status') == 'COMPLETE'
                 for s in SEEDS for h in (0, 1))
    if not man_ok or any(len(R[s]) != 64 for s in SEEDS):
        print('INCOMPLETE (need 64 states per seed and both shard manifests COMPLETE):', out['n_states'], 'manifests ok', man_ok); return
    stats = {}
    for eps in EPS:
        for s in SEEDS:
            O = [not set.intersection(*[acc(w, eps) for w in r['worlds']]) for r in R[s]]
            stats[(s, eps)] = O
    nc = {s: [need(r['teacher']['L_full'], r['teacher']['L_cache']) for r in R[s]] for s in SEEDS}
    ne = {s: [need(r['teacher']['L_full'], r['teacher']['L_empty']) for r in R[s]] for s in SEEDS}
    rate = {(s, e): float(np.mean(stats[(s, e)])) for s in SEEDS for e in EPS}
    pooled = {e: float(np.mean(sum((stats[(s, e)] for s in SEEDS), []))) for e in EPS}
    Opool = sum((stats[(s, PRIMARY)] for s in SEEDS), []); NCpool = sum((nc[s] for s in SEEDS), []); NEpool = sum((ne[s] for s in SEEDS), [])
    k_cache, k_empty = kappa(Opool, NCpool), kappa(Opool, NEpool)
    K1 = pooled[PRIMARY] < 0.05; K2 = (not np.isfinite(k_cache)) or k_cache < 0.1
    K3 = (pooled[0.02] == 0 and pooled[0.001] > 0) or (pooled[0.02] > 0 and pooled[0.001] > 3 * pooled[0.02])
    rng = np.random.default_rng(0); a1 = np.asarray(stats[(1, PRIMARY)], float); a8 = np.asarray(stats[(8, PRIMARY)], float)
    bs = [a1[rng.integers(0, len(a1), len(a1))].mean() > a8[rng.integers(0, len(a8), len(a8))].mean() for _ in range(4000)]
    out.update(rate={f's{s}_eps{e}': rate[(s, e)] for s in SEEDS for e in EPS}, pooled=pooled, kappa_cache=k_cache, kappa_empty=k_empty,
               need_cache_rate={s: float(np.mean(nc[s])) for s in SEEDS}, need_empty_rate={s: float(np.mean(ne[s])) for s in SEEDS},
               K1=bool(K1), K2=bool(K2), K3=bool(K3), P_s1_gt_s8=bool(rate[(1, PRIMARY)] > rate[(8, PRIMARY)]),
               P_bootstrap=float(np.mean(bs)), GO=not (K1 or K2 or K3))
    L.append('obstruction rate by eps: ' + ' | '.join(f'eps {e}: s1 {rate[(1, e)]:.3f} s8 {rate[(8, e)]:.3f} pooled {pooled[e]:.3f}' for e in EPS))
    L.append(f'teacher need (cache base, N_s definition): s1 {np.mean(nc[1]):.3f} s8 {np.mean(nc[8]):.3f}; empty base: s1 {np.mean(ne[1]):.3f} s8 {np.mean(ne[8]):.3f}')
    L.append(f'Cohen kappa(O, need_cache) = {k_cache:.3f}; kappa(O, need_empty) = {k_empty:.3f}')
    L.append(f'K1 (pooled rate < 5 %): {"TRIGGERED" if K1 else "not triggered"} | K2 (kappa < 0.1): {"TRIGGERED" if K2 else "not triggered"} | '
             f'K3 (unstable in eps): {"TRIGGERED" if K3 else "not triggered"} -> {"GO" if out["GO"] else "NO GO"}')
    L.append(f'P rate(s1) > rate(s8): {out["P_s1_gt_s8"]} (bootstrap share {out["P_bootstrap"]:.3f})')
    sec = {}
    for s in SEEDS:
        hr = [hitting(r['worlds'], PRIMARY, 'raw') for r, o in zip(R[s], stats[(s, PRIMARY)]) if o]
        hq = [hitting(r['worlds'], PRIMARY, 'quant') for r, o in zip(R[s], stats[(s, PRIMARY)]) if o]
        tq = float(np.mean([int(np.argmax(r['teacher']['L_full'])) in acc(r['worlds'][0], PRIMARY) for r in R[s]]))
        sec[s] = dict(obstructions=len(hr), raw_hitting=hr, quant_hitting=hq, raw_unresolvable=sum(h is None for h in hr),
                      quant_unresolvable=sum(h is None for h in hq), teacher_action_in_A=tq,
                      fibre_size_mean=float(np.mean([len(r['worlds']) for r in R[s]])))
        L.append(f'  s{s}: obstructions {len(hr)}/{len(R[s])}; hitting number (raw) ' +
                 f'{[h for h in hr if h is not None]} unresolvable {sec[s]["raw_unresolvable"]}; (3 B) unresolvable {sec[s]["quant_unresolvable"]}; '
                 f'teacher full-view action in A_eps {tq:.3f}; mean |F| {sec[s]["fibre_size_mean"]:.1f}')
    out['secondary'] = sec
    text = '\n'.join(L); print(text)
    (M / 'e3_whole_fibre_report_20261001.json').write_text(json.dumps(out, indent=1, default=str))
    (M / 'e3_whole_fibre_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
