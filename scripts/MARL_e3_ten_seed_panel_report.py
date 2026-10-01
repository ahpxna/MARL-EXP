#!/usr/bin/env python3
"""Report of the reserved ten-seed panel 2701-2764 x 8/16 (written 01/10/2026 08:4x EDT, BEFORE the panel was run).

Implements two pre-specified files, nothing else:
  * research/marl_budget/PROTOCOL_E3_TEN_SEEDS_20260930.md (ledger L-186): relay6Cage_st_s0..9 under age-first vs the
    same-seed zero-byte students distill_none_s0..9; e_{s,c} = (sum waiting relay)/(sum waiting zero-byte) - 1 over the
    128 paired episodes; primary statistic per condition = mean over the ten seeds; 95 % interval from a two-level
    bootstrap (resample the ten seeds with replacement, then traffic seeds -- both headways together -- WITHIN EACH drawn
    seed), 4000 draws, generator seed 0; SUPPORTED iff the upper bound is < 0 in all three conditions iid / cap4 / low.
    Secondary readings: per-seed effects with traffic-seed intervals; Spearman(mean_c e_s, H_s) (predicted >= 0.5); the
    congestion order; the replicate zero-byte students.
  * research/marl_budget/PROTOCOL_E3_COMM_VALUE_PREDICTOR_20261001.md (direction A): gain_s = -mean_c e_{s,c};
    P-A1 Spearman(N_s, gain_s) >= 0.5; P-A2 Spearman(N_s, gain_s) > Spearman(D_s, gain_s).  N_s is read from
    e3_decision_depth_ten_report_20261001.json (primary_cache.N, development panel); D_s is the list fixed in the protocol.
Sensitivity (labelled, not part of either rule): the same bootstrap with ONE traffic resample shared by every drawn seed
(the convention of scripts/MARL_e3_ten_seed_synthesis.py).
SELF-CHECKS (refuses to give a verdict otherwise): every manifest COMPLETE / PASS; every arm has exactly the 128 episodes
seed2701..seed2764 x load8/load16; every manifest's actor checkpoint is the expected one; the relay arm rows carry the
expected rule; the bootstrap reproduces the point estimate's sign convention on a constant-ratio synthetic check.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); P = M / 'e3_ten_seed_panel_20260930'; A = 'research/marl_budget/e3_delivery_actors_20260929'
EPS = [f'seed{s}_load{h}' for s in range(2701, 2765) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
CONDS = {'iid': ('agefirst_iid', 'prefix'), 'cap4': ('agefirst_iid', 'cap4'), 'low': ('agefirst_low', 'prefix')}
CONG = {'iid': ('prefix_iid', 'prefix'), 'cap4': ('prefix_iid', 'cap4'), 'low': ('prefix_low', 'prefix')}
D_S = dict(enumerate([0.081, 0.076, 0.069, 0.061, 0.080, 0.125, 0.102, 0.043, 0.031, 0.069]))   # fixed in the protocol
PROBLEMS: list[str] = []


def load(tag: str, actor: str, rule: str):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    if m.get('status') != 'COMPLETE' or m.get('self_check') != 'PASS':
        PROBLEMS.append(f'{tag}: manifest {m.get("status")}/{m.get("self_check")}'); return None
    if f'{actor}={A}/{actor}/ckpt_best.pt' not in str(m.get('args')):
        PROBLEMS.append(f'{tag}: actor checkpoint is not {actor}'); return None
    rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['rule'] == rule}
    if sorted(rows) != sorted(EPS):
        PROBLEMS.append(f'{tag}/{rule}: {len(rows)} episodes, not the 128 of the reserved panel'); return None
    return np.array([rows[e] for e in EPS], dtype=float)


def effect(a, b, ii=None):
    return (a.sum() / b.sum() - 1) if ii is None else (a[ii].sum() / b[ii].sum() - 1)


def two_level(pairs: dict[int, tuple], shared: bool, draws=4000, seed=0):
    S = sorted(pairs); rng = np.random.default_rng(seed); bs = []
    for _ in range(draws):
        ss = rng.choice(S, len(S))
        if shared:
            ii = np.concatenate([IDX[TS[p]] for p in rng.choice(len(TS), len(TS))])
            bs.append(np.mean([effect(*pairs[s], ii) for s in ss]))
        else:
            bs.append(np.mean([effect(*pairs[s], np.concatenate([IDX[TS[p]] for p in rng.choice(len(TS), len(TS))]))
                               for s in ss]))
    return np.percentile(bs, [2.5, 97.5])


def per_seed_ci(a, b, draws=4000, seed=0):
    rng = np.random.default_rng(seed)
    bs = [effect(a, b, np.concatenate([IDX[TS[p]] for p in rng.choice(len(TS), len(TS))])) for _ in range(draws)]
    return np.percentile(bs, [2.5, 97.5])


def self_test():
    a = np.full(len(EPS), 9.0); b = np.full(len(EPS), 10.0)
    lo, hi = two_level({0: (a, b), 1: (a, b)}, shared=False, draws=50)
    assert abs(lo + 0.1) < 1e-12 and abs(hi + 0.1) < 1e-12, (lo, hi)


def main():
    self_test()
    Z = {s: load(f'Z_s{s}', f'distill_none_s{s}', 'none') for s in range(10)}
    Zr = {s: load(f'Zrep_s{s}', f'distill_none_rep_s{s}', 'none') for s in range(10)}
    X = {(s, c): load(f'C_s{s}_{t}', f'relay6Cage_st_s{s}', r) for s in range(10) for c, (t, r) in CONDS.items()}
    Y = {(s, c): load(f'C_s{s}_{t}', f'relay6Cage_st_s{s}', r) for s in range(10) for c, (t, r) in CONG.items()}
    out = dict(problems=PROBLEMS, primary={}, per_seed={}, secondary={})
    lines = []
    complete = all(Z[s] is not None for s in range(10)) and all(X[k] is not None for k in X)
    if not complete or PROBLEMS:
        miss = [f'Z_s{s}' for s in range(10) if Z[s] is None] + [f'{k}' for k in X if X[k] is None]
        lines.append(f'PRIMARY NOT COMPLETE: missing/invalid {miss}; problems {PROBLEMS}. No verdict.')
    else:
        verdict = True
        for c in CONDS:
            pairs = {s: (X[(s, c)], Z[s]) for s in range(10)}
            est = float(np.mean([effect(*pairs[s]) for s in range(10)]))
            lo, hi = two_level(pairs, shared=False); slo, shi = two_level(pairs, shared=True)
            verdict &= bool(hi < 0)
            out['primary'][c] = dict(mean=100 * est, lo=100 * lo, hi=100 * hi, shared_lo=100 * slo, shared_hi=100 * shi)
            lines.append(f'PRIMARY {c:5s}: mean e = {100*est:+.2f} % [{100*lo:+.2f}, {100*hi:+.2f}]  '
                         f'(sensitivity, shared traffic resample: [{100*slo:+.2f}, {100*shi:+.2f}])')
        out['verdict'] = 'SUPPORTED' if verdict else 'NOT SUPPORTED'
        lines.append(f'RULE (upper < 0 in all three conditions): {out["verdict"]}')
        e = {}
        for s in range(10):
            cells = {}
            for c in CONDS:
                lo, hi = per_seed_ci(X[(s, c)], Z[s]); cells[c] = (100 * effect(X[(s, c)], Z[s]), 100 * lo, 100 * hi)
            e[s] = float(np.mean([v[0] for v in cells.values()])); out['per_seed'][s] = dict(cells=cells, mean=e[s])
            lines.append(f'  s{s}: mean {e[s]:+.2f} %  ' + '  '.join(f'{c} {v[0]:+.2f}[{v[1]:+.2f},{v[2]:+.2f}]'
                                                                  for c, v in cells.items()))
        # secondary: teacher headroom (development, L-160/L-170)
        H = {int(k): v for k, v in json.loads((M / 'e3_seed_prediction_report_20260930.json').read_text())['H'].items()}
        hs = sorted(set(H) & set(e)); rH = float(spearmanr([e[s] for s in hs], [H[s] for s in hs]).correlation)
        out['secondary']['spearman_e_H'] = dict(seeds=hs, rho=rH, predicted='>= 0.5')
        lines.append(f'SECONDARY Spearman(e_s, H_s) over {hs}: {rH:.3f} (predicted >= 0.5)')
        # direction A
        N = {int(k): v for k, v in json.loads((M / 'e3_decision_depth_ten_report_20261001.json').read_text())
             ['primary_cache']['N'].items()}
        gain = {s: -e[s] for s in range(10)}
        rN = float(spearmanr([N[s] for s in range(10)], [gain[s] for s in range(10)]).correlation)
        rD = float(spearmanr([D_S[s] for s in range(10)], [gain[s] for s in range(10)]).correlation)
        out['direction_A'] = dict(N=N, D=D_S, gain=gain, rho_N=rN, rho_D=rD, PA1=bool(rN >= 0.5), PA2=bool(rN > rD))
        lines.append(f'DIRECTION A  Spearman(N_s, gain_s) = {rN:.3f}  P-A1 (>= 0.5): {"SUPPORTED" if rN >= 0.5 else "NOT SUPPORTED"}'
                     f' | Spearman(D_s, gain_s) = {rD:.3f}  P-A2 (N beats D): {"SUPPORTED" if rN > rD else "NOT SUPPORTED"}')
    # secondary arms, whatever is complete
    for name, arm, ref in (('congestion order vs Z', Y, Z), ('age-first vs Zrep', X, Zr)):
        for c in CONDS:
            S = [s for s in range(10) if arm[(s, c)] is not None and ref[s] is not None]
            if not S:
                continue
            pairs = {s: (arm[(s, c)], ref[s]) for s in S}
            est = float(np.mean([effect(*pairs[s]) for s in S])); lo, hi = two_level(pairs, shared=False)
            out['secondary'][f'{name}/{c}'] = dict(seeds=S, mean=100 * est, lo=100 * lo, hi=100 * hi,
                                                   per_seed={s: 100 * effect(*pairs[s]) for s in S})
            lines.append(f'SECONDARY {name:22s} {c:5s} on {len(S)} seeds: {100*est:+.2f} % [{100*lo:+.2f}, {100*hi:+.2f}]  '
                         f'below 0: {sum(effect(*pairs[s]) < 0 for s in S)}/{len(S)}')
    text = '\n'.join(lines); print(text)
    (M / 'e3_ten_seed_panel_report_20261001.json').write_text(json.dumps(out, indent=1, default=float))
    (M / 'e3_ten_seed_panel_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
