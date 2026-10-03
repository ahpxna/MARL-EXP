#!/usr/bin/env python3
"""Reports of the queued tests (written 02/10/2026 15:2x EDT, before any of their runs).
  --test C : PROTOCOL_E3_MIX2_20261002 (3x3, panel 4501-4564, seeds 0-4): C1 relayMIX2 >= relayMIX - 0.3 at K2 and K3;
             C2 relayMIX2 at K1 >= 0 with lower bound > -0.5, and at iid >= relay6Cage - 0.3.
  --test D : PROTOCOL_E3_G4_MIX_20261002 (4x4, panel 4601-4664, seeds 0-9): D1 relayMIX vs Z at K1 >= 0, lower > -0.5;
             D2 relayMIX vs relayCage at iid >= -0.5; D3 relayMIX's worst gain over K > relayCage's and relayCK1's."""
import argparse, json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); NAME = {1: 'K=1', 2: 'K=2', 3: 'K=3', 0: 'iid'}
CFG = {'C': dict(P=M / 'e3_mix2_20261002', panel=range(4501, 4565), seeds=list(range(5)), arms=('relayMIX2_st', 'relayMIX_st', 'relay6Cage_st', 'relayCK1_st')),
       'D': dict(P=M / 'e3_g4_mix_20261002', panel=range(4601, 4665), seeds=list(range(10)), arms=('relayMIX_st', 'relayCage_st', 'relayCK1_st'))}


def main(a):
    c = CFG[a.test]; P = c['P']; SEEDS = c['seeds']; EPS = [f'seed{s}_load{h}' for s in c['panel'] for h in (8, 16)]
    TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
    def load(tag, rule, ck):
        d = P / tag
        if not (d / 'manifest.json').exists():
            return None
        m = json.loads((d / 'manifest.json').read_text()); assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
        assert f'{ck}/ckpt_best.pt' in str(m.get('args')), tag
        rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['rule'] == rule}
        assert sorted(rows) == sorted(EPS), tag
        return np.array([rows[e] for e in EPS], float)
    gain = lambda x, y, ii=None: -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100
    def boot(X, Y):
        rng = np.random.default_rng(0); bs = []
        for _ in range(4000):
            ss = rng.choice(SEEDS, len(SEEDS))
            bs.append(np.mean([gain(X[s], Y[s], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
        return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]
    Z = {s: load(f'Z_s{s}', 'none', f'distill_none_s{s}') for s in SEEDS}
    R = {(r, s, K): load(f'R_{r}_s{s}_K{K}', 'prefix', f'{r}_s{s}') for r in c['arms'] for s in SEEDS for K in (1, 2, 3, 0)}
    allv = list(Z.values()) + list(R.values())
    if any(v is None for v in allv):
        print(f'INCOMPLETE: {sum(v is None for v in allv)} of {len(allv)} items missing'); return
    G = {(r, K): float(np.mean([gain(R[(r, s, K)], Z[s]) for s in SEEDS])) for r in c['arms'] for K in (1, 2, 3, 0)}
    L = [f'test {a.test}: gain vs Z (95 %)'] + [f'{r} | ' + ' | '.join(f'{NAME[K]} {G[(r, K)]:+.2f} {boot({s: R[(r, s, K)] for s in SEEDS}, Z)}' for K in (1, 2, 3, 0)) for r in c['arms']]
    if a.test == 'C':
        c1 = all(G[('relayMIX2_st', K)] >= G[('relayMIX_st', K)] - 0.3 for K in (2, 3)); ci = boot({s: R[('relayMIX2_st', s, 1)] for s in SEEDS}, Z)
        c2 = G[('relayMIX2_st', 1)] >= 0 and ci[0] > -0.5 and G[('relayMIX2_st', 0)] >= G[('relay6Cage_st', 0)] - 0.3
        L += [f'C1 coverage of the middle (K2, K3 within 0.3 of relayMIX) -> {"SUPPORTED" if c1 else "NOT SUPPORTED"}', f'C2 extremes kept -> {"SUPPORTED" if c2 else "NOT SUPPORTED"}']
    else:
        ci = boot({s: R[('relayMIX_st', s, 1)] for s in SEEDS}, Z); d1 = G[('relayMIX_st', 1)] >= 0 and ci[0] > -0.5
        e = [gain(R[('relayMIX_st', s, 0)], R[('relayCage_st', s, 0)]) for s in SEEDS]; d2 = float(np.mean(e)) >= -0.5
        worst = {r: min(G[(r, K)] for K in (1, 2, 3, 0)) for r in c['arms']}; d3 = worst['relayMIX_st'] > max(worst['relayCage_st'], worst['relayCK1_st'])
        L += [f'D1 repair at K1: {G[("relayMIX_st", 1)]:+.2f} {ci} -> {"SUPPORTED" if d1 else "NOT SUPPORTED"}', f'D2 no cost at iid: {np.mean(e):+.2f} % -> {"SUPPORTED" if d2 else "NOT SUPPORTED"}',
              f'D3 best worst case: ' + ', '.join(f'{r} {v:+.2f}' for r, v in worst.items()) + f' -> {"SUPPORTED" if d3 else "NOT SUPPORTED"}']
    text = '\n'.join(L); print(text); (M / f'e3_mixq_{a.test}_report_20261002.txt').write_text(text + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--test', choices=['C', 'D'], required=True); main(p.parse_args())
