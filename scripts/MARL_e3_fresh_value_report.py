#!/usr/bin/env python3
"""Report of PROTOCOL_E3_COMPAT_MAP_20261001.md Addendum 1, Part D (written before the runs; EXPLORATORY: gains known).
Per cell (seeds 0-9): fresh-witness rate per fresh packet (senders held at t - 1), W_F = fresh witnesses per receiver-step,
W_S = relayed witnesses with age >= 3 per receiver-step (Part C records), N = W_F - W_S.  BF1, BF2 as in the addendum."""
from __future__ import annotations
import json, sys
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.MARL_e3_witness_burden_report import CELLS, gains, W as WC

M = Path('research/marl_budget'); P = M / 'e3_fresh_value_20261001'; S = range(10); STEPS = 1872


def main():
    g = gains(); out = {}; L = ['order | capacity | fresh packets / step | new-sender share | fresh-witness rate | W_F | W_S (a>=3) | N = W_F - W_S | gain vs Z']
    for o, c in CELLS:
        ds = [P / f'{o}_{c}_s{s}' for s in S]
        if not all((d / 'manifest.json').exists() for d in ds):
            L.append(f'{o} | {c} | INCOMPLETE'); continue
        nf, new, rate, WF, WS = [], [], [], [], []
        for s, d in zip(S, ds):
            z = np.load(d / 'fresh_value.npz'); w = np.load(WC / f'{o}_{c}_s{s}' / 'witness.npz'); held = z['witness'] >= 0
            nf.append(len(z['witness']) / STEPS); new.append(float((~held).mean())); rate.append(float(z['witness'][held].mean()))
            WF.append(float(z['witness'][held].sum() / STEPS)); WS.append(float(w['witness'][w['age'] >= 3].sum() / STEPS))
        r = dict(fresh=float(np.mean(nf)), new=float(np.mean(new)), rate=float(np.mean(rate)), WF=float(np.mean(WF)), WS=float(np.mean(WS)), gain=g[(o, c)])
        r['N'] = r['WF'] - r['WS']; out[(o, c)] = r
        L.append(f'{o} | {c} | {r["fresh"]:.2f} | {r["new"]:.3f} | {r["rate"]:.3f} | {r["WF"]:.3f} | {r["WS"]:.3f} | {r["N"]:+.3f} | {r["gain"]:+.2f} %')
    if len(out) == len(CELLS):
        bf1 = {c: (out[('prefix', c)]['rate'], out[('agefirst', c)]['rate']) for c in ('iid', 'cap4', 'low')}
        BF1 = all(p >= 1.2 * a for p, a in bf1.values())
        ks = list(out); rN = float(spearmanr([out[k]['N'] for k in ks], [out[k]['gain'] for k in ks]).correlation)
        rWF = float(spearmanr([out[k]['WF'] for k in ks], [out[k]['gain'] for k in ks]).correlation)
        cond = all(out[('prefix', c)]['N'] > out[('agefirst', 'const1')]['N'] for c in ('cap4', 'low'))
        BF2 = rN >= 0.85 and cond
        L += ['BF1 fresh-witness rate congestion vs age-first (need >= 1.2x): ' + ', '.join(f'{c} {p:.3f} vs {a:.3f}' for c, (p, a) in bf1.items())
              + f' -> {"SUPPORTED" if BF1 else "NOT SUPPORTED"}',
              f'BF2 Spearman(N, gain) {rN:+.3f} (need >= +0.85; W_F alone {rWF:+.3f}; B_3 alone -0.778), congestion cap4/low N above '
              f'age-first const1: {cond} -> {"SUPPORTED" if BF2 else "NOT SUPPORTED"}']
    text = '\n'.join(L); print(text); (M / 'e3_fresh_value_report_20261001.txt').write_text(text + '\n')
    (M / 'e3_fresh_value_report_20261001.json').write_text(json.dumps({f'{o}|{c}': v for (o, c), v in out.items()}, indent=1))


if __name__ == '__main__':
    main()
