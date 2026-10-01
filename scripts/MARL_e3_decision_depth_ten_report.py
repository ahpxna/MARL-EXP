#!/usr/bin/env python3
"""V-D10 report (research/marl_budget/PROTOCOL_E3_DECISION_DEPTH_TEN_SEEDS_20261001.md, written 01:08 EDT before the runs).

PRIMARY (as pre-registered): N_s = 1 - share of receiver-steps whose teacher action with no FRESH sender (v1 probe, i.e.
on top of the direct cache) is in A_0.25; prediction Spearman(N_s, -G_s) >= 0.5, with G_s the development relay-vs-zero-
byte effect of e3_seed_prediction_report_20260930.json.  Also Spearman(N_s, -H_s) against the BYTEBUDGET headroom.
SECONDARY (not pre-registered; ADDENDUM 01:15): the same with the EMPTY base (v2 probe, pure decision depth).
SELF-CHECK: refuses to report unless all ten seeds are complete with full parity.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

R = Path('research/marl_budget')


def spearman(x, y):
    rx = np.argsort(np.argsort(x)); ry = np.argsort(np.argsort(y))
    return float(np.corrcoef(rx, ry)[0, 1])


def need(dirpath, key):
    m = json.loads((dirpath / 'manifest.json').read_text())
    if m.get('self_check') != 'PASS' or m['parity_episodes'] != 128:
        raise SystemExit(f'{dirpath}: incomplete')
    z = np.load(dirpath / 'depth.npz')
    return float(1.0 - np.mean(z[key][:, 1] == 0))


def main():
    pred = json.loads((R / 'e3_seed_prediction_report_20260930.json').read_text())
    G = {int(k): v for k, v in pred['G'].items()}; H = {int(k): v for k, v in pred['H'].items()}
    out = {}
    for label, base_dir, key in (('primary_cache', R / 'e3_decision_depth_ten_20261001', 'minset'),
                                 ('secondary_empty', R / 'e3_decision_depth_v2_20261001', 'minset_empty')):
        Ns = {}
        for s in range(10):
            d = base_dir / f'cage_s{s}_agefirst_low'
            if not (d / 'manifest.json').exists():
                print(f'{label}: seed {s} not complete'); break
            Ns[s] = need(d, key)
        else:
            seeds = sorted(Ns)
            rhoG = spearman([Ns[s] for s in seeds], [-G[s] for s in seeds])
            hs = [s for s in seeds if s in H]
            rhoH = spearman([Ns[s] for s in hs], [-H[s] for s in hs])
            out[label] = dict(N=Ns, rho_G=rhoG, rho_H=rhoH, threshold=0.5, supported=rhoG >= 0.5)
            print(f'{label}: N_s ' + ' '.join(f'{s}:{Ns[s]:.3f}' for s in seeds) +
                  f' | Spearman(N, -G) = {rhoG:.3f} (pre-registered >= 0.5: {"SUPPORTED" if rhoG >= 0.5 else "NOT SUPPORTED"})'
                  f' | Spearman(N, -H) = {rhoH:.3f} on {len(hs)} seeds')
    if out:
        (R / 'e3_decision_depth_ten_report_20261001.json').write_text(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
