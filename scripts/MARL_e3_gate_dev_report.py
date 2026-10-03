#!/usr/bin/env python3
"""EXPLORATORY development-panel look at the silence-fallback gates (e3_gate_dev_20261001; seed901-904 x 8/16, seeds 0-9).
Per arm and K: mean gain vs Z (e3_dev_Z), vs the plain relay (e3_negflip rows), seeds with gain >= 0, fallback share."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_gate_dev_20261001'; ARMS = ('clip', 'tail', 'cov', 'both'); KS = (1, 2, 3, 0)
DEV = [f'seed{s}_load{h}' for s in (901, 902, 903, 904) for h in (8, 16)]


def q(path, rule=None):
    r = {x['episode']: x for x in json.loads(Path(path).read_text()) if rule is None or x.get('rule') == rule}
    return np.array([r[e]['queue_sum'] for e in DEV]), r


def main():
    L = ['arm | K | mean gain vs Z | seeds >= 0 | min seed | vs plain relay | fallback share']
    out = {}
    for K in KS:
        Z = {s: q(M / f'e3_dev_Z_20261001/Z_s{s}/rows.json', 'none')[0] for s in range(10)}
        R = {s: q(M / f'e3_negflip_20261001/s{s}_K{K}/rows.json')[0] for s in range(10)}
        g0 = [-(R[s].sum() / Z[s].sum() - 1) * 100 for s in range(10)]
        L.append(f'plain | {K if K else "iid"} | {np.mean(g0):+.2f} | {sum(x >= 0 for x in g0)}/10 | {min(g0):+.2f} | - | 0')
        for a in ARMS:
            G = []; V = []; F = []
            for s in range(10):
                d = P / f'{a}_s{s}_K{K}'
                if not (d / 'manifest.json').exists():
                    print('INCOMPLETE', d.name); return
                x, rr = q(d / 'rows.json'); G.append(-(x.sum() / Z[s].sum() - 1) * 100); V.append(-(x.sum() / R[s].sum() - 1) * 100)
                F.append(sum(r['fallback_decisions'] for r in rr.values()) / (len(DEV) * 26 * 9))
            out[f'{a}_K{K}'] = dict(gain_vs_Z=G, vs_relay=V, fallback=F)
            L.append(f'{a} | {K if K else "iid"} | {np.mean(G):+.2f} | {sum(x >= 0 for x in G)}/10 | {min(G):+.2f} | {np.mean(V):+.2f} | {np.mean(F):.3f}')
    text = '\n'.join(L); print(text)
    (M / 'e3_gate_dev_report_20261001.json').write_text(json.dumps(out, indent=1))
    (M / 'e3_gate_dev_report_20261001.txt').write_text('EXPLORATORY (development panel; arms designed on it)\n' + text + '\n')


if __name__ == '__main__':
    main()
