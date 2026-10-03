#!/usr/bin/env python3
"""Report of PROTOCOL_E3_ARCH_CONTROL_20261001.md (written before the runs).  Per architecture (attention, shared-concat,
mean pool) and capacity (const1, const2, iid): gain vs Z per seed and mean; AC1 / AC2 per alternative architecture; AC3 paired."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_arch_control_20261001'; SEEDS = (0, 1, 2)
EPS = [f'seed{s}_load{h}' for s in range(3601, 3665) for h in (8, 16)]
ARCH = {'relayAttnCage_st': 'attention', 'relaySCCage_st': 'shared-concat', 'relay6Cage_st': 'mean pool'}


def load(tag, rule):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
    rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['rule'] == rule}
    assert sorted(rows) == sorted(EPS), f'{tag}: {len(rows)} episodes'
    return np.array([rows[e] for e in EPS], float)


def main():
    Z = {s: load(f'Z_s{s}', 'none') for s in SEEDS}
    L = ['architecture | capacity | gain vs Z per seed | mean']; out = {}
    for a, name in ARCH.items():
        for c in ('const1', 'const2', 'iid'):
            g = []
            for s in SEEDS:
                X = load(f'R_{a}_s{s}_{c}', 'prefix')
                g.append(None if X is None or Z[s] is None else float(-(X.sum() / Z[s].sum() - 1) * 100))
            out[(a, c)] = g
            ok = [x for x in g if x is not None]
            L.append(f'{name} | {c} | ' + ' '.join('  -  ' if x is None else f'{x:+.2f}' for x in g) + (f' | {np.mean(ok):+.2f} %' if ok else ' | -'))
    for a in ('relayAttnCage_st', 'relaySCCage_st'):
        k1 = [x for x in out[(a, 'const1')] if x is not None]; ii = [x for x in out[(a, 'iid')] if x is not None]
        if len(k1) < 3 or len(ii) < 3:
            L.append(f'{ARCH[a]}: INCOMPLETE'); continue
        AC1 = np.mean(k1) < 0 and np.mean(ii) > 0 and sum(x < 0 for x in k1) >= 2
        AC2 = np.mean(k1) > 0 and sum(x > 0 for x in k1) >= 2
        mp = out[('relay6Cage_st', 'const1')]
        L.append(f'{ARCH[a]}: AC1 generic {"SUPPORTED" if AC1 else "NOT SUPPORTED"} | AC2 specific {"SUPPORTED" if AC2 else "NOT SUPPORTED"} | '
                 f'AC3 vs mean pool at K = 1: ' + ' '.join(f'{x - y:+.2f}' for x, y in zip(out[(a, "const1")], mp) if x is not None and y is not None))
    text = '\n'.join(L); print(text)
    (M / 'e3_arch_control_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
