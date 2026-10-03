#!/usr/bin/env python3
"""Report of PROTOCOL_E3_SWITCH_20261002.md (written 15:14:00 EDT, before any run).  3x3, panel 4401-4464, seeds 0-4.
SW1 relayMIX >= both specialists on k1_iid, iid_k1, alt4; SW2 relayMIX switching gain >= mean(own k1, own iid) - 0.5;
SW3 (reported) each specialist's switching gain between its two pure-regime gains."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_switch_20261002'; SEEDS = list(range(5))
EPS = [f'seed{s}_load{h}' for s in range(4401, 4465) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
ARMS = ('relayMIX_st', 'relayCK1_st', 'relay6Cage_st'); SCH = ('k1', 'iid', 'k1_iid', 'iid_k1', 'alt4')


def load(tag, rule, ckpt_name):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
    assert f'{ckpt_name}/ckpt_best.pt' in str(m.get('args')), tag
    rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['rule'] == rule}
    assert sorted(rows) == sorted(EPS), f'{tag}: {len(rows)} episodes'
    return np.array([rows[e] for e in EPS], float)


def gain(x, y, ii=None):
    return -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100


def boot(X, Y):
    rng = np.random.default_rng(0); bs = []
    for _ in range(4000):
        ss = rng.choice(SEEDS, len(SEEDS))
        bs.append(np.mean([gain(X[s], Y[s], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
    return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]


def main():
    Z = {s: load(f'Z_s{s}', 'none', f'distill_none_s{s}') for s in SEEDS}
    R = {(a, s, c): load(f'R_{a}_s{s}_{c}', 'prefix', f'{a}_s{s}') for a in ARMS for s in SEEDS for c in SCH}
    allv = list(Z.values()) + list(R.values())
    if any(v is None for v in allv):
        print(f'INCOMPLETE: {sum(v is None for v in allv)} of {len(allv)} items missing'); return
    G = {(a, c): float(np.mean([gain(R[(a, s, c)], Z[s]) for s in SEEDS])) for a in ARMS for c in SCH}
    L = ['arm | ' + ' | '.join(SCH)]
    for a in ARMS:
        L.append(f'{a} | ' + ' | '.join(f'{G[(a, c)]:+.2f} {boot({s: R[(a, s, c)] for s in SEEDS}, Z)}' for c in SCH))
    sw = ('k1_iid', 'iid_k1', 'alt4')
    SW1 = all(G[('relayMIX_st', c)] >= max(G[('relayCK1_st', c)], G[('relay6Cage_st', c)]) for c in sw)
    ref = (G[('relayMIX_st', 'k1')] + G[('relayMIX_st', 'iid')]) / 2; SW2 = all(G[('relayMIX_st', c)] >= ref - 0.5 for c in sw)
    SW3 = {a: all(min(G[(a, 'k1')], G[(a, 'iid')]) <= G[(a, c)] <= max(G[(a, 'k1')], G[(a, 'iid')]) for c in sw) for a in ('relayCK1_st', 'relay6Cage_st')}
    L += [f'SW1 relayMIX >= both specialists on every switching schedule -> {"SUPPORTED" if SW1 else "NOT SUPPORTED"} (' + ', '.join(f'{c}: MIX {G[("relayMIX_st", c)]:+.2f} CK1 {G[("relayCK1_st", c)]:+.2f} 6Cage {G[("relay6Cage_st", c)]:+.2f}' for c in sw) + ')',
          f'SW2 relayMIX switching >= mean(own k1, iid) {ref:+.2f} - 0.5 -> {"SUPPORTED" if SW2 else "NOT SUPPORTED"}',
          f'SW3 (reported) specialists between their pure-regime gains: {SW3}']
    text = '\n'.join(L); print(text); (M / 'e3_switch_report_20261002.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
