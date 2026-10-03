#!/usr/bin/env python3
"""Report of PROTOCOL_E3_NYC16X3_20261002.md (written 02/10/2026 22:5x EDT, before any NYC panel run).
N1 relayCage_st at iid beats Z (lower > 0); N2 rule A count form (sign(net_rel/47 - theta), tau_train from ruleA_s*.json, pooled;
cells whose interval covers 0 are not scored); N3 relayCK1 - relayCage at K1 lower > 0; N4 relayCK1 iid - K1 upper < 0;
N5 FB1 and FB3 from the fallback verdict file.  Gain and bootstrap as scripts/MARL_e3_mixq_report.py.
Usage: MARL_e3_nyc_report.py [--root G] [--fb F] [--seeds 0 1 2 3 4] [--panel-lo 5001 --n-panel 64] [--smoke]"""
import argparse, json
from pathlib import Path
import numpy as np

NAME = {1: 'K=1', 2: 'K=2', 3: 'K=3', 0: 'iid'}; THETA = -0.08; M1 = 47


def main(a):
    G = Path(a.root); E = G / 'eval'; seeds = a.seeds; panel = list(range(a.panel_lo, a.panel_lo + a.n_panel))
    EPS = [f'seed{s}_load{h}' for s in panel for h in (8, 16)]; TS = [f'seed{s}' for s in panel]
    IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}

    def load(tag, rule, ck):
        d = E / tag; m = json.loads((d / 'manifest.json').read_text())
        assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
        assert f'{ck}/ckpt_best.pt' in str(m.get('args')), tag
        rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['rule'] == rule}
        assert set(EPS) <= set(rows), (tag, len(rows))
        return np.array([rows[e] for e in EPS], float)
    gain = lambda x, y, ii=None: -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100

    def boot(f):
        rng = np.random.default_rng(0); bs = []
        for _ in range(4000 if not a.smoke else 200):
            ss = rng.choice(seeds, len(seeds)); ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
            bs.append(np.mean([f(s, ii) for s in ss]))
        return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]
    Z = {s: load(f'Z_s{s}', 'none', f'distill_none_s{s}') for s in seeds}
    R = {(r, s, K): load(f'R_{r}_s{s}_K{K}', 'prefix', f'{r}_s{s}') for r in ('relayCage_st', 'relayCK1_st') for s in seeds for K in (1, 2, 3, 0)}
    G_ = {}; CI = {}
    for r in ('relayCage_st', 'relayCK1_st'):
        for K in (1, 2, 3, 0):
            G_[(r, K)] = float(np.mean([gain(R[(r, s, K)], Z[s]) for s in seeds]))
            CI[(r, K)] = boot(lambda s, ii, r=r, K=K: gain(R[(r, s, K)], Z[s], ii))
    L = [f'NYC 16x3: gain vs Z (95 %), seeds {seeds}, panel {panel[0]}-{panel[-1]}']
    L += [f'{r} | ' + ' | '.join(f'{NAME[K]} {G_[(r, K)]:+.2f} {CI[(r, K)]}' for K in (1, 2, 3, 0)) for r in ('relayCage_st', 'relayCK1_st')]
    n1 = CI[('relayCage_st', 0)][0] > 0
    # N2: tau pooled from the per-seed ruleA files (each written before that seed's panel runs)
    ra = [json.loads((G / f'ruleA_s{s}.json').read_text()) for s in seeds]; h = np.sum([x['age_hist'] for x in ra], axis=0)
    c = np.cumsum(h); tau = int(np.searchsorted(c, 0.99 * c[-1])); kmin = (1 + THETA) * M1 / (tau + 2)
    n2_cells = []; n2 = True
    for K in (1, 2, 3):
        hs = []; dec = 0
        for s in seeds:
            d = Path(a.fb) / f'FB_relayCage_st_s{s}_K{K}'
            for row in json.loads((d / 'rows.json').read_text()):
                if row['system'] == 'RELAY' and row['episode'] in EPS:
                    hs.append(row['age_hist']); dec += row['decisions']
        hs = np.sum(hs, axis=0); net = (hs[0] - hs[tau + 1:15].sum() - hs[15]) / dec / M1
        pred = net > THETA; lo, hi = CI[('relayCage_st', K)]; obs = None if lo <= 0 <= hi else (G_[('relayCage_st', K)] > 0)
        if obs is not None and obs != pred:
            n2 = False
        n2_cells.append(f'K{K}: net_rel/47 {net:+.3f} -> predicted {"+" if pred else "-"}, observed {G_[("relayCage_st", K)]:+.2f} {[lo, hi]} ' +
                        ('(no sign, not scored)' if obs is None else ('ok' if obs == pred else 'WRONG')))
    scored = sum('not scored' not in x for x in n2_cells)
    d3 = boot(lambda s, ii: gain(R[('relayCK1_st', s, 1)], Z[s], ii) - gain(R[('relayCage_st', s, 1)], Z[s], ii))
    n3 = d3[0] > 0; m3 = G_[('relayCK1_st', 1)] - G_[('relayCage_st', 1)]
    d4 = boot(lambda s, ii: gain(R[('relayCK1_st', s, 0)], Z[s], ii) - gain(R[('relayCK1_st', s, 1)], Z[s], ii))
    n4 = d4[1] < 0; m4 = G_[('relayCK1_st', 0)] - G_[('relayCK1_st', 1)]
    vf = Path(a.fb).parent / 'verdict_nyc.json'
    fb = json.loads(vf.read_text()).get('nyc') if vf.exists() else None
    n5 = None if fb is None else (fb.get('FB1') is not False and fb.get('FB3') is not False and (fb.get('FB1') or fb.get('FB3')) is not None)
    sv = lambda v: 'not tested' if v is None else ('SUPPORTED' if v else 'NOT SUPPORTED')
    L += [f'N1 relay beats Z at iid (relayCage_st, lower > 0): {G_[("relayCage_st", 0)]:+.2f} {CI[("relayCage_st", 0)]} -> {sv(n1)}',
          f'N2 rule A count form (tau_train p99 {tau}, closed-form K_min {kmin:.2f}; {scored} scored cells): ' + '; '.join(n2_cells) + f' -> {sv(n2 if scored else None)}',
          f'N3 train-match rescue at K1 (relayCK1 - relayCage): {m3:+.2f} {d3} -> {sv(n3)}',
          f'N4 upgrade hazard (relayCK1 iid - K1): {m4:+.2f} {d4} -> {sv(n4)}',
          f'N5 fallback transfers (FB1 and FB3 on NYC): {fb and {k: fb.get(k) for k in ("FB1", "FB3")}} -> {sv(n5)}']
    txt = '\n'.join(L); print(txt)
    if not a.smoke:
        (G / 'report.txt').write_text(txt + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--root', default='research/marl_budget/e3_nyc16x3_20261002')
    p.add_argument('--fb', default='research/marl_budget/e3_fallback_20261002/nyc'); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2, 3, 4])
    p.add_argument('--panel-lo', type=int, default=5001); p.add_argument('--n-panel', type=int, default=64); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
