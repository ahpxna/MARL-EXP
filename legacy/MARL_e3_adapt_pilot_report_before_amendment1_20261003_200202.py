#!/usr/bin/env python3
"""Report of PROTOCOL_E3_ADAPT_PILOT_20261003.md (protocol 19:0x EDT 03/10; report written before any pilot run).
Per arm x seed x budget: gain vs Z on the NEW (iid) and OLD (K1) channel, on DEV (traffic 5717-5748) and SELECT (5701-5716);
old-channel drop from the parent; BCWI alpha chosen on SELECT (max new gain with SELECT old drop <= eps); primary PAIRED - FTMIX
at B = 40 on DEV; the go / no-go rule of §6.  Training costs from the trainers' manifests and logs.  --smoke: traffic 9001-9002."""
import argparse, json
from pathlib import Path
import numpy as np

BASE = Path('research/marl_budget/e3_adapt_pilot_20261003'); EPS = 0.5
ARMS = ['FTNEW', 'FTMIX', 'PCT', 'PAIRED', 'A0', 'A1', 'A2']; AL = ['0.25', '0.5', '0.75']


def main(a):
    E = BASE / ('smoke_pipe' if a.smoke else '')
    if a.smoke:
        seeds, buds, sel, dev = [0], [8, 16], [9001], [9002]
    else:
        seeds, buds, sel, dev = [0, 1], [8, 16, 40, 80], list(range(5701, 5717)), list(range(5717, 5749))
    blocks = {'SELECT': sel, 'DEV': dev}

    def rows(d, arm):
        if not (d / 'manifest.json').exists():
            return None
        m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
        return {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['arm'] == arm}

    def gain(q, z, block):
        eps = [f'seed{t}_load{h}' for t in blocks[block] for h in (8, 16)]
        return -(sum(q[e] for e in eps) / sum(z[e] for e in eps) - 1) * 100
    G = {}; out = []
    for s in seeds:
        z = rows(E / f'Z_s{s}', 'Z')
        if z is None:
            continue
        for K in (0, 1):
            p = rows(E / f'E_PARENT_s{s}_B0_K{K}', 'PLAIN')
            if p is not None:
                for blk in blocks:
                    G[('PARENT', s, 0, K, blk)] = gain(p, z, blk)
            for b in buds:
                for arm in ARMS + [f'BCWI{x}' for x in AL]:
                    q = rows(E / f'E_{arm}_s{s}_B{b}_K{K}', 'PLAIN')
                    if q is not None:
                        for blk in blocks:
                            G[(arm, s, b, K, blk)] = gain(q, z, blk)
    S = [s for s in seeds if all(('PARENT', s, 0, K, 'DEV') in G for K in (0, 1))]
    out.append(f'== adaptation pilot (screening; 2 seeds): complete parent evaluations for seeds {S}')
    # BCWI: alpha per (seed, budget) on SELECT
    for s in S:
        for b in buds:
            cand = [x for x in AL if all((f'BCWI{x}', s, b, K, 'SELECT') in G for K in (0, 1))]
            feas = [x for x in cand if G[('PARENT', s, 0, 1, 'SELECT')] - G[(f'BCWI{x}', s, b, 1, 'SELECT')] <= EPS]
            if cand:
                best = max(feas or cand, key=lambda x: G[(f'BCWI{x}', s, b, 0, 'SELECT')])
                for K in (0, 1):
                    G[('BCWI', s, b, K, 'DEV')] = G[(f'BCWI{best}', s, b, K, 'DEV')]
                G[('BCWI_alpha', s, b)] = (best, bool(feas))
    show = ARMS + ['BCWI']
    for s in S:
        out.append(f'-- seed {s}: DEV gain vs Z, NEW channel (iid) | OLD channel (K1) drop from the parent (parent: new '
                   f"{G[('PARENT', s, 0, 0, 'DEV')]:+.2f}, old {G[('PARENT', s, 0, 1, 'DEV')]:+.2f})")
        out.append('arm | ' + ' | '.join(f'B={b}' for b in buds))
        for arm in show:
            cells = []
            for b in buds:
                if (arm, s, b, 0, 'DEV') in G and (arm, s, b, 1, 'DEV') in G:
                    drop = G[('PARENT', s, 0, 1, 'DEV')] - G[(arm, s, b, 1, 'DEV')]
                    cells.append(f"{G[(arm, s, b, 0, 'DEV')]:+.2f} / drop {drop:+.2f}")
                else:
                    cells.append('—')
            extra = f" (alpha {[G.get(('BCWI_alpha', s, b)) for b in buds]})" if arm == 'BCWI' else ''
            out.append(f'{arm} | ' + ' | '.join(cells) + extra)
    # costs
    for s in S:
        for arm in ARMS:
            f = E / f'T_{arm}_s{s}' / 'manifest.json'
            if f.exists():
                m = json.loads(f.read_text()); lg = [json.loads(l) for l in open(E / f'T_{arm}_s{s}' / 'log.jsonl')]
                hr = [r['h_rate'] for r in lg if r.get('h_rate') is not None]
                out.append(f"cost {arm} s{s}: simulated episodes {m['budget_used']}, teacher queries (decision steps) {m['teacher_queries']}, "
                           f"{m['seconds']:.0f} s" + (f", h-rate mean {np.mean(hr):.3f}" if hr else ''))
    # primary and go / no-go
    bp = 40 if 40 in buds else buds[-1]
    ok = [s for s in S if all((x, s, bp, K, 'DEV') in G for x in ('PAIRED', 'FTMIX', 'A0') for K in (0, 1))]
    if ok:
        d = {s: G[('PAIRED', s, bp, 0, 'DEV')] - G[('FTMIX', s, bp, 0, 'DEV')] for s in ok}
        drop = {s: G[('PARENT', s, 0, 1, 'DEV')] - G[('PAIRED', s, bp, 1, 'DEV')] for s in ok}
        d0 = {s: G[('PAIRED', s, bp, 0, 'DEV')] - G[('A0', s, bp, 0, 'DEV')] for s in ok}
        c1 = all(v > 1.0 for v in d.values()); c2 = all(v <= EPS for v in drop.values()); c3 = all(v > 0 for v in d0.values())
        out.append(f'-- primary (B = {bp}, DEV): PAIRED - FTMIX new-channel gain per seed {({s: round(v, 2) for s, v in d.items()})}')
        out.append(f'   (1) > +1.0 on every seed: {c1}; (2) PAIRED old drop <= {EPS}: {({s: round(v, 2) for s, v in drop.items()})} -> {c2}; '
                   f'(3) PAIRED - A0 > 0: {({s: round(v, 2) for s, v in d0.items()})} -> {c3}')
        out.append(f"   verdict: {'GO (open the confirmatory panel)' if c1 and c2 and c3 else 'NO-GO (report where PAIRED loses)'}")
        best_small = {s: max(ARMS + ['BCWI'], key=lambda x: G.get((x, s, bp, 0, 'DEV'), -1e9)) for s in ok}
        out.append(f'   best arm at B = {bp} per seed (new channel): {best_small}')
    d_ = E; (d_ / 'report.txt').write_text('\n'.join(out) + '\n')
    (d_ / 'report.json').write_text(json.dumps({'|'.join(map(str, k)): v for k, v in G.items()}, indent=1, default=str)); print('\n'.join(out))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
