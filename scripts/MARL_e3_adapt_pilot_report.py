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
    # Amendment 1 (20:0x, before any pilot result was read): completeness first; no verdict on a partial pilot.
    need = [('PARENT', s, 0, K, blk) for s in seeds for K in (0, 1) for blk in blocks] + \
           [(x, s, b, K, blk) for s in seeds for b in buds for x in ARMS + [f'BCWI{al}' for al in AL] for K in (0, 1) for blk in blocks]
    miss = [k for k in need if k not in G]
    out.append(f'== adaptation pilot (screening; seeds {seeds}): {len(need) - len(miss)} / {len(need)} required evaluations present')
    if miss:
        out.append(f'INCOMPLETE: e.g. {miss[:6]}; no verdict'); E.joinpath('report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    S = seeds
    # BCWI (Amendment 1): alpha in {0 (= parent), 0.25, 0.5, 0.75, 1 (= FT-mix at the same budget)}; feasible = SELECT old drop <= eps;
    # alpha = 0 is always feasible, so a violating alpha is never chosen.
    def bcwi(al, s, b, K, blk):
        return G[('PARENT', s, 0, K, blk)] if al == '0' else (G[('FTMIX', s, b, K, blk)] if al == '1' else G[(f'BCWI{al}', s, b, K, blk)])
    for s in S:
        for b in buds:
            cand = ['0'] + AL + ['1']
            feas = [x for x in cand if G[('PARENT', s, 0, 1, 'SELECT')] - bcwi(x, s, b, 1, 'SELECT') <= EPS]
            best = max(feas, key=lambda x: bcwi(x, s, b, 0, 'SELECT'))
            for K in (0, 1):
                G[('BCWI', s, b, K, 'DEV')] = bcwi(best, s, b, K, 'DEV')
            G[('BCWI_alpha', s, b)] = best
    show = ARMS + ['BCWI']
    for s in S:
        out.append(f'-- seed {s}: DEV gain vs Z, NEW channel (iid) / OLD channel (K1) drop from the parent (parent: new '
                   f"{G[('PARENT', s, 0, 0, 'DEV')]:+.2f}, old {G[('PARENT', s, 0, 1, 'DEV')]:+.2f})")
        out.append('arm | ' + ' | '.join(f'B={b}' for b in buds))
        for arm in show:
            cells = [f"{G[(arm, s, b, 0, 'DEV')]:+.2f} / drop {G[('PARENT', s, 0, 1, 'DEV')] - G[(arm, s, b, 1, 'DEV')]:+.2f}" for b in buds]
            extra = f" (alpha {[G[('BCWI_alpha', s, b)] for b in buds]})" if arm == 'BCWI' else ''
            out.append(f'{arm} | ' + ' | '.join(cells) + extra)
    for s in S:
        for arm in ARMS:
            f = E / f'T_{arm}_s{s}' / 'manifest.json'
            m = json.loads(f.read_text()); lg = [json.loads(l) for l in open(E / f'T_{arm}_s{s}' / 'log.jsonl')]
            hr = [r['h_rate'] for r in lg if r.get('h_rate') is not None]
            out.append(f"cost {arm} s{s}: simulated episodes {m['budget_used']}, teacher queries (decision steps) {m['teacher_queries']}, "
                       f"{m['seconds']:.0f} s" + (f", h-rate mean {np.mean(hr):.3f}" if hr else ''))
    # contrasts (new channel, DEV), per seed; component reading per Amendment 1
    nd = lambda x, y, s, b: G[(x, s, b, 0, 'DEV')] - G[(y, s, b, 0, 'DEV')]
    CON = [('PAIRED', 'FTMIX', 'primary'), ('PAIRED', 'A0', 'weighting + preservation'), ('PAIRED', 'A2', 'weighting (h), given preservation'),
           ('PAIRED', 'A1', 'preservation, given weighting'), ('A0', 'FTMIX', 'pairing alone'), ('PAIRED', 'PCT', 'vs PCT-style'),
           ('PAIRED', 'BCWI', 'vs BCWI'), ('FTNEW', 'FTMIX', 'old replay')]
    for b in buds:
        out.append(f'-- contrasts at B = {b} (new-channel gain difference per seed, DEV): ' +
                   '; '.join(f"{x}-{y} [{lab}] {[round(nd(x, y, s, b), 2) for s in S]}" for x, y, lab in CON))
    bp = 40 if 40 in buds else buds[-1]
    d = {s: nd('PAIRED', 'FTMIX', s, bp) for s in S}; drop = {s: G[('PARENT', s, 0, 1, 'DEV')] - G[('PAIRED', s, bp, 1, 'DEV')] for s in S}
    c1 = all(v > 1.0 for v in d.values()); c2 = all(v <= EPS for v in drop.values()); c3 = all(nd('PAIRED', 'A0', s, bp) > 0 for s in S)
    c4 = all(nd('PAIRED', 'A2', s, bp) > 0 for s in S); c5 = all(nd('PAIRED', 'PCT', s, bp) > 0 and nd('PAIRED', 'BCWI', s, bp) > 0 for s in S)
    out.append(f'-- primary (B = {bp}, DEV): PAIRED - FTMIX per seed {({s: round(v, 2) for s, v in d.items()})}; PAIRED old drop {({s: round(v, 2) for s, v in drop.items()})}')
    out.append(f'   registered GO = (1) > +1.0 every seed {c1} & (2) old drop <= {EPS} {c2} & (3) PAIRED > A0 {c3} -> {c1 and c2 and c3}')
    out.append(f'   Amendment 1 GO additionally needs (4) PAIRED > A2 on every seed {c4} & (5) PAIRED > PCT and > BCWI on every seed {c5} -> '
               f"{'GO (open the confirmatory panel)' if c1 and c2 and c3 and c4 and c5 else 'NO-GO (report where PAIRED loses)'}")
    out.append(f"   caveat: the loss normalises CE over old and new samples together, so gamma > 0 also raises the new channel's share of the weight; "
               f"PAIRED - A2 confounds regression targeting with that shift (control arm: uniform new-channel up-weighting, confirmation stage)")
    out.append(f"   best arm at B = {bp} per seed (new channel): {({s: max(show, key=lambda x: G[(x, s, bp, 0, 'DEV')]) for s in S})}")
    d_ = E; (d_ / 'report.txt').write_text('\n'.join(out) + '\n')
    (d_ / 'report.json').write_text(json.dumps({'|'.join(map(str, k)): v for k, v in G.items()}, indent=1, default=str)); print('\n'.join(out))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
