#!/usr/bin/env python3
"""Report for MARL_e3_truncation_closed_loop.py (direction (b), legal rules).  Read-only on COMPLETE run dirs.

Per actor and rule: bytes saved against the prefix (1 - sum bytes / sum prefix bytes, bid bytes included), the paired
waiting change (per-episode waiting / prefix waiting - 1; mean and 95% bootstrap CI over episodes, 2000 resamples), the
share of episodes with IDENTICAL waiting.  Same-byte comparison: the blind-truncation curve (prefix = 0 saved, then the
blind fractions) is interpolated linearly in bytes saved; each non-blind rule is reported as (its waiting change) minus
(the blind curve's at the same saving), with a paired bootstrap over episodes using the per-episode blind values
interpolated at the rule's pooled saving.  The blind family is every blind_<f> and cap_<c> rule; a rule is DOMINATED if a
blind rule saves at least as many bytes with a mean waiting change no larger.  Proxy: share of steps whose proxy L is exactly safe for the current step, its
L against the exact smallest safe L.  Pooled over actors by family (scratch / bc / mix).
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np


def boot(x, n=2000, seed=0):
    x = np.asarray(x, float); r = np.random.default_rng(seed); m = [x[r.integers(0, len(x), len(x))].mean() for _ in range(n)]
    return float(x.mean()), float(np.quantile(m, 0.025)), float(np.quantile(m, 0.975))


def main(a):
    root = Path(a.root); out = {}; lines = []; fam = defaultdict(lambda: defaultdict(list))
    for d in sorted(p for p in root.iterdir() if p.is_dir()):
        if not (d / 'manifest.json').exists():
            lines.append(f'{d.name}: not complete, skipped'); continue
        R = json.loads((d / 'rows.json').read_text()); rules = json.loads((d / 'manifest.json').read_text())['rules']
        by = {(r['episode'], r['rule']): r for r in R}; eps = sorted({r['episode'] for r in R})
        base = {e: by[(e, 'prefix')] for e in eps}
        per = {}
        for rule in rules:
            wc = np.array([by[(e, rule)]['queue_sum'] / base[e]['queue_sum'] - 1 for e in eps])
            sv = 1 - sum(by[(e, rule)]['bytes'] for e in eps) / sum(base[e]['bytes'] for e in eps)
            per[rule] = dict(saved=sv, wc=wc, ident=float(np.mean([by[(e, rule)]['queue_sum'] == base[e]['queue_sum'] for e in eps])))
        blind = sorted([r for r in rules if r.startswith(('blind_', 'cap_'))], key=lambda r: per[r]['saved'])
        xs = [0.0] + [per[r]['saved'] for r in blind]; W = np.stack([np.zeros(len(eps))] + [per[r]['wc'] for r in blind])      # (points, episodes)
        res = {}
        lines.append(f'== {d.name}: {len(eps)} episodes, prefix {np.mean([base[e]["bytes"] for e in eps]) / 26:.0f} B/step')
        for rule in rules:
            v = per[rule]; b = boot(v['wc']); row = dict(bytes_saved=v['saved'], waiting_change=b, identical_share=v['ident'])
            txt = f'  {rule:10s} saved {v["saved"]:6.3f} | waiting {b[0]:+.4f} [{b[1]:+.4f}, {b[2]:+.4f}] | identical {v["ident"]:.2f}'
            if not rule.startswith(('blind_', 'cap_')) and rule != 'prefix':
                dom = [r for r in blind if per[r]['saved'] >= v['saved'] and per[r]['wc'].mean() <= v['wc'].mean()]
                row['dominated_by_blind'] = dom
                if dom:
                    txt += f' | DOMINATED by {",".join(dom)}'
            if not rule.startswith(('blind_', 'cap_')) and rule != 'prefix' and xs[0] <= v['saved'] <= xs[-1]:
                wb = np.array([np.interp(v['saved'], xs, W[:, k]) for k in range(len(eps))]); dlt = boot(v['wc'] - wb)
                row['vs_blind_same_bytes'] = dlt; txt += f' | minus blind at same bytes {dlt[0]:+.4f} [{dlt[1]:+.4f}, {dlt[2]:+.4f}]'
            if rule == 'proxy':
                C = [c for e in eps for c in by[(e, 'proxy')]['checks']]
                if C:
                    row['proxy'] = dict(safe_share=float(np.mean([c['safe'] for c in C])), L=float(np.mean([c['L'] for c in C])),
                                        L_exact=float(np.mean([c['L_exact'] for c in C])), L0=float(np.mean([c['L0'] for c in C])),
                                        too_short=float(np.mean([c['L'] < c['L_exact'] for c in C])))
                    p_ = row['proxy']; txt += f' | current-step exact-safe {p_["safe_share"]:.2f}, L {p_["L"]:.2f} vs exact {p_["L_exact"]:.2f} of L0 {p_["L0"]:.2f}'
            res[rule] = row; lines.append(txt)
            f = 'bc' if d.name.startswith('bc') else ('mix' if d.name.startswith('mix') else 'scratch')
            fam[f][rule].append((v['saved'], b[0], row.get('vs_blind_same_bytes', (np.nan,))[0]))
        out[d.name] = res
    lines.append('== pooled by family (mean over actors: saved, waiting change, minus blind at same bytes)')
    for f, rr in fam.items():
        for rule, vals in rr.items():
            v = np.array(vals, float); lines.append(f'  {f:8s} {rule:10s} n={len(v)} saved {np.nanmean(v[:, 0]):6.3f} waiting {np.nanmean(v[:, 1]):+.4f} vs blind {np.nanmean(v[:, 2]):+.4f}')
    Path(a.out + '.json').write_text(json.dumps(out, indent=1)); Path(a.out + '.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--root', default='research/marl_budget/e3_truncation_cl_20260929'); p.add_argument('--out', default='research/marl_budget/e3_truncation_cl_report_20260929')
    main(p.parse_args())
