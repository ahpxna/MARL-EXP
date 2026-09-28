#!/usr/bin/env python3
"""E3 performance-bytes FRONTIER over several total caps (readiness audit P3: >= 3 budget points, same design).

Input: closed-loop v2 run dirs (one per cap) of the SAME actor, the same selectors and the same episodes.
Per method (selector init seeds averaged per episode): paired relative change of sum-of-waiting against
the same episode's prefix, 95% bootstrap CI over episodes, and absolute charged bytes per decision step.
Self-checks (refuse to plot): identical prefix rows across caps (the prefix does not depend on the cap),
equal episode sets, zero oracle access by any deployable row.  Writes <stem>.png/.pdf/.json.
"""
from __future__ import annotations
import argparse, hashlib, json
from collections import defaultdict
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

N_DEC = 26


def boot(v, B=10000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v, float)
    return [float(x) for x in np.quantile([v[rng.integers(0, len(v), len(v))].mean() for _ in range(B)], [0.025, 0.975])]


def main(a):
    pts = defaultdict(list); ref = None; sha = {}
    for d in a.runs:
        raw = (Path(d) / 'rows.json').read_bytes(); rows = json.loads(raw); sha[d] = hashlib.sha256(raw).hexdigest()
        cap = {r['cap'] for r in rows}; assert len(cap) == 1, d; cap = cap.pop()
        per = defaultdict(lambda: defaultdict(list))
        for r in rows:
            if not r['method'].startswith('oracle') and r['summary'].get('oracle_access_used'):
                raise SystemExit(f'SELF-CHECK FAIL: oracle access in {d}')
            per[r['method'].split('/')[0]][r['episode']].append(r)
        pq = {e: v[0]['queue_sum'] for e, v in per['prefix'].items()}
        if ref is None:
            ref = pq
        elif pq != ref:
            raise SystemExit(f'SELF-CHECK FAIL: prefix rows differ across caps ({d})')
        eps = sorted(pq)
        for m, dd in per.items():
            if m == 'prefix':
                continue
            if sorted(dd) != eps:
                raise SystemExit(f'SELF-CHECK FAIL: {m} misses episodes in {d}')
            rel = [100 * (np.mean([r['queue_sum'] for r in dd[e]]) - pq[e]) / pq[e] for e in eps]
            by = float(np.mean([np.mean([r['bytes'] for r in dd[e]]) for e in eps]) / N_DEC)
            pts[m].append(dict(cap=cap, bytes_per_step=by, rel=float(np.mean(rel)), ci=boot(rel), n=len(eps)))
    pb = float(np.mean([v for v in ref.values()]))
    fig, ax = plt.subplots(figsize=(7.5, 4.2))
    for m, P in sorted(pts.items()):
        P = sorted(P, key=lambda x: x['cap']); x = [p['bytes_per_step'] for p in P]; y = [p['rel'] for p in P]
        ax.errorbar(x, y, yerr=[[p['rel'] - p['ci'][0] for p in P], [p['ci'][1] - p['rel'] for p in P]], fmt='-o', capsize=3, label=m)
        for p in P:
            ax.annotate(f'+{p["cap"]}', (p['bytes_per_step'], p['rel']), fontsize=7, xytext=(3, 3), textcoords='offset points')
    ax.axhline(0, color='gray', lw=0.8)
    ax.set_xlabel('total charged bytes per decision step'); ax.set_ylabel('Σ waiting vs prefix, same episode (%)\nlower is better')
    ax.set_title(a.title, fontsize=9); ax.legend(fontsize=8, loc='upper left', bbox_to_anchor=(1.02, 1), frameon=False)
    od = Path(a.out); od.mkdir(parents=True, exist_ok=True)
    fig.savefig(od / f'{a.stem}.png', dpi=200, bbox_inches='tight'); fig.savefig(od / f'{a.stem}.pdf', bbox_inches='tight'); plt.close(fig)
    (od / f'{a.stem}.json').write_text(json.dumps(dict(runs=sha, points=pts), indent=1))
    for m, P in sorted(pts.items()):
        for p in sorted(P, key=lambda x: x['cap']):
            print(f'{m:12s} cap +{p["cap"]:3d}: bytes/step {p["bytes_per_step"]:6.1f}  Σwait {p["rel"]:+6.2f}% [{p["ci"][0]:+.2f}, {p["ci"][1]:+.2f}]')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--runs', nargs='+', required=True); p.add_argument('--out', required=True)
    p.add_argument('--stem', required=True); p.add_argument('--title', default='E3 performance-bytes frontier')
    main(p.parse_args())
