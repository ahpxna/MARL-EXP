#!/usr/bin/env python3
"""The declared choice of the staleness bound s* (PROTOCOL_E3_TRUNCATION_DRAFT_20260929.md §3), applied to the v3
development runs (read-only).  Per family (scratch / bc / mix), for every s in the grid: pooled bytes saved (mean over
actors of 1 - sum bytes / sum prefix bytes) and the pooled waiting change with a TWO-LEVEL bootstrap (actors, then
traffic seeds with both headways kept together; 4000 resamples, seed 0); s* = the largest pooled saving whose upper
95 % bound is below +1.0 %.  With one actor (mix) the first level is degenerate.
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np


def main(a):
    root = Path(a.root); fam = defaultdict(dict)
    for d in sorted(p for p in root.iterdir() if p.is_dir() and (p / 'manifest.json').exists()):
        R = json.loads((d / 'rows.json').read_text()); by = {(r['episode'], r['rule']): r for r in R}
        f = 'bc' if d.name.startswith('bc') else ('mix' if d.name.startswith('mix') else 'scratch'); fam[f][d.name] = by
    rng = np.random.default_rng(0); out = {}; lines = []
    for f, actors in fam.items():
        names = sorted(actors); eps = sorted({e for (e, _) in next(iter(actors.values()))}); seeds = sorted({e.split('_')[0] for e in eps})
        res = {}
        for s in a.grid:
            rule = f'proxyage_{s:g}'
            W = {n: {e: actors[n][(e, rule)]['queue_sum'] / actors[n][(e, 'prefix')]['queue_sum'] - 1 for e in eps} for n in names}
            sv = float(np.mean([1 - sum(actors[n][(e, rule)]['bytes'] for e in eps) / sum(actors[n][(e, 'prefix')]['bytes'] for e in eps) for n in names]))
            by_seed = {n: defaultdict(list) for n in names}
            for n in names:
                for e, v in W[n].items():
                    by_seed[n][e.split('_')[0]].append(v)
            bs = []
            for _ in range(a.n):
                an = rng.choice(names, len(names)); ss = rng.choice(seeds, len(seeds))
                bs.append(np.mean([np.mean(sum((by_seed[n][k] for k in ss), [])) for n in an]))
            m = float(np.mean([np.mean(list(W[n].values())) for n in names]))
            res[s] = dict(saved=sv, waiting=m, lo=float(np.quantile(bs, 0.025)), hi=float(np.quantile(bs, 0.975)))
        ok = [s for s in a.grid if res[s]['hi'] < a.margin]
        star = max(ok, key=lambda s: res[s]['saved']) if ok else None
        out[f] = dict(actors=names, grid=res, s_star=star)
        lines.append(f'== {f} ({len(names)} actors: {", ".join(names)})')
        for s in a.grid:
            v = res[s]; lines.append(f'  s={s:>5g}: saved {v["saved"]:.3f} | waiting {v["waiting"]:+.4f} [{v["lo"]:+.4f}, {v["hi"]:+.4f}]' + ('  <- s*' if s == star else ''))
        lines.append(f'  s* = {star} (largest saving with upper bound < {a.margin:+.3f})')
    Path(a.out + '.json').write_text(json.dumps(out, indent=1)); Path(a.out + '.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--root', default='research/marl_budget/e3_truncation_cl_v3_20260929'); p.add_argument('--out', default='research/marl_budget/e3_truncation_select_s_20260929')
    p.add_argument('--grid', type=float, nargs='+', default=[40, 50, 60, 80, 100, 150]); p.add_argument('--margin', type=float, default=0.01)
    p.add_argument('--n', type=int, default=4000)
    main(p.parse_args())
