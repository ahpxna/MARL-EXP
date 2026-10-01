#!/usr/bin/env python3
"""Read MARL_e3_hindsight_probe.py shard outputs (read-only).  Per actor: the stored oracle-best candidate's gain on the
original future and on the resampled futures (retention, P(gain > 0), P(gain < 0)); the hindsight oracle E_f[max_c g]
vs the in-sample ex-ante oracle max_c E_f[g] on the evaluated subset; an honest ex-ante choice (argmax of the mean gain
over the OTHER variant futures, evaluated on the held-out one, rotated); the within-state Spearman of candidate gains
between futures.  Rows of an incomplete shard (no manifest) are reported separately and excluded from the main line.
Caveat carried into every line: only the exogenous ARRIVALS after 10 t are resampled; the capacity trace K is held at
the original seeded draw (the scheduler does not know K at t+1, t+2 either).
Usage: MARL_e3_hindsight_report.py DIR... (each DIR holds shard_k/)
"""
import glob, json, os, sys
import numpy as np
from scipy.stats import spearmanr

for D in sys.argv[1:]:
    R, partial = [], 0
    for f in sorted(glob.glob(f'{D}/shard_*/rows.json')):
        rows = json.load(open(f))
        if os.path.exists(f.replace('rows.json', 'manifest.json')):
            R += rows
        else:
            partial += len(rows)
    G = [np.array(r['gains']) for r in R]
    best_o = np.mean([g[0, 1] for g in G]); best_v = np.mean([g[1:, 1].mean() for g in G])
    hind = np.mean([g[1:].max(1).mean() for g in G]); exa = np.mean([g[1:].mean(0).max() for g in G])
    xs = [V[k, int(np.argmax(np.delete(V, k, 0).mean(0)))] for g in G for V in [g[1:]] for k in range(V.shape[0])]
    rel = [spearmanr(g[i], g[j]).correlation for g in G for i in range(len(g)) for j in range(i + 1, len(g)) if np.ptp(g[i]) > 0 and np.ptp(g[j]) > 0]
    print(f'{os.path.basename(D)}: states {len(R)} (complete shards; {partial} more in an incomplete shard, excluded), futures {G[0].shape[0] - 1}, cands {G[0].shape[1]} | '
          f'stored best: original {best_o:.2f}, resampled {best_v:.2f} (retention {best_v / best_o:.2f}), P(>0) {np.mean([np.mean(g[1:, 1] > 0) for g in G]):.2f} '
          f'P(<0) {np.mean([np.mean(g[1:, 1] < 0) for g in G]):.2f} | hindsight E_f[max] {hind:.2f}, in-sample max E_f {exa:.2f}, held-out-future choice {np.mean(xs):.2f} '
          f'({np.mean(xs) / hind:.2f} of hindsight) | within-state Spearman across futures {np.nanmean(rel):.2f} | resampled: arrivals after 10t only; capacity trace fixed')
