#!/usr/bin/env python3
"""Report for MARL_e3_delivery_eval.py (information ceiling).  Read-only on a COMPLETE run dir.

Per actor x delivery rule: mean episode waiting (sum of queues) and mean bytes per step.  Paired comparisons, per
episode, against the PREFIX SYSTEM = the prefix-trained scratch actors under the prefix rule (each actor separately and
their per-episode mean): relative change (system / reference - 1), mean and 95 % bootstrap CI over traffic seeds with
both headways of a seed kept together (2000 resamples, seed 0).
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np


def boot_by_seed(d, n=2000, seed=0):
    """d: {episode: value}; resample traffic seeds (both loads together)."""
    by = defaultdict(list)
    for e, v in d.items():
        by[e.split('_')[0]].append(v)
    keys = sorted(by); r = np.random.default_rng(seed)
    vals = [np.mean(sum((by[k] for k in r.choice(keys, len(keys))), [])) for _ in range(n)]
    return float(np.mean(list(d.values()))), float(np.quantile(vals, 0.025)), float(np.quantile(vals, 0.975))


def main(a):
    R = json.loads(Path(a.run, 'rows.json').read_text())
    W = defaultdict(dict); B = defaultdict(dict)
    for r in R:
        W[(r['actor'], r['rule'])][r['episode']] = r['queue_sum']; B[(r['actor'], r['rule'])][r['episode']] = r['bytes'] / 26.0
    refs = [k for k in W if k[1] == 'prefix' and k[0] in a.prefix_actors]
    eps = sorted(set.intersection(*[set(W[k]) for k in refs]))
    ref_mean = {e: float(np.mean([W[k][e] for k in refs])) for e in eps}
    lines = [f'reference = mean over {len(refs)} prefix-trained actors under prefix ({", ".join(k[0] for k in refs)}); {len(eps)} episodes',
             f'{"actor":16s} {"rule":8s} {"waiting":>9s} {"B/step":>7s}  vs reference mean [95% CI]']
    out = {}
    for (act, rule), d in sorted(W.items()):
        rel = {e: d[e] / ref_mean[e] - 1 for e in eps if e in d}
        m, lo, hi = boot_by_seed(rel)
        out[f'{act}/{rule}'] = dict(mean_waiting=float(np.mean(list(d.values()))), bytes_per_step=float(np.mean(list(B[(act, rule)].values()))), vs_reference=(m, lo, hi))
        lines.append(f'{act:16s} {rule:8s} {np.mean(list(d.values())):9.1f} {np.mean(list(B[(act, rule)].values())):7.1f}  {m:+.4f} [{lo:+.4f}, {hi:+.4f}]')
    Path(a.out + '.json').write_text(json.dumps(out, indent=1)); Path(a.out + '.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--run', required=True); p.add_argument('--out', required=True)
    p.add_argument('--prefix-actors', nargs='+', default=['scratch_s3', 'scratch_rs_s0', 'scratch_rs_s1', 'scratch_rs_s2', 'scratch_rs_s4'])
    main(p.parse_args())
