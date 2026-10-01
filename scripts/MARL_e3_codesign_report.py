#!/usr/bin/env python3
"""Co-design comparison (29/09): a delivery-trained actor under truncation rules (MARL_e3_truncation_closed_loop_v3.py rows)
against the PREFIX SYSTEM on the same episodes: the prefix-trained scratch actors under the prefix rule, read from the
v3 (or v2) truncation closed-loop rows of seeds 901-964 x 8/16.  Per rule: bytes per step, waiting change against the
per-episode mean of the prefix actors (mean and 95 % bootstrap CI over traffic seeds, both loads kept together), and
the same against each prefix actor.  Read-only.
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np


def boot_by_seed(d, n=2000, seed=0):
    by = defaultdict(list)
    for e, v in d.items():
        by[e.split('_')[0]].append(v)
    keys = sorted(by); r = np.random.default_rng(seed)
    vals = [np.mean(sum((by[k] for k in r.choice(keys, len(keys))), [])) for _ in range(n)]
    return float(np.mean(list(d.values()))), float(np.quantile(vals, 0.025)), float(np.quantile(vals, 0.975))


def main(a):
    ref = {}
    for tag in a.prefix_actors:
        for root in a.prefix_roots:
            f = Path(root, tag, 'rows.json')
            if Path(root, tag, 'manifest.json').exists():
                ref[tag] = {r['episode']: (r['queue_sum'], r['bytes']) for r in json.loads(f.read_text()) if r['rule'] == 'prefix'}; break
    R = json.loads(Path(a.run, 'rows.json').read_text()); rules = sorted({r['rule'] for r in R}, key=lambda x: (x != 'prefix', x))
    eps = sorted(set.intersection(*[set(v) for v in ref.values()], {r['episode'] for r in R}))
    refm = {e: float(np.mean([ref[t][e][0] for t in ref])) for e in eps}; refb = float(np.mean([ref[t][e][1] for t in ref for e in eps])) / 26
    lines = [f'prefix system: {len(ref)} actors ({", ".join(ref)}), {len(eps)} common episodes, {refb:.1f} B/step',
             f'{"rule":12s} {"B/step":>7s}  vs prefix system [95% CI]   | per prefix actor']
    out = {}
    for rule in rules:
        d = {r['episode']: r for r in R if r['rule'] == rule and r['episode'] in eps}
        m = boot_by_seed({e: d[e]['queue_sum'] / refm[e] - 1 for e in eps}); bps = float(np.mean([d[e]['bytes'] for e in eps])) / 26
        per = {t: float(np.mean([d[e]['queue_sum'] / ref[t][e][0] - 1 for e in eps])) for t in ref}
        out[rule] = dict(bytes_per_step=bps, vs_prefix_system=m, per_prefix_actor=per)
        lines.append(f'{rule:12s} {bps:7.1f}  {m[0]:+.4f} [{m[1]:+.4f}, {m[2]:+.4f}] | ' + ' '.join(f'{v:+.3f}' for v in per.values()))
    Path(a.out + '.json').write_text(json.dumps(out, indent=1)); Path(a.out + '.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--run', required=True); p.add_argument('--out', required=True)
    p.add_argument('--prefix-roots', nargs='+', default=['research/marl_budget/e3_truncation_cl_v3_20260929', 'research/marl_budget/e3_truncation_cl_v2_20260929'])
    p.add_argument('--prefix-actors', nargs='+', default=['scratch_s3', 'scratch_rs_s0', 'scratch_rs_s1', 'scratch_rs_s2', 'scratch_rs_s4'])
    main(p.parse_args())
