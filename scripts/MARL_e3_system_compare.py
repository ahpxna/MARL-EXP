#!/usr/bin/env python3
"""Paired comparison of E3 SYSTEMS (actor + delivery rule) on common episodes (29/09).  Read-only.

Each system is DIR:RULE[:ACTOR], a COMPLETE run directory whose rows.json has 'episode', 'rule', 'queue_sum', 'bytes'
(and 'actor' for delivery-eval runs).  Every system is compared with the FIRST (the reference): per episode
waiting / reference waiting - 1; mean and 95 % bootstrap CI over traffic seeds with both headways kept together
(4000 resamples, seed 0); bytes per step of each system.
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np


def load(spec):
    parts = spec.split(':'); d, rule = parts[0], parts[1]; actor = parts[2] if len(parts) > 2 else None
    if not Path(d, 'manifest.json').exists():
        raise SystemExit(f'{d} is not COMPLETE')
    R = [r for r in json.loads(Path(d, 'rows.json').read_text()) if r['rule'] == rule and (actor is None or r.get('actor') == actor)]
    return {r['episode']: (r['queue_sum'], r['bytes']) for r in R}


def main(a):
    S = [(s, load(s)) for s in a.systems]; ref_name, ref = S[0]
    eps = sorted(set.intersection(*[set(v) for _, v in S])); rng = np.random.default_rng(0); lines = [f'reference {ref_name}; {len(eps)} common episodes']
    out = {}
    for name, v in S:
        d = {e: v[e][0] / ref[e][0] - 1 for e in eps}; by = defaultdict(list)
        for e, x in d.items():
            by[e.split('_')[0]].append(x)
        keys = sorted(by); bs = [np.mean(sum((by[k] for k in rng.choice(keys, len(keys))), [])) for _ in range(4000)]
        m, lo, hi = float(np.mean(list(d.values()))), float(np.quantile(bs, 0.025)), float(np.quantile(bs, 0.975))
        bps = float(np.mean([v[e][1] for e in eps])) / 26
        out[name] = dict(vs_reference=(m, lo, hi), bytes_per_step=bps, mean_waiting=float(np.mean([v[e][0] for e in eps])))
        lines.append(f'{name:90s} {bps:6.1f} B/step | waiting {out[name]["mean_waiting"]:8.1f} | {m:+.4f} [{lo:+.4f}, {hi:+.4f}]')
    if a.out:
        Path(a.out + '.json').write_text(json.dumps(out, indent=1)); Path(a.out + '.txt').write_text('\n'.join(lines) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('systems', nargs='+'); p.add_argument('--out', default='')
    main(p.parse_args())
