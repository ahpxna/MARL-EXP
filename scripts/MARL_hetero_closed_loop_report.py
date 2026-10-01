#!/usr/bin/env python3
"""Full traffic endpoints of a closed-loop run (read-only on rows.json).

Per method (init seeds averaged per episode): sum of waiting, finished and unfinished vehicles,
throughput, travel time of FINISHED vehicles (biased: excludes the unfinished), CityFlow's
CENSORED average travel time (unfinished vehicles counted up to the end of the episode), bytes,
edits.  Paired relative differences against the prefix and against a control, with a bootstrap
over episodes.
Self-check (abort): every deployable method (prefix and learned selectors) must show zero oracle
access in the environment's access log; only oracle_* references may use it.
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np

KEYS = [('queue_sum', 'Σ waiting', -1), ('finished', 'finished', +1),
        ('summary.unfinished_vehicles', 'unfinished', -1), ('summary.throughput_per_hour', 'throughput/h', +1),
        ('summary.travel_time_finished_mean', 'TT finished (biased)', -1),
        ('summary.travel_time_cityflow_censored', 'TT censored', -1), ('bytes', 'bytes', -1)]


def get(r, k):
    for part in k.split('.'):
        r = r[part]
    return float(r)


def boot(v, B=10000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v, float)
    return np.quantile([v[rng.integers(0, len(v), len(v))].mean() for _ in range(B)], [0.025, 0.975])


def main(a):
    rows = json.loads((Path(a.run) / 'rows.json').read_text())
    by = defaultdict(dict)
    for r in rows:
        dep = not r['method'].startswith('oracle')
        if dep and r['summary'].get('oracle_access_used'):
            raise AssertionError(f'deployable method {r["method"]} used oracle access in {r["episode"]}')
        by[r['method'].split('/')[0]].setdefault(r['episode'], []).append(r)
    eps = sorted(by['prefix'])
    mean = {m: {k: np.array([np.mean([get(x, k) for x in by[m][e]]) for e in eps]) for k, _, _ in KEYS} for m in by}
    print(f'{len(eps)} episodes; methods: {sorted(by)}')
    for m in sorted(by):
        print(f'\n== {m}')
        for k, name, _ in KEYS:
            v = mean[m][k]; p = mean['prefix'][k]
            line = f'  {name:22s} {v.mean():10.2f}'
            if m != 'prefix':
                rel = (v - p) / np.where(p == 0, 1, p); lo, hi = boot(rel)
                line += f'   vs prefix {100 * rel.mean():+6.2f}% [{100 * lo:+6.2f},{100 * hi:+6.2f}]'
            if a.control and m not in ('prefix', a.control) and a.control in mean:
                c = mean[a.control][k]; rel = (v - c) / np.where(c == 0, 1, c); lo, hi = boot(rel)
                line += f'   vs {a.control} {100 * rel.mean():+6.2f}% [{100 * lo:+6.2f},{100 * hi:+6.2f}]'
            print(line)
    print('\nself-check: no deployable method used oracle access')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('run'); p.add_argument('--control', default='ctrl_history')
    main(p.parse_args())
