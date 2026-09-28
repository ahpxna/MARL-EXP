#!/usr/bin/env python3
"""Aggregate every mitigation DEVELOPMENT screen into one paired table (read-only).

For each (method, total cap, policy): seed-averaged mean gain on the development groups (501-508,
opened B1 test), fraction of the oracle at the method's own (bid-reduced) cap, and the paired
difference to the better no-bid legal control (ctrl_public / ctrl_history, chosen by the SELECT
metric at +28) at the SAME total cap and policy, with a cluster bootstrap over development
episodes.  Development evidence only; not confirmatory.
"""
from __future__ import annotations
import argparse, glob, json
from collections import defaultdict
from pathlib import Path
import numpy as np


def boot(v, eps, B=5000, seed=0):
    rng = np.random.default_rng(seed); E = sorted(set(eps))
    idx = {e: np.array([i for i, x in enumerate(eps) if x == e]) for e in E}; v = np.asarray(v, float)
    out = [v[np.concatenate([idx[E[p]] for p in rng.choice(len(E), len(E))])].mean() for _ in range(B)]
    return np.quantile(out, [0.025, 0.975])


def main(a):
    rows = defaultdict(list)          # (method, cap, pol) -> list of (gains, eps, oracle)
    sel_metric = defaultdict(list)
    for d in a.dirs:
        for f in sorted(glob.glob(f'{d}/job_*.json')):
            j = json.load(open(f))
            for name, res in j['results'].items():
                for cap, row in res.items():
                    for pol in ('repair_R1', 'direct'):
                        rows[(name, cap, pol)].append((row[pol]['gains'], row[pol].get('eps'), row['oracle_R1']['gains']))
            sel_metric[j['learner']].append(j['select_metric'])
        rf = Path(d) / 'rules.json'
        if rf.exists():
            R = json.load(open(rf))
            for name, res in R.items():
                if name in ('table', 'counts'):
                    continue
                for cap, row in res.items():
                    for pol in ('repair_R1', 'direct'):
                        rows[(name, cap, pol)].append((row[pol]['gains'], row[pol]['eps'], row['oracle_R1']['gains']))
    eps_ref = next(v[0][1] for v in rows.values() if v[0][1] is not None)
    ctrl = max(('ctrl_public', 'ctrl_history'), key=lambda c: np.mean(sel_metric.get(c, [-np.inf])))
    print(f'no-bid control chosen by select metric: {ctrl}\n')
    print(f'{"method":24s} {"cap":5s} {"policy":9s} {"gain":>7s} {"%orc":>6s} {"vs ctrl":>8s} {"CI95 of diff":>18s}  seeds')
    for (name, cap, pol) in sorted(rows, key=lambda k: (k[1], k[2], k[0])):
        L = rows[(name, cap, pol)]
        g = np.mean([x[0] for x in L], axis=0); orc = float(np.mean(L[0][2]))
        c = rows.get((ctrl, cap, pol))
        if c:
            gc = np.mean([x[0] for x in c], axis=0); diff = g - gc; lo, hi = boot(diff, eps_ref)
            ds = f'{diff.mean():+8.3f} [{lo:+7.3f},{hi:+7.3f}]'
        else:
            ds = ''
        per = ' '.join(f'{np.mean(x[0]):+.2f}' for x in L)
        print(f'{name:24s} {cap:5s} {pol:9s} {g.mean():+7.3f} {100 * g.mean() / orc if orc else 0:6.1f} {ds:>28s}  {per}')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('dirs', nargs='+')
    main(p.parse_args())
