#!/usr/bin/env python3
"""Report for the music-theory broadcast orders (ledger L-168; development panel 901-964 x 8/16).

Per relay student seed s: mean waiting and bytes per condition, and PAIRED per-episode comparisons (ratio of sums, 95 %
bootstrap over traffic seeds, both headways of a seed resampled together, 4000 draws):
  PRIMARY  bass vs prefix order, under cap4 (iid K) and under the low capacity process;
  secondary bass vs agefirst (cap-correct), bass vs prefix under iid prefix decoding, and every condition vs the same-seed
           0-byte distilled student (its existing 'none' rows).
The pre-registered rule (L-168): 'bass helps at low capacity' iff the upper bound < 0 on BOTH seeds in BOTH conditions.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import numpy as np

E = Path('research/marl_budget/e3_music_eval_20260930'); C = Path('research/marl_budget/e3_codesign_eval_20260929')


def rows(path, rule):
    return {r['episode']: r for r in json.loads(Path(path).read_text()) if r['rule'] == rule}


def cond(s):
    return {
        ('prefix', 'iid', 'prefix'): (C / f'relay_st_s{s}_eval/rows.json', 'prefix'),
        ('prefix', 'iid', 'cap4'): (C / f'relay_st_s{s}_eval/rows.json', 'cap4') if s == 0 else (E / f'relay_st_s{s}_prefix_cap4/rows.json', 'cap4'),
        ('bass', 'iid', 'prefix'): (E / f'relay_st_s{s}_bass_iid/rows.json', 'prefix'),
        ('bass', 'iid', 'cap4'): (E / f'relay_st_s{s}_bass_iid/rows.json', 'cap4'),
        ('agefirst', 'iid', 'prefix'): (E / f'relay_st_s{s}_agefirst_iid/rows.json', 'prefix'),
        ('agefirst', 'iid', 'cap4'): (E / f'relay_st_s{s}_agefirst_iid/rows.json', 'cap4'),
        ('prefix', 'low', 'prefix'): (E / f'relay_st_s{s}_prefix_low/rows.json', 'prefix'),
        ('bass', 'low', 'prefix'): (E / f'relay_st_s{s}_bass_low/rows.json', 'prefix'),
        ('agefirst', 'low', 'prefix'): (E / f'relay_st_s{s}_agefirst_low/rows.json', 'prefix'),
        ('student0B', 'iid', 'none'): (C / f'distill_none_s{s}/rows.json', 'none'),
    }


def paired(A, B, draws=4000, seed=0):
    eps = sorted(set(A) & set(B)); assert len(eps) == 128, len(eps)
    seeds = sorted({e.split('_')[0] for e in eps}); by = {sd: [e for e in eps if e.startswith(sd + '_')] for sd in seeds}
    a = {e: A[e]['queue_sum'] for e in eps}; b = {e: B[e]['queue_sum'] for e in eps}
    est = sum(a.values()) / sum(b.values()) - 1; rng = np.random.default_rng(seed); bs = []
    for _ in range(draws):
        pick = rng.choice(seeds, len(seeds)); ee = [e for sd in pick for e in by[sd]]
        bs.append(sum(a[e] for e in ee) / sum(b[e] for e in ee) - 1)
    lo, hi = np.quantile(bs, [0.025, 0.975])
    return round(100 * est, 2), round(100 * lo, 2), round(100 * hi, 2)


def main(a):
    rep = {}; lines = []
    for s in a.seeds:
        R = {}
        for k, (p, rule) in cond(s).items():
            if Path(p).exists():
                R[k] = rows(p, rule)
        rs = rep[f's{s}'] = dict(means={}, comparisons={})
        for k, v in R.items():
            rs['means']['/'.join(k)] = dict(waiting=round(float(np.mean([r['queue_sum'] for r in v.values()])), 1),
                                            bytes_per_episode=round(float(np.mean([r['bytes'] for r in v.values()])), 1), n=len(v))
        pairs = [(('bass', 'iid', 'cap4'), ('prefix', 'iid', 'cap4'), 'PRIMARY cap4: bass - prefix order'),
                 (('bass', 'low', 'prefix'), ('prefix', 'low', 'prefix'), 'PRIMARY low: bass - prefix order'),
                 (('bass', 'iid', 'cap4'), ('agefirst', 'iid', 'cap4'), 'cap4: bass - agefirst'),
                 (('bass', 'low', 'prefix'), ('agefirst', 'low', 'prefix'), 'low: bass - agefirst'),
                 (('agefirst', 'iid', 'cap4'), ('prefix', 'iid', 'cap4'), 'cap4: agefirst - prefix order'),
                 (('agefirst', 'low', 'prefix'), ('prefix', 'low', 'prefix'), 'low: agefirst - prefix order'),
                 (('bass', 'iid', 'prefix'), ('prefix', 'iid', 'prefix'), 'iid: bass - prefix order'),
                 (('agefirst', 'iid', 'prefix'), ('prefix', 'iid', 'prefix'), 'iid: agefirst - prefix order')]
        for k in R:
            if k[0] != 'student0B':
                pairs.append((k, ('student0B', 'iid', 'none'), f'{"/".join(k)} - 0-byte student'))
        for x, y, name in pairs:
            if x in R and y in R:
                rs['comparisons'][name] = paired(R[x], R[y])
        lines.append(f'== relay_st_s{s}')
        for k, v in rs['means'].items():
            lines.append(f'   {k:22s} waiting {v["waiting"]:7.1f}  bytes/episode {v["bytes_per_episode"]:7.1f}  n {v["n"]}')
        for name, (e, lo, hi) in rs['comparisons'].items():
            lines.append(f'   {name:42s} {e:+6.2f} % [{lo:+6.2f}, {hi:+6.2f}]')
    prim = [rep[f's{s}']['comparisons'].get(n) for s in a.seeds for n in ('PRIMARY cap4: bass - prefix order', 'PRIMARY low: bass - prefix order')]
    verdict = 'incomplete' if any(p is None for p in prim) else ('SUPPORTED (dev)' if all(p[2] < 0 for p in prim) else 'NOT SUPPORTED (dev)')
    rep['primary_verdict'] = verdict; lines.append(f'PRIMARY (L-168 rule, both seeds, both conditions, upper < 0): {verdict}')
    print('\n'.join(lines)); Path(a.out).write_text(json.dumps(rep, indent=1)); Path(a.out).with_suffix('.txt').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1])
    p.add_argument('--out', default='research/marl_budget/e3_music_report_20260930.json')
    main(p.parse_args())
