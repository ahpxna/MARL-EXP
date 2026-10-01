#!/usr/bin/env python3
"""Traffic-seed cluster sensitivity for the E3 closed-loop endpoints (28/09 self-audit L-16; read-only, no rollouts).

Every E3 panel has two episodes per traffic seed (headways 8 and 16), and the reported CIs resampled EPISODES.
This recomputes each paired endpoint with (a) the episode bootstrap, as reported, and (b) a bootstrap over TRAFFIC
SEEDS (both loads of a seed resampled together; handoff F1.3), from the stored rows only:
  msguse   <actor>/msguse/rows.json: variant vs 'actual' of the same actor (A2 and the MP2-vs-actor A1 numbers);
  delay    e3_delay_v2_20260928/rows.json: each method at d vs d = 0, and MP2 vs each actor at the same d (A4);
  closed   closed-loop rows (<dir>/rows.json): every method vs the same episode's prefix, init seeds averaged (S1, S5).
Self-check: the episode-bootstrap mean reproduces the stored report's mean where one exists (msguse, delay).
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np

M = Path(__file__).resolve().parents[1] / 'research/marl_budget'


def boot(vals, keys, B=10000, seed=0):
    by = defaultdict(list)
    for v, k in zip(vals, keys):
        by[k].append(v)
    K = sorted(by); rng = np.random.default_rng(seed)
    out = [np.mean(np.concatenate([by[K[i]] for i in rng.integers(0, len(K), len(K))])) for _ in range(B)]
    return [round(float(x), 2) for x in np.quantile(out, [0.025, 0.975])]


def endpoint(rel, eps):
    seeds = [e.split('_')[0] for e in eps]; ce, cs = boot(rel, eps), boot(rel, seeds)
    return dict(mean=round(float(np.mean(rel)), 2), ci_episode=ce, ci_traffic_seed=cs, n_episodes=len(set(eps)), n_seeds=len(set(seeds)),
                changes_significance=bool((ce[0] > 0 or ce[1] < 0) != (cs[0] > 0 or cs[1] < 0)))


def msguse(d):
    rows = json.loads((M / d / 'msguse/rows.json').read_text()); rep = json.loads((M / d / 'msguse/report.json').read_text()); out = {}
    eps = [r['episode'] for r in rows]
    for k in ['full', 'none', 'stale', 'shuffle', 'mp2', 'mp2_full']:
        rel = [100 * (r[k]['queue_sum'] - r['actual']['queue_sum']) / r['actual']['queue_sum'] for r in rows]
        e = endpoint(rel, eps)
        if abs(e['mean'] - rep[f'{k}_vs_actual_pct']['mean']) > 0.01:
            raise SystemExit(f'SELF-CHECK FAIL: {d} {k} mean {e["mean"]} != report {rep[f"{k}_vs_actual_pct"]["mean"]}')
        out[f'{k}_vs_actual'] = e
    return out


def delay(d):
    rows = json.loads((M / d / 'rows.json').read_text()); rep = json.loads((M / d / 'report.json').read_text())
    Q = {(r['actor'], r['delay'], r['episode']): r['queue_sum'] for r in rows}; eps = sorted({r['episode'] for r in rows})
    names = sorted({r['actor'] for r in rows}); ds = sorted({r['delay'] for r in rows}); out = {}
    for n in names:
        for dd in ds:
            rel = [100 * (Q[(n, dd, e)] - Q[(n, 0, e)]) / Q[(n, 0, e)] for e in eps]; out[f'{n}/d{dd}_vs_d0'] = endpoint(rel, eps)
            if n != 'mp2':
                rel2 = [100 * (Q[('mp2', dd, e)] - Q[(n, dd, e)]) / Q[(n, dd, e)] for e in eps]; out[f'mp2_vs_{n}/d{dd}'] = endpoint(rel2, eps)
    for k, v in out.items():
        if k in rep and abs(v['mean'] - rep[k]['mean']) > 0.01:
            raise SystemExit(f'SELF-CHECK FAIL: {d} {k} mean {v["mean"]} != report {rep[k]["mean"]}')
    return out


def closed(d):
    rows = json.loads((M / d / 'rows.json').read_text()); per = defaultdict(lambda: defaultdict(list))
    for r in rows:
        per[r['method'].split('/')[0]][r['episode']].append(r['queue_sum'])
    eps = sorted(per['prefix']); pq = {e: per['prefix'][e][0] for e in eps}; out = {}
    for m_, dd in per.items():
        if m_ == 'prefix':
            continue
        if sorted(dd) != eps:
            raise SystemExit(f'SELF-CHECK FAIL: {d} {m_} misses prefix episodes')
        out[m_] = endpoint([100 * (np.mean(dd[e]) - pq[e]) / pq[e] for e in eps], eps)
    return out


def main(a):
    res = {'msguse': {}, 'delay': {}, 'closed': {}}
    for d in a.msguse:
        res['msguse'][d] = msguse(d)
    for d in a.delay:
        res['delay'][d] = delay(d)
    for d in a.closed:
        res['closed'][d] = closed(d)
    Path(a.out).write_text(json.dumps(res, indent=1))
    for kind, R in res.items():
        for d, E in R.items():
            for k, e in E.items():
                flag = '  <-- significance changes' if e['changes_significance'] else ''
                print(f'{kind:7s} {d:52s} {k:24s} {e["mean"]:+6.2f}  ep {e["ci_episode"]}  seed {e["ci_traffic_seed"]} (n={e["n_seeds"]}){flag}')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--msguse', nargs='*', default=[]); p.add_argument('--delay', nargs='*', default=[]); p.add_argument('--closed', nargs='*', default=[])
    p.add_argument('--out', required=True)
    main(p.parse_args())
