#!/usr/bin/env python3
"""Traffic-free replica checks of the channel mathematics (30/09 19:4x EDT; ledgers L-180, L-181).
Uses the E3 prefix sets (models/marl_hetero_selector.prefix_sets) and the E3 scheduler mirror (models/marl_delivery_music.AgeMirror,
the transient relay merge asserted equal to the evaluator's merged views in CityFlow).  Writes one JSON with:
  floor     receiver mean age and injection age under age-first / bass / hub heads, per capacity process, against F(m, L)
  onehop    the one-hop sandwich f_j(t) <= a_i(t)[j] <= 1 + f_j(t-1), checked for EVERY receiver, agent and step (i != head),
            with a covering-receiver head (hub) and, as a control that can fail, with the age-first head
  hetero    one rich receiver (K = k) and the rest K = 1, against all receivers K = k: relay age-first, relay hub, raw age-first
  lock      raw packets, constant K, age-first with index ties: never-covered share vs (m - L) / (L (m - 1)) when L | m
  memory    transient (E3) vs persistent (gossip) merge
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from models.marl_hetero_selector import prefix_sets
from models.marl_delivery_music import AgeMirror, NEVER


class Persistent(AgeMirror):
    def update(self, sets, meas_time):
        m = self.m; new = np.full((m, m), NEVER)
        for i in range(m):
            best = np.maximum(self.cache[i], self.table[i])
            for k in sets[i]:
                best = np.maximum(best, self.table[k])
            for k in sets[i]:
                best[k] = meas_time
            best[i] = NEVER; new[i] = best
        for i in range(m):
            for k in sets[i]:
                self.cache[i, k] = meas_time
        self.table = new


def F(m, L):
    return sum(s * min(L, m - s * L) for s in range(0, -(-m // L))) / m


def caps(kind, m, rng):
    if kind in ('iid', 'cap4'): return list(rng.integers(1, 8, m))
    if kind == 'low': return list(rng.integers(1, 4, m))
    if kind.startswith('const'): return [int(kind[5:])] * m
    if kind.startswith('rich'):
        K = [1] * m; K[int(rng.integers(m))] = int(kind[4:]); return K
    raise ValueError(kind)


def run(kind, head, m=9, T=40, eps=300, merge='transient', raw=False, check=False, seed0=0):
    ages, inj, L_seen = [], [], []; lo = up = checks = 0
    for e in range(eps):
        rng = np.random.default_rng(seed0 + e); M = (Persistent if merge == 'persistent' else AgeMirror)(m)
        paid = [None] * m; last = np.full(m, -10 ** 6); cover = None; f_prev = None; lastK = None
        for t in range(T):
            key = lambda j: (0, j) if paid[j] is None else (1, paid[j], j)
            order = list(sorted(range(m), key=key))
            if t > 0 and head == 'hub' and cover is not None:
                order = [cover] + [j for j in order if j != cover]
            if t > 0 and head == 'bass':
                st = M.staleness(float(t)); b = min(range(m), key=lambda j: (st[j], key(j))); order = [b] + [j for j in order if j != b]
            K = caps(kind, m, rng); sets = prefix_sets(tuple(order), K)
            if kind == 'cap4':
                hd = set(order[:4]); sets = [frozenset(j for j in sets[i] if j in hd) for i in range(m)]
            U = set().union(*sets); L_seen.append(len(U))
            for j in U: paid[j] = t; last[j] = t
            M.update(sets, float(t)); f = t - last
            if t >= 12:
                tab = M.cache if raw else M.table
                a = np.where(tab > NEVER / 2, t - tab, 10 ** 6)
                if check:
                    for i in range(m):
                        if i == order[0]:
                            continue
                        for j in range(m):
                            if j != i:
                                checks += 1; lo += int(a[i, j] < f[j]); up += int(a[i, j] > 1 + f_prev[j])
                a2 = np.minimum(a.astype(float), 14.0); np.fill_diagonal(a2, np.nan); ages.append(np.nanmean(a2)); inj.append(float(np.mean(np.minimum(f, 14))))
            covs = [i for i in range(m) if U - {i} <= set(sets[i])]
            cover = ([i for i in covs if i != order[0]] or covs or [None])[0]; f_prev = f
    return dict(mean_age=float(np.mean(ages)), mean_injection_age=float(np.mean(inj)), mean_stream_length=float(np.mean(L_seen)),
                **(dict(lower_violations=lo, upper_violations=up, checks=checks) if check else {}))


def lock(m, K, ties='index', T=400, warm=200, seed=0):
    rng = np.random.default_rng(seed); paid = [None] * m; cov = np.zeros((m, m), bool); tie = np.arange(m)
    for t in range(T):
        if ties == 'random': tie = rng.permutation(m)
        key = lambda j: (0, tie[j]) if paid[j] is None else (1, paid[j], tie[j])
        order = tuple(sorted(range(m), key=key)); sets = prefix_sets(order, [K] * m)
        for j in set().union(*sets): paid[j] = t
        if t >= warm:
            for i in range(m):
                for j in sets[i]: cov[i, j] = True
    np.fill_diagonal(cov, True)
    return float(1 - (cov.sum() - m) / (m * (m - 1)))


def main(a):
    out = dict(F={str(L): F(9, L) for L in range(1, 10)}, floor={}, onehop={}, hetero={}, lock=[], memory={})
    for kind in ('iid', 'cap4', 'low', 'const1', 'const2', 'const3', 'rich7'):
        out['floor'][kind] = {h: run(kind, h, eps=a.eps) for h in ('agefirst', 'bass', 'hub')}
        print('floor', kind, {h: round(v['mean_age'], 3) for h, v in out['floor'][kind].items()}, flush=True)
    for kind in ('iid', 'low', 'const1', 'rich7'):
        out['onehop'][kind] = {h: run(kind, h, eps=a.eps_check, check=True, seed0=10_000) for h in ('hub', 'agefirst')}
        print('onehop', kind, {h: (v['upper_violations'], v['checks']) for h, v in out['onehop'][kind].items()}, flush=True)
    for k in (2, 3, 4, 6, 8):
        out['hetero'][str(k)] = dict(homogeneous=dict(relay_agefirst=run(f'const{k}', 'agefirst', eps=a.eps), relay_hub=run(f'const{k}', 'hub', eps=a.eps),
                                                    raw_agefirst=run(f'const{k}', 'agefirst', eps=a.eps, raw=True)),
                                     one_rich=dict(relay_agefirst=run(f'rich{k}', 'agefirst', eps=a.eps), relay_hub=run(f'rich{k}', 'hub', eps=a.eps),
                                                   raw_agefirst=run(f'rich{k}', 'agefirst', eps=a.eps, raw=True)))
        print('hetero', k, flush=True)
    for m in range(4, 14):
        for K in range(1, m - 1):
            L = K + 1
            out['lock'].append(dict(m=m, K=K, never_covered_index_ties=lock(m, K), never_covered_random_ties=lock(m, K, 'random'),
                                    formula_if_divisible=((m - L) / (L * (m - 1)) if m % L == 0 else None)))
    for kind in ('iid', 'low', 'const2'):
        out['memory'][kind] = {mg: run(kind, 'agefirst', eps=a.eps, merge=mg)['mean_age'] for mg in ('transient', 'persistent')}
    Path(a.out).write_text(json.dumps(out, indent=1)); print('wrote', a.out)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--eps', type=int, default=300); p.add_argument('--eps-check', type=int, default=200)
    p.add_argument('--out', default='research/marl_budget/e3_math_replica_20260930.json')
    main(p.parse_args())
