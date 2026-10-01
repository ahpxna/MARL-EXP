#!/usr/bin/env python3
"""Traffic-free replica: which relay packets keep the one-step freshness bound when the team grows (30/09 20:5x EDT; ledger L-188).

Same prefix sets (models/marl_hetero_selector.prefix_sets), capacity processes and covering-head rule as
scripts/MARL_e3_math_replica.py (imported, not copied).  Merges compared, on m = 9 and m = 16:
  full            the E3 transient merge (models/marl_delivery_music.AgeMirror): every packet carries every agent (O(m) slots)
  slots8          RELAY v3 (models/marl_relay_v3): sender k carries only its 8 nearest grid neighbours, transient merge
  news            PROPOSED: sender k carries only what it decoded DIRECTLY at the previous step (with ids), and receivers keep
                  memory (persistent max); packet size = number of news entries, recorded
  news_nomem      the same packets with the transient merge (control: memory is what makes news packets sufficient)
Heads: hub (the replica's covering receiver of the previous step, not the head when possible), hubK (the EVALUATOR's rule,
models/marl_delivery_music_v4.HubDelivery: largest previous capacity, ties by the age-first key) and agefirst.
For every receiver INCLUDING the head, agent j != i and step t >= 12: lower = copy fresher than the last transmission
(impossible), upper = age above 1 + the previous step's injection age (the one-step bound).  Also: whether the hubK head
was a covering receiver of the previous step and differed from the previous head (the hypotheses of
LeanMarlRelayOneHopV1.one_hop).
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from models.marl_hetero_selector import prefix_sets
from models.marl_delivery_music import AgeMirror, NEVER
from models.marl_relay_v3 import nearest_slots
from scripts.MARL_e3_math_replica import caps


class SlotMirror(AgeMirror):
    def __init__(self, m, slots):
        super().__init__(m); self.slots = slots

    def update(self, sets, meas_time):
        for k in range(self.m):
            for j in range(self.m):
                if j != k and j not in self.slots[k]:
                    self.table[k, j] = NEVER
        super().update(sets, meas_time)


class NewsMirror:
    """table[i, j]: freshest measurement time of j held by i.  Sender k's packet at step t carries k's direct decodes of step
    t - 1 (measured at t - 1).  memory=True keeps previous copies (persistent max); False is transient."""

    def __init__(self, m, memory=True):
        self.m = m; self.memory = memory
        self.table = np.full((m, m), NEVER); self.cache = np.full((m, m), NEVER)
        self.prev_sets = [frozenset()] * m; self.prev_time = None; self.max_news = 0

    def update(self, sets, meas_time):
        m = self.m; new = np.full((m, m), NEVER)
        self.max_news = max(self.max_news, max(len(s) for s in self.prev_sets))
        for i in range(m):
            best = np.maximum(self.table[i], self.cache[i]) if self.memory else self.cache[i].copy()
            for k in sets[i]:
                for j in self.prev_sets[k]:
                    best[j] = max(best[j], self.prev_time)
            for k in sets[i]:
                best[k] = meas_time
            best[i] = NEVER; new[i] = best
        for i in range(m):
            for k in sets[i]:
                self.cache[i, k] = meas_time
        self.table = new; self.prev_sets = [frozenset(s) for s in sets]; self.prev_time = meas_time


def run(kind, head, merge, m, rows, cols, T=40, eps=100, seed0=20_000):
    slots = nearest_slots(rows, cols, 8)
    ages, inj = [], []; c = dict(lower_head=0, upper_head=0, lower_other=0, upper_other=0, checks_head=0, checks_other=0)
    hubK = dict(steps=0, covering=0, distinct=0, both=0); max_news = 0
    for e in range(eps):
        rng = np.random.default_rng(seed0 + e)
        M = {'full': lambda: AgeMirror(m), 'slots8': lambda: SlotMirror(m, slots),
             'news': lambda: NewsMirror(m, True), 'news_nomem': lambda: NewsMirror(m, False)}[merge]()
        paid = [None] * m; last = np.full(m, -10 ** 6); cover = None; f_prev = None; lastK = None
        prev_sets = None; prev_U = None; prev_head = None
        for t in range(T):
            key = lambda j: (0, j) if paid[j] is None else (1, paid[j], j)
            order = list(sorted(range(m), key=key))
            if t > 0 and head == 'hub' and cover is not None:
                order = [cover] + [j for j in order if j != cover]
            if t > 0 and head == 'hubK' and lastK is not None:
                b = min(range(m), key=lambda j: (-lastK[j], key(j)))
                hubK['steps'] += 1
                cov = prev_U - {b} <= set(prev_sets[b]); dis = b != prev_head
                hubK['covering'] += int(cov); hubK['distinct'] += int(dis); hubK['both'] += int(cov and dis)
                order = [b] + [j for j in order if j != b]
            K = caps(kind, m, rng); sets = prefix_sets(tuple(order), K)
            if kind == 'cap4':
                hd = set(order[:4]); sets = [frozenset(j for j in sets[i] if j in hd) for i in range(m)]
            U = set().union(*sets)
            for j in U: paid[j] = t; last[j] = t
            M.update(sets, float(t)); f = t - last
            if t >= 12:
                a = np.where(M.table > NEVER / 2, t - M.table, 10 ** 6)
                for i in range(m):
                    tag = 'head' if i == order[0] else 'other'
                    for j in range(m):
                        if j != i and last[j] >= 0:  # never-transmitted agents satisfy both bounds trivially (sentinels)
                            c['checks_' + tag] += 1
                            c['lower_' + tag] += int(a[i, j] < f[j]); c['upper_' + tag] += int(a[i, j] > 1 + f_prev[j])
                a2 = np.minimum(a.astype(float), 14.0); np.fill_diagonal(a2, np.nan)
                ages.append(np.nanmean(a2)); inj.append(float(np.mean(np.minimum(f, 14))))
            covs = [i for i in range(m) if U - {i} <= set(sets[i])]
            cover = ([i for i in covs if i != order[0]] or covs or [None])[0]; f_prev = f; lastK = K
            prev_sets = sets; prev_U = U; prev_head = order[0]
        if merge.startswith('news'):
            max_news = max(max_news, M.max_news)
    out = dict(mean_age=float(np.mean(ages)), mean_injection_age=float(np.mean(inj)), **c)
    if head == 'hubK':
        out['hubK'] = hubK
    if merge.startswith('news'):
        out['max_news_entries'] = int(max_news); out['news_packet_bits_4bit_ids'] = 17 + int(max_news) * (21 + 4)
    return out


def main(a):
    out = dict(script=Path(__file__).name, eps=a.eps, T=40, results={})
    t0 = time.time()
    for (rows, cols) in ((3, 3), (4, 4)):
        m = rows * cols
        for kind in a.kinds.split(','):
            for head in ('hub', 'hubK', 'agefirst'):
                for merge in ('full', 'slots8', 'news', 'news_nomem'):
                    if m == 9 and merge == 'slots8':
                        continue
                    r = run(kind, head, merge, m, rows, cols, eps=a.eps)
                    out['results'][f'{rows}x{cols}|{kind}|{head}|{merge}'] = r
                    print(f'{rows}x{cols} {kind:6s} {head:8s} {merge:10s} age {r["mean_age"]:.2f} inj {r["mean_injection_age"]:.2f} '
                          f'upper other {r["upper_other"]}/{r["checks_other"]} head {r["upper_head"]}/{r["checks_head"]} '
                          f'lower {r["lower_other"] + r["lower_head"]}'
                          + (f' hubK cov {r["hubK"]["covering"]}/{r["hubK"]["steps"]} both {r["hubK"]["both"]}' if 'hubK' in r else '')
                          + (f' news {r["max_news_entries"]} ({r["news_packet_bits_4bit_ids"]} b)' if 'max_news_entries' in r else '')
                          + f'  [{time.time() - t0:.0f}s]', flush=True)
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--eps', type=int, default=100)
    p.add_argument('--kinds', default='iid,low,const1,const2,rich7,cap4')
    p.add_argument('--out', required=True)
    main(p.parse_args())
