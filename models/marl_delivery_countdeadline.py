"""COUNT-DEADLINE order (01/10/2026 23:4x EDT; PROTOCOL_E3_NET_COUNT_20261001.md Part 4, direction B).

Why: across channels the value of communication tracks the COUNT of out-of-support copies (L-239), not their summed age;
the receiver tolerates copies up to its training range tau.  Rule: before committing the order at step t, for every sender
j count u_j = the number of OTHER receivers whose freshest copy of j (scheduler mirror, AgeMirror.table — the scheduler
information every E3 order already uses) is at least tau decision steps old, or absent; senders are ordered by u_j, most
first, ties by the age-first key (unheard first, then the oldest last broadcast, then the index).  With u_j equal for all
senders this is exactly MusicDelivery('agefirst').  Capacities, prefix sets, the cap<c> rule, R = 0 and byte accounting are
MusicDelivery's.
"""
from __future__ import annotations
import numpy as np
from models.marl_delivery_music import MusicDelivery, AgeMirror, NEVER
from models.marl_hetero_selector import prefix_sets


class CountDeadlineDelivery(MusicDelivery):
    def __init__(self, tau):
        super().__init__('agefirst'); self.tau = float(tau)
        if not self.tau >= 0:
            raise ValueError(tau)
        self.stats = dict(steps=0, steps_reordered=0)

    def counts(self, now, interval):
        A = np.where(self.mirror.table > NEVER / 2, (now - self.mirror.table) / float(interval), np.inf)
        np.fill_diagonal(A, -np.inf)                       # a receiver's own entry is not a copy
        return (A >= self.tau - 1e-9).sum(0)              # column j: receivers holding j out of support

    def __call__(self, env, seed, load, t):
        m = env.n_agents
        if t == 0 or self.mirror is None:
            self.mirror = AgeMirror(m)
        mode = self.mode
        if not (mode == 'prefix' or mode.startswith('cap')):
            raise ValueError(f'count-deadline orders support prefix / cap<c>, not {mode}')
        ctx = env.scheduler_context(); now = float(env._now()); P = ctx.packets
        key = lambda j: (0, j) if P[j] is None else (1, P[j].measured_at, j)
        base = tuple(sorted(range(m), key=key))
        u = self.counts(now, env.action_interval) if t > 0 else np.zeros(m)
        order = tuple(sorted(range(m), key=lambda j: (-int(u[j]),) + key(j)))
        self.stats['steps'] += 1; self.stats['steps_reordered'] += int(order != base)
        env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        sets = prefix_sets(order, K)
        if mode.startswith('cap'):
            head = set(order[:int(mode[3:])])
            sets = [frozenset(j for j in sets[i] if j in head) for i in range(m)]; env._k = {i: len(sets[i]) for i in range(m)}
        env.submit_profile([set(s) for s in sets], R=0)
        self.mirror.update(sets, now); self.last_order = order
        return sets
