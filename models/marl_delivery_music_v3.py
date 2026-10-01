"""Broadcast orders v3 (30/09 16:3x EDT; ledger L-178): the LIFETIME-DEADLINE head 'deadline<D>'.

Why (corpus notes, section "Novelty against 'just relay + distillation'", item B):
  * Paper A: the repair of a frozen surrogate should be TARGETED at the starved cells; the uniform beta-mixture of
    models/marl_delivery_music_v2.py (V-A) is the untargeted version and is inefficient on seed 1;
  * FUNCTIONAL LIFE4: a relayed copy has a decision lifetime; refresh a sender when its copy is about to expire;
  * pinwheel scheduling: "sender j at the head at least once every a_j steps" bounds j's age at EVERY receiver by a_j - 1,
    because the head is decoded by every receiver with K_i >= 1.  This rule is an online earliest-deadline heuristic.
Rule: keep the cached-queue ranking (the prefix order, best at iid), but move to the front every sender whose WORST
relayed age over the other receivers (AgeMirror.table, scheduler information only) is >= D decision steps, the oldest
first (ties by the prefix rank).  D = infinity is exactly the prefix order.  At t = 0 every sender is unheard and ties
at the same age, so the order is the prefix ranking.
Capacities, prefix sets, the cap<c> rule, R = 0 and byte accounting are those of MusicDelivery (HETERO_v0 unchanged).
"""
from __future__ import annotations
import numpy as np
from models.marl_delivery_music import MusicDelivery, AgeMirror, NEVER, UNHEARD_AGE  # noqa: F401
from models.marl_hetero_selector import prefix_sets


class DeadlineDelivery(MusicDelivery):
    def __init__(self, D):
        super().__init__('prefix'); self.D = float(D)
        if not self.D > 0:
            raise ValueError(D)
        self.stats = dict(steps=0, steps_with_promotion=0, promoted=0)

    def worst_age(self, now):
        a = np.where(self.mirror.table > NEVER / 2, now - self.mirror.table, UNHEARD_AGE)
        np.fill_diagonal(a, -np.inf)                     # a receiver's own entry is not a relayed copy
        return a.max(0)                                  # column j: worst age of j over the receivers

    def __call__(self, env, seed, load, t):
        m = env.n_agents
        if t == 0 or self.mirror is None:
            self.mirror = AgeMirror(m)
        mode = self.mode
        if not (mode == 'prefix' or mode.startswith('cap')):
            raise ValueError(f'deadline orders support prefix / cap<c>, not {mode}')
        ctx = env.scheduler_context(); now = float(env._now())
        base = tuple(ctx.cached_queue_ranking()); rank = {j: r for r, j in enumerate(base)}
        w = self.worst_age(now); thr = self.D * float(env.action_interval) - 1e-6
        late = sorted([j for j in base if w[j] >= thr], key=lambda j: (-w[j], rank[j])) if t > 0 else []
        order = tuple(late) + tuple(j for j in base if j not in late)
        self.stats['steps'] += 1; self.stats['steps_with_promotion'] += int(bool(late)); self.stats['promoted'] += len(late)
        env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        sets = prefix_sets(order, K)
        if mode.startswith('cap'):
            head = set(order[:int(mode[3:])])
            sets = [frozenset(j for j in sets[i] if j in head) for i in range(m)]; env._k = {i: len(sets[i]) for i in range(m)}
        env.submit_profile([set(s) for s in sets], R=0)
        self.mirror.update(sets, now); self.last_order = order
        return sets
