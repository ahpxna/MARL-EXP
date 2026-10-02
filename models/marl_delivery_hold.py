"""HOLD-r age-first order (01/10/2026 19:2x EDT; PROTOCOL_E3_HOLD_DOSE_20261001.md): the age-first ranking of
models/marl_delivery_music.MusicDelivery('agefirst') is recomputed only every r steps and the committed order is reused in
between.  Same capacities, prefix sets, packets and byte accounting; only the schedule changes (a dose manipulation of the
relayed-copy age tail at fixed K and fixed fresh count).  r = 1 is exactly MusicDelivery('agefirst') with mode prefix.
Scheduler information only (the previous committed order and the packets' measurement times)."""
from __future__ import annotations
from models.marl_hetero_selector import prefix_sets
from models.marl_delivery_music import MusicDelivery, AgeMirror


class HoldDelivery(MusicDelivery):
    def __init__(self, r):
        super().__init__('agefirst'); self.r = int(r)
        if self.r < 1:
            raise ValueError(r)

    def __call__(self, env, seed, load, t):
        m = env.n_agents
        if t == 0 or self.mirror is None:
            self.mirror = AgeMirror(m)
        if self.mode != 'prefix':
            raise ValueError('hold orders support mode prefix only')
        now = float(env._now())
        if t % self.r == 0 or self.last_order is None:
            P = env.scheduler_context().packets
            key = lambda j: (0, j) if P[j] is None else (1, P[j].measured_at, j)
            order = tuple(sorted(range(m), key=key))
        else:
            order = self.last_order
        env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        sets = prefix_sets(order, K)
        env.submit_profile([set(s) for s in sets], R=0)
        self.mirror.update(sets, now); self.last_order = order
        return sets
