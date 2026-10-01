"""Broadcast orders v4 (30/09 19:2x EDT; ledger L-181): the DOMINANT-KNOWER ('hub') head.

Why (the math of L-181): decoded sets are prefixes of ONE order, so they are nested.  The receiver with the largest
capacity at step t-1 decoded a superset of every other receiver's direct set (up to the self-skip), and every receiver
decodes the head.  Putting last step's largest-capacity receiver at the head therefore gives every receiver, one hop
later, what the best-informed receiver knew.  In a traffic-free replica this cuts relayed ages sharply when capacities
are heterogeneous (one rich receiver, the rest K = 1).  It is near-neutral under the iid / low capacities of E3, where
the age-first head already has a random, moderately large capacity.
Rule 'hub': head = argmax_i K_i(t-1), ties by the age-first key; the rest of the stream is age-first; at t = 0 the order
is age-first.  Information: the capacities revealed at t-1 (the scheduler receives them from reveal_budget).
Capacities, prefix sets, the cap<c> rule, R = 0 and byte accounting are those of MusicDelivery (HETERO_v0 unchanged).
"""
from __future__ import annotations
from models.marl_delivery_music import MusicDelivery, AgeMirror, NEVER  # noqa: F401
from models.marl_hetero_selector import prefix_sets


class HubDelivery(MusicDelivery):
    def __init__(self):
        super().__init__('agefirst'); self.lastK = None; self.stats = dict(steps=0, hub_was_agefirst_head=0)

    def __call__(self, env, seed, load, t):
        m = env.n_agents
        if t == 0 or self.mirror is None:
            self.mirror = AgeMirror(m); self.lastK = None
        mode = self.mode
        if not (mode == 'prefix' or mode.startswith('cap')):
            raise ValueError(f'hub order supports prefix / cap<c>, not {mode}')
        ctx = env.scheduler_context(); now = float(env._now())
        P = ctx.packets
        key = lambda j: (0, j) if P[j] is None else (1, P[j].measured_at, j)
        order = tuple(sorted(range(m), key=key))
        if self.lastK is not None:
            b = min(range(m), key=lambda j: (-self.lastK[j], key(j)))
            self.stats['hub_was_agefirst_head'] += int(b == order[0])
            order = (b,) + tuple(j for j in order if j != b)
        self.stats['steps'] += 1
        env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        sets = prefix_sets(order, K)
        if mode.startswith('cap'):
            head = set(order[:int(mode[3:])])
            sets = [frozenset(j for j in sets[i] if j in head) for i in range(m)]; env._k = {i: len(sets[i]) for i in range(m)}
        env.submit_profile([set(s) for s in sets], R=0)
        self.mirror.update(sets, now); self.last_order = order; self.lastK = K
        return sets
