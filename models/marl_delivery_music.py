"""MUSIC-THEORY broadcast orders for the relay method (30/09 13:3x EDT; ledger L-168).

Why: under PROTOCOL_HETERO_v0 a receiver decodes a PREFIX of one broadcast stream (its first K_i packets), and with relay
packets (models/marl_relay.py) each packet carries its sender's fresh summary AND the sender's whole table.  The stream
position therefore plays two roles:
  * position 1 is decoded by EVERY receiver (K_i >= 1), like the BASS line that every player of an ensemble hears and
    that fixes the harmony: whoever sits there decides which table everybody gets;
  * the other positions are heard only by receivers with larger K, like the upper voices of an arrangement that must
    sound complete for an ensemble of any size; they inject fresh summaries in turn, like a HOCKET (voices alternate).
The default order (cached-queue ranking) ignores both roles: the same congested senders stay at the head, and the others'
summaries go unbroadcast for many steps (the age tail found by scripts/MARL_e3_relay_age_diag.py, L-164).
Orders here:
  prefix    the cached-queue ranking (exactly MARL_e3_actor_train_delivery_v7.deliver with mode prefix / cap<c>);
  agefirst  oldest last-broadcast first (the order of models/marl_delivery_agefirst.py), BUT with the cap<c> rule applied
            (deliver_agefirst ignores the delivery mode, so cap4 rows run through it are uncapped: ledger L-168);
  bass      position 1 = the agent whose relay table is FRESHEST (least total age over the other agents), the rest by
            agefirst.
Information access: the bass rule needs every agent's relay table.  Tables are a deterministic function of the past
orders, the revealed capacities, the submitted sets and the packets' measurement times, all of which the scheduler
already holds (the mirror).  AgeMirror replays that function from those records only; the evaluator checks at every
step that it equals the merged views' measurement times, so the rule provably uses scheduler information only.
Capacities, prefix sets, R and byte accounting are those of the prefix rule; HETERO_v0 is unchanged.
"""
from __future__ import annotations
import numpy as np
from models.marl_hetero_selector import prefix_sets

NEVER = -1e18
UNHEARD_AGE = 1e4          # seconds charged for an agent a table has never held


class AgeMirror:
    """Scheduler-side replica of the relay tables: table[i, j] = measurement time of the freshest copy of j in i's merged
    view (models/marl_relay.merge_views, mode age); cache[i, j] = last DIRECT decode of j by i."""

    def __init__(self, m):
        self.m = m; self.cache = np.full((m, m), NEVER); self.table = np.full((m, m), NEVER)

    def update(self, sets, meas_time):
        m = self.m; new = np.full((m, m), NEVER)
        for i in range(m):
            best = self.cache[i].copy()
            for k in sets[i]:
                best = np.maximum(best, self.table[k])
            for k in sets[i]:
                best[k] = meas_time
            best[i] = NEVER; new[i] = best
        for i in range(m):
            for k in sets[i]:
                self.cache[i, k] = meas_time
        self.table = new

    def staleness(self, now):
        a = np.where(self.table > NEVER / 2, now - self.table, UNHEARD_AGE)
        np.fill_diagonal(a, 0.0)
        return a.sum(1)


class MusicDelivery:
    """Drop-in for MARL_e3_actor_train_delivery_v7.deliver(env, seed, load, t) with a delivery mode (prefix / cap<c>)
    and an order (prefix / agefirst / bass).  Call reset() at the start of every episode (done automatically at t == 0)."""

    def __init__(self, order):
        if order not in ('prefix', 'agefirst', 'bass'):
            raise ValueError(order)
        self.order = order; self.mode = 'prefix'; self.mirror = None; self.last_order = None

    def __call__(self, env, seed, load, t):
        m = env.n_agents
        if t == 0 or self.mirror is None:
            self.mirror = AgeMirror(m)
        mode = self.mode
        if not (mode == 'prefix' or mode.startswith('cap')):
            raise ValueError(f'music orders support prefix / cap<c>, not {mode}')
        ctx = env.scheduler_context(); now = float(env._now())
        if self.order == 'prefix':
            order = tuple(ctx.cached_queue_ranking())
        else:
            P = ctx.packets
            key = lambda j: (0, j) if P[j] is None else (1, P[j].measured_at, j)
            order = tuple(sorted(range(m), key=key))
            if self.order == 'bass' and t > 0:
                st = self.mirror.staleness(now)
                b = min(range(m), key=lambda j: (st[j], key(j)))
                order = (b,) + tuple(j for j in order if j != b)
        env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        sets = prefix_sets(order, K)
        if mode.startswith('cap'):
            head = set(order[:int(mode[3:])])
            sets = [frozenset(j for j in sets[i] if j in head) for i in range(m)]; env._k = {i: len(sets[i]) for i in range(m)}
        env.submit_profile([set(s) for s in sets], R=0)
        self.mirror.update(sets, now); self.last_order = order
        return sets
