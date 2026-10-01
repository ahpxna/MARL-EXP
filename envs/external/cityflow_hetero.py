"""PROTOCOL_HETERO_v0 transport: one broadcast stream, heterogeneous receiver capacities.

Per decision step: commit a base order (before the reveal) -> reveal the capacity vector K
(k_i in 1..m-2, i.i.d. uniform, seeded) -> submit a per-receiver profile S (|S_i| = k_i,
i not in S_i, |S_i \\ P_i| <= R) -> transmit -> act.

Transmission: every packet in the accounted transmitted set T is encoded once (25 B).  Receiver i
decodes ONLY S_i: its cache is updated only for those packets; other transmitted packets are
not decoded by i.  The public scheduler, which is the broadcaster, caches every packet in T.
Bytes use models.marl_hetero_selector.profile_cost, the single cost function shared by every
method.  Zero delivery delay only; no airtime, loss or instruction latency model.
"""
from __future__ import annotations
import json, os
from pathlib import Path
import numpy as np

from envs.external.cityflow_budgeted import BudgetedCityFlowEnv, encode_payload, decode_payload
from envs.external.cityflow_broadcast import BroadcastCityFlowEnv
from models.marl_hetero_selector import prefix_sets, profile_cost, check_legal


class HeteroBroadcastEnv(BroadcastCityFlowEnv):
    def __init__(self, engine, roadnet, *, capacity_seed, **kw):
        if kw.get('delivery_delay', 0) != 0:
            raise ValueError('zero delivery delay only')
        BudgetedCityFlowEnv.__init__(self, engine, roadnet, **kw)   # broadcast neighbours via MRO
        self.capacity_seed = int(capacity_seed)

    def reset(self, budget_seed=0):
        views = BroadcastCityFlowEnv.reset(self, budget_seed)
        rng = np.random.default_rng(self.capacity_seed)
        self._trace = rng.integers(1, self.n_agents - 1, size=(self.n_decisions, self.n_agents))
        self._profile_cost = None
        return views

    def reveal_budget(self):
        return BudgetedCityFlowEnv.reveal_budget(self)

    def submit_broadcast(self, selected):
        raise RuntimeError('use submit_profile for the heterogeneous protocol')

    def submit_profile(self, sets, R=None, cap=None):
        self._require('revise')
        m = self.n_agents
        K = [self._k[i] for i in range(m)]
        sets = [frozenset(int(j) for j in sets[i]) for i in range(m)]
        check_legal(self._global_ranking, K, sets, R=R, cap=cap)
        P = prefix_sets(self._global_ranking, K)
        self._final = {i: tuple(sorted(sets[i])) for i in range(m)}
        self._revisions = {i: len(sets[i] - P[i]) for i in range(m)}
        self._profile_cost = profile_cost(self._global_ranking, K, sets)
        self._stage = 'transmit'
        return self._profile_cost[0]

    def transmit(self):
        self._require('transmit')
        nbytes, desc, T = self._profile_cost
        rec = dict(payload_bytes=0, request_bytes=nbytes, messages=0, clipped_fields=0)
        payloads = {}
        for j in sorted(T):
            data, clipped = encode_payload(self._summary(j))
            payloads[j] = decode_payload(data)
            rec['payload_bytes'] += len(data); rec['messages'] += 1; rec['clipped_fields'] += clipped
            self._scheduler_cache[j] = payloads[j]
        rec['request_bytes'] = nbytes - rec['payload_bytes']          # accounted control bytes
        self._delivered_now = [set() for _ in range(self.n_agents)]
        for i in range(self.n_agents):
            for j in self._final[i]:
                p = payloads[j]
                self._cache[i][j] = (p, p.measured_at, self._t)
                self._delivered_now[i].add(j)
        for key, value in rec.items():
            self._totals[key] += value
        self._comm_record = dict(rec, description=desc, accounted_bytes=nbytes)
        self._stage = 'act'
        return self.views()

    def step(self, actions):
        order = self._global_ranking; final = self._final
        result = BudgetedCityFlowEnv.step(self, actions)
        result[2]['base_order'] = list(order)
        result[2]['profile'] = [list(final[i]) for i in range(self.n_agents)]
        self._global_ranking = self._global_final = None
        return result


def make_hetero_env(scenario, *, budget_spec, n_decisions, capacity_seed, action_interval=10,
                    mode='deploy'):
    if os.environ.get('CIG_EXTERNAL_RUNTIME_ACTIVE') != '1':
        raise RuntimeError('use the existing managed external runtime')
    import cityflow
    engine = cityflow.Engine(scenario['files']['config.json']['path'], thread_num=1)
    roadnet = json.loads(Path(scenario['files']['roadnet.json']['path']).read_text())
    return HeteroBroadcastEnv(engine, roadnet, budget_spec=budget_spec, R=None, n_decisions=n_decisions,
                              action_interval=action_interval, mode=mode, capacity_seed=capacity_seed)
