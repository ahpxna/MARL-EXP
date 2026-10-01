"""Global broadcast adapter for the cheap MARL screening experiment.

One grant k selects k SENDERS for the whole network. Every other agent and the
public scheduler receives each selected 25-byte packet. The scheduler sees only
previously paid packets, never the collection of fresh agent observations.
This first screening adapter supports zero delivery delay only. It does not
model wall-clock computation as traffic time and makes no latency-advantage claim.
The historical receiver-budget adapter is kept unchanged.
"""
from __future__ import annotations
import dataclasses
import hashlib
import json
import os
import struct
from pathlib import Path

from envs.external.cityflow_budgeted import (
    BudgetedCityFlowEnv, BudgetTraceSpec, MessagePayload, encode_payload, decode_payload,
)


@dataclasses.dataclass(frozen=True)
class SchedulerContext:
    decision_step: int
    sim_time: float
    # Only payloads actually broadcast in earlier steps, immutable data.
    packets: tuple[MessagePayload | None, ...]

    def features(self):
        out = [self.sim_time / 1000.0]
        for p in self.packets:
            if p is None:
                out.extend([0.0] * 12)
            else:
                out.extend([1.0, (self.sim_time-p.measured_at)/100.0,
                            p.phase/10.0, p.phase_elapsed/100.0])
                out.extend(x/100.0 for x in p.vehicles)
                out.extend(x/100.0 for x in p.waiting)
        return out

    def cached_queue_ranking(self):
        return tuple(sorted(range(len(self.packets)), key=lambda j:
            (0, 0, j) if self.packets[j] is None else
            (1, -sum(self.packets[j].waiting), j)))


class BroadcastCityFlowEnv(BudgetedCityFlowEnv):
    def __init__(self, engine, roadnet, **kw):
        if kw.get('delivery_delay', 0) != 0:
            raise ValueError('screening adapter supports zero delivery delay only')
        if kw['budget_spec'].per_agent:
            raise ValueError('global broadcast requires one shared budget trace')
        super().__init__(engine, roadnet, **kw)

    def _parse_roadnet(self, roadnet, clearance_phase):
        super()._parse_roadnet(roadnet, clearance_phase)
        self.physical_neighbours = self.neighbours
        self.neighbours = tuple(tuple(j for j in range(self.n_agents) if j != i)
                                for i in range(self.n_agents))
        self._topology = [dataclasses.replace(t, neighbours=self.neighbours[t.agent])
                          for t in self._topology]

    def reset(self, budget_seed=0):
        self._scheduler_cache = {}
        self._global_ranking = self._global_final = None
        result = super().reset(budget_seed)
        if (self._trace < 0).any() or (self._trace > self.n_agents).any():
            raise ValueError('global grant must lie in [0, number of agents]')
        return result

    def scheduler_context(self):
        # No _sensor(), _summary(), or views() call here.
        return SchedulerContext(self._t, self._now(),
            tuple(self._scheduler_cache.get(j) for j in range(self.n_agents)))

    def commit_rankings(self, rankings):
        raise RuntimeError('use commit_global_ranking for the broadcast protocol')

    def commit_global_ranking(self, ranking):
        self._require('rank')
        ranking = tuple(ranking)
        if any(type(j) is not int for j in ranking) or sorted(ranking) != list(range(self.n_agents)):
            raise ValueError('global ranking must be a permutation of all sender IDs')
        self._global_ranking = ranking
        self._rankings = {i: tuple(j for j in ranking if j != i) for i in range(self.n_agents)}
        digest = hashlib.sha256(json.dumps([self._t, ranking]).encode()).hexdigest()
        self.commit_hashes.append(digest)
        self._stage = 'reveal'
        return digest

    def reveal_budget(self):
        values = super().reveal_budget()
        if len(set(values.values())) != 1:
            raise RuntimeError('inconsistent shared grant')
        return values[0]

    def submit_final_sets(self, final_sets):
        raise RuntimeError('use submit_broadcast for the broadcast protocol')

    def submit_broadcast(self, selected):
        self._require('revise')
        selected = tuple(selected)
        k = self._k[0]
        if (any(type(j) is not int for j in selected) or len(set(selected)) != len(selected)
                or not set(selected) <= set(range(self.n_agents)) or len(selected) != k):
            raise ValueError('broadcast must contain exactly k distinct valid senders')
        replacements = len(set(selected)-set(self._global_ranking[:k]))
        if self.R is not None and replacements > self.R:
            raise ValueError('broadcast exceeds revision radius')
        self._global_final = tuple(sorted(selected))
        self._final = {i: tuple(j for j in self._global_final if j != i) for i in range(self.n_agents)}
        # Base step sums this map. A global replacement is counted ONCE.
        self._revisions = {i: replacements if i == 0 else 0 for i in range(self.n_agents)}
        self._stage = 'transmit'
        return replacements

    def transmit(self):
        self._require('transmit')
        # A concrete ideal-broadcast schedule: uint32 decision index + sender bitset.
        mask = sum(1 << j for j in self._global_final)
        schedule = struct.pack('<I', self._t) + mask.to_bytes((self.n_agents+7)//8, 'little')
        rec = dict(payload_bytes=0, request_bytes=len(schedule), messages=0, clipped_fields=0)
        self._delivered_now = [set() for _ in range(self.n_agents)]
        for j in self._global_final:
            data, clipped = encode_payload(self._summary(j))
            p = decode_payload(data)
            rec['payload_bytes'] += len(data)
            rec['messages'] += 1
            rec['clipped_fields'] += clipped
            self._scheduler_cache[j] = p
            for i in range(self.n_agents):
                if i != j:
                    self._cache[i][j] = (p, p.measured_at, self._t)
                    self._delivered_now[i].add(j)
        for key, value in rec.items():
            self._totals[key] += value
        self._comm_record = rec
        self._stage = 'act'
        return self.views()

    def step(self, actions):
        selected, ranking = self._global_final, self._global_ranking
        result = super().step(actions)
        result[2]['global_selected'] = list(selected)
        result[2]['global_ranking'] = list(ranking)
        self._global_ranking = self._global_final = None
        return result

    def counterfactual_broadcast_views(self, selected):
        self._require('revise')
        selected = tuple(selected)
        if (len(set(selected)) != len(selected) or
                not set(selected) <= set(range(self.n_agents))):
            raise ValueError('invalid hypothetical broadcast')
        # Diagnostic only. Each receiver changes together under the SAME S.
        return {i: dataclasses.replace(
            self.counterfactual_view(i, [j for j in selected if j != i]),
            stage='act', budget=len(selected),
            final_set=tuple(j for j in selected if j != i)) for i in range(self.n_agents)}


def make_broadcast_env(scenario, *, budget_spec: BudgetTraceSpec, n_decisions,
                       action_interval=10, R=None, mode='deploy'):
    if os.environ.get('CIG_EXTERNAL_RUNTIME_ACTIVE') != '1':
        raise RuntimeError('use the existing managed external runtime')
    import cityflow
    engine = cityflow.Engine(scenario['files']['config.json']['path'], thread_num=1)
    roadnet = json.loads(Path(scenario['files']['roadnet.json']['path']).read_text())
    return BroadcastCityFlowEnv(engine, roadnet, budget_spec=budget_spec, R=R,
                               n_decisions=n_decisions, action_interval=action_interval, mode=mode)
