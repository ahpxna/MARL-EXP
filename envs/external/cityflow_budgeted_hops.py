"""Budgeted CityFlow with a MULTI-HOP candidate message set (P3 extension, 2026-09-27).

Identical to :mod:`envs.external.cityflow_budgeted` (not edited), except that the
candidate senders of intersection ``i`` are all intersections within ``hops`` road hops,
not only the adjacent ones.  Every information-access rule of the base class is kept:
- the own sensor covers own incoming lanes only;
- messages arrive as bytes;
- absent senders are known only from the cache.

Messages from a 2-hop sender model direct V2I/backbone delivery with the same 25-byte
payload.

Why: the nesting-degree theorem (LeanMarlNestingDegreeGeneralV1) and the exhaustive
enumeration show that with m ≤ 6 candidates, one revision always suffices for the best nested
order.  The one-hop grid (m ≤ 4) therefore cannot exhibit a price of nesting at all.  A
multi-hop set gives m = 5..8 on a 3×3 grid and up to 10 inside a 4×4 grid.
"""
from __future__ import annotations

import dataclasses
import json
import os
from collections import deque
from pathlib import Path
from typing import Optional

from envs.external.cityflow_budgeted import BudgetedCityFlowEnv, BudgetTraceSpec


class BudgetedCityFlowEnvHops(BudgetedCityFlowEnv):
    """Base environment with candidate senders = intersections within `hops` hops."""

    def __init__(self, engine, roadnet: dict, *, hops: int = 2, **kw):
        if int(hops) < 1:
            raise ValueError("hops must be >= 1")
        self.hops = int(hops)
        super().__init__(engine, roadnet, **kw)

    def _parse_roadnet(self, roadnet, clearance_phase):
        super()._parse_roadnet(roadnet, clearance_phase)
        adj = self.neighbours  # one-hop adjacency from the base parser
        self.one_hop = adj
        multi = []
        for i in range(self.n_agents):
            dist = {i: 0}
            dq = deque([i])
            while dq:
                u = dq.popleft()
                if dist[u] == self.hops:
                    continue
                for v in adj[u]:
                    if v not in dist:
                        dist[v] = dist[u] + 1
                        dq.append(v)
            multi.append(tuple(sorted(v for v in dist if v != i)))
        self.neighbours = tuple(multi)
        self._topology = [dataclasses.replace(t, neighbours=self.neighbours[t.agent]) for t in self._topology]


def make_budgeted_grid_env_hops(scenario: dict, *, hops: int = 2, budget_spec: BudgetTraceSpec,
                                R: Optional[int], n_decisions: int, action_interval: int = 10,
                                delivery_delay: int = 0, mode: str = "deploy"):
    """Construct the multi-hop env on a scenario from make_grid_scenario.  Isolated runtime only."""
    if os.environ.get("CIG_EXTERNAL_RUNTIME_ACTIVE") != "1":
        raise RuntimeError("CityFlow construction attempted outside the managed external runtime")
    import cityflow
    cfg = scenario["files"]["config.json"]["path"]
    engine = cityflow.Engine(cfg, thread_num=1)
    roadnet = json.loads(Path(scenario["files"]["roadnet.json"]["path"]).read_text(encoding="utf-8"))
    return BudgetedCityFlowEnvHops(engine, roadnet, hops=hops, budget_spec=budget_spec, R=R,
                                   n_decisions=n_decisions, action_interval=action_interval,
                                   delivery_delay=delivery_delay, mode=mode)
