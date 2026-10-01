"""Scheduler-owned mirror of every receiver's packet cache, from the PUBLIC event history only.

MARL_SCOPE_AFTER_CHEAP_TESTS §"A concrete omission": under the heterogeneous transport each
receiver keeps its own, possibly OLD, version of each sender's packet, and MP2 acts on it.  The
scheduler already knows every payload it transmitted and every profile it submitted, so in the
loss-free, zero-delay protocol it can reconstruct each receiver's cache without new
communication.  This class does exactly that and nothing else: update() consumes (step,
decoded transmitted payloads, submitted profile); features() reads only the mirror and the
public time.  No sensor, summary, view or simulator call is possible from here.
"""
from __future__ import annotations
from typing import Dict, Mapping, Sequence


class ReceiverMirror:
    def __init__(self, m: int):
        self.m = m
        self.reset()

    def reset(self):
        self.cache: list[Dict[int, tuple]] = [dict() for _ in range(self.m)]

    def update(self, step: int, payloads: Mapping[int, object], profile: Sequence[Sequence[int]]):
        """payloads: sender -> decoded payload actually transmitted; profile[i]: senders i decodes."""
        for i in range(self.m):
            for j in profile[i]:
                if j not in payloads:
                    raise ValueError(f'receiver {i} decodes {j}, which was not transmitted')
                p = payloads[j]
                self.cache[i][j] = (p, int(p.measured_at), int(step))

    def entry(self, i: int, j: int):
        return self.cache[i].get(j)

    @staticmethod
    def pair_features(entry, now: float):
        if entry is None:
            return [0.0] * 12
        p, measured, _ = entry
        return ([1.0, (now - measured) / 100.0, p.phase / 10.0, p.phase_elapsed / 100.0]
                + [x / 100.0 for x in p.vehicles] + [x / 100.0 for x in p.waiting])

    def features(self, now: float):
        """m*(m-1) receiver-sender blocks of 12: present, age, phase, elapsed, vehicles[4], waiting[4]."""
        out = []
        for i in range(self.m):
            for j in range(self.m):
                if j != i:
                    out.extend(self.pair_features(self.cache[i].get(j), now))
        return out
