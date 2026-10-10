#!/usr/bin/env python3
"""Emulator variants for E6 / E3 (03/10/2026 23:1x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003).
ExactV extends scripts/MARL_e3_p2_nesting_replay.Exact (not edited):
  * packet_only: a copy of sender j is usable only if THIS receiver once received it at an age < 14 decision steps (direct
    packets: age 0; a relayed copy: the 4-bit age field of the 25 B packet, saturated at 14) — only then is its measurement
    time recoverable from packets.  Copies first and only seen at age >= 14 are ambiguous and treated as missing.
  * rule for a missing K1 entry: 'older' (Exact's rule: most recent usable copy measured before m*, true age), 'absent'
    (never heard), 'fresh' (the receiver's current merged-view copy of j, with its own age).
Counters: entries, missing, substituted, ambiguous (entries whose exact copy exists but only at reception age >= 14).
With packet_only=False and rule='older' ExactV reproduces Exact exactly (self-check in the evaluator)."""
from __future__ import annotations
from dataclasses import replace
import scripts.MARL_e3_p2_nesting_replay as NR
import models.marl_delivery_music as MUSIC
from models.marl_relay_v2 import AGE_CAP_STEPS
from envs.external.cityflow_budgeted import CacheEntry


class ExactV(NR.Exact):
    def __init__(self, m, iv, rule='older', packet_only=False):
        super().__init__(m, iv); self.rule = rule; self.packet_only = packet_only
        self.minage = [dict() for _ in range(m)]; self.cnt = dict(entries=0, missing=0, substituted=0, ambiguous=0, fresh=0, absent=0)

    def _age(self, now, ms):
        return int(round((float(now) - float(ms)) / self.iv))

    def observe(self, views, prev_actual):
        super().observe(views, prev_actual)
        for i in range(self.m):
            now = float(views[i].sim_time)
            for e in views[i].inbox:
                k = (e.sender, float(e.measured_at)); self.minage[i][k] = 0
                if prev_actual is not None:
                    pk = prev_actual[e.sender]
                    for c in tuple(pk.inbox) + tuple(pk.cache):
                        if c.sender != i and (self.slots is None or c.sender in self.slots[e.sender]):
                            kc = (c.sender, float(c.measured_at)); a = self._age(now, c.measured_at)
                            self.minage[i][kc] = min(self.minage[i].get(kc, 10 ** 9), a)

    def usable(self, i, key):
        return key in self.seen[i] and (not self.packet_only or self.minage[i].get(key, 10 ** 9) < AGE_CAP_STEPS)

    def views(self, mv, t, now):
        self.legacy.step(now); out = {}; tab = self.legacy.mirror.table
        for i in range(self.m):
            ents = []; cur = {e.sender: e for e in mv[i].inbox}
            for j in range(self.m):
                ms = tab[i, j]
                if j == i or ms <= MUSIC.NEVER / 2:
                    continue
                self.cnt['entries'] += 1; key = (j, float(ms))
                if key in self.seen[i] and self.minage[i].get(key, 10 ** 9) >= AGE_CAP_STEPS:
                    self.cnt['ambiguous'] += 1
                if self.usable(i, key):
                    p = self.seen[i][key]
                else:
                    self.cnt['missing'] += 1
                    if self.rule == 'absent':
                        self.cnt['absent'] += 1; continue
                    if self.rule == 'fresh':
                        if j in cur:
                            ents.append(cur[j]); self.cnt['fresh'] += 1
                        continue
                    olds = [k for k in self.seen[i] if k[0] == j and k[1] < ms and self.usable(i, k)]
                    if not olds:
                        continue
                    ms = max(olds)[1]; p = self.seen[i][(j, ms)]; self.cnt['substituted'] += 1
                age = 0.0 if ms == now else min(AGE_CAP_STEPS, int(round((now - ms) / self.iv))) * self.iv
                ents.append(CacheEntry(j, p, ms, age, int(t)))
            out[i] = replace(mv[i], inbox=tuple(ents), cache=())
        return out
