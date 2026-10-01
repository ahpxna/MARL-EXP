"""Broadcast orders v2 (30/09 15:3x EDT; ledger L-176): models/marl_delivery_music.py (imported unchanged) plus the Paper-A
REPAIR mixture 'mix<beta>': at every decision step, with probability beta the stream head rotates (agefirst), otherwise the
cached-queue ranking (the frozen surrogate) is used.  The coin is deterministic in (traffic seed, headway, step), so every
actor sees the same mixture on the same episode.  beta = 0 is exactly the prefix order and beta = 1 exactly agefirst.
Capacities, prefix sets, the cap<c> rule and byte accounting are those of MusicDelivery.
"""
from __future__ import annotations
import numpy as np
from models.marl_delivery_music import MusicDelivery, AgeMirror, NEVER  # noqa: F401 (re-exported)


class MixDelivery(MusicDelivery):
    def __init__(self, beta):
        super().__init__('prefix'); self.beta = float(beta)
        if not 0.0 <= self.beta <= 1.0:
            raise ValueError(beta)
        self.rotated = 0; self.steps = 0

    def __call__(self, env, seed, load, t):
        u = np.random.default_rng([int(seed), int(round(float(load) * 10)), int(t), 0xBE7A]).random()
        self.order = 'agefirst' if u < self.beta else 'prefix'
        self.rotated += int(self.order == 'agefirst'); self.steps += 1
        return super().__call__(env, seed, load, t)
