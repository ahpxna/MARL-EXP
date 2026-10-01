"""CommAdapter with the NON-NEIGHBOUR sender blocks masked (29/09; ledger L-105 follow-up).

Identical to models.marl_comm_actor.CommAdapter (same schema and dimension, so checkpoints load unchanged), except that
encode() zeroes the whole per-sender block of every agent j that is not a PHYSICAL neighbour of the receiver (no road
between them in either direction; read from the public topology through the adapter's own static features).  The
actor then sees only its physical neighbours' messages: a structural prior, not a delivery rule.
"""
from __future__ import annotations
import numpy as np
from models.marl_comm_actor import CommAdapter


class MaskedCommAdapter(CommAdapter):
    def __init__(self, topos, n_dec, interval=10):
        super().__init__(topos, n_dec, interval)
        self.adjacent = {(i, j): bool(self.static[(i, j)].any()) for (i, j) in self.static}

    def encode(self, view, variant='actual', rng=None):
        x = super().encode(view, variant, rng).copy(); i = view.agent; base = self.own_dim + self.m; k = 0
        for j in range(self.m):
            if j == i:
                continue
            if not self.adjacent[(i, j)]:
                x[base + k * self.blk_dim: base + (k + 1) * self.blk_dim] = 0.0
            k += 1
        return x
