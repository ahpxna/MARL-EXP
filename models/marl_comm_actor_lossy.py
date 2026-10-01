"""PACKET LOSS on top of any adapter, for the P4 robustness diagnostic (30/09 09:2x; ledger L-155).

Each packet decoded THIS step (a fresh block) is lost independently with probability p.  The draw is deterministic in
(receiver, decision step, sender), so every arm sees the same losses.  A lost packet is treated like a stale one under the
fresh-only receiver: the block is not heard, and its dynamic part is zeroed (the static topology part is kept).  With the
fresh-only set receiver this means "this sender is absent this step".  Diagnostic only: the actors were trained without loss.
"""
from __future__ import annotations
import numpy as np

BLK_DYN = 21                       # fresh, heard, age, phase(9), elapsed, vehicles(4), waiting(4)


def lossy(base_cls, p):
    p = float(p)

    class LossyAdapter(base_cls):
        def encode(self, view, variant='actual', rng=None):
            x = super().encode(view, variant, rng).copy()
            if p <= 0:
                return x
            i = int(view.agent); base = self.own_dim + self.m
            for k in range(self.m - 1):
                j = k if k < i else k + 1
                b = x[base + k * self.blk_dim: base + (k + 1) * self.blk_dim]
                if b[0] > 0.5:
                    u = np.random.default_rng([i, int(view.decision_step), j, 0x10557]).random()
                    if u < p:
                        b[:BLK_DYN] = 0.0
            return x

    LossyAdapter.__name__ = f'Lossy{int(round(100 * p))}{base_cls.__name__}'
    return LossyAdapter
