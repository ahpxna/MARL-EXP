"""Sender-side payload COMPRESSION for the direction-2 diagnostic (29/09 22:4x; ledger L-128).

The sender quantises its own payload (phase elapsed, vehicles and waiting per approach) with a codebook fitted on
TRAINING traffic (`scripts/MARL_e3_payload_codebook.py`).  The receiver decodes bin representatives.  The phase itself
is kept exactly (9 values, 4 bits).  The quantisation acts on the encoded sender blocks, the same numbers the actor sees,
so any base adapter (default, freshonly) can be wrapped: `quantized(base_cls, book, L)`.
Diagnostic only.  Actors trained on raw payloads measure ROBUSTNESS to compression, not a trained compressed protocol.
"""
from __future__ import annotations
import numpy as np
from models.marl_comm_actor import N_PH, SCALE_P, SCALE_T

I_EL = 3 + N_PH                      # block index of phase_elapsed / SCALE_T
I_VEH = slice(4 + N_PH, 8 + N_PH)    # vehicles / SCALE_P
I_WAI = slice(8 + N_PH, 12 + N_PH)   # waiting / SCALE_P


def _q(x, field):
    e = np.asarray(field['edges'], float); r = np.asarray(field['reps'], float)
    k = np.clip(np.searchsorted(e, np.round(x), side='right') - 1, 0, len(e) - 1)
    return r[k]


def quantized(base_cls, book, L):
    cb = book['codebooks'][str(L)]

    class QuantAdapter(base_cls):
        def encode(self, view, variant='actual', rng=None):
            x = super().encode(view, variant, rng).copy()
            base = self.own_dim + self.m
            for k in range(self.m - 1):
                b = x[base + k * self.blk_dim: base + (k + 1) * self.blk_dim]
                if b[1] < 0.5:                                 # not heard: nothing was sent to quantise
                    continue
                b[I_EL] = _q(b[I_EL] * SCALE_T, cb['elapsed']) / SCALE_T
                b[I_VEH] = _q(b[I_VEH] * SCALE_P, cb['vehicles']) / SCALE_P
                b[I_WAI] = _q(b[I_WAI] * SCALE_P, cb['waiting']) / SCALE_P
            return x

    QuantAdapter.__name__ = f'Quant{L}{base_cls.__name__}'
    return QuantAdapter
