"""RELAY v3: the v2 relay packet with a FIXED slot set per sender, for teams larger than nine (30/09 20:4x EDT; ledger L-186).

Why: the v2 layout carries every other agent (17 + 21 (m - 1) bits), which fits a 25 B packet only for m <= 9
(work/p13_conjectures/LeanMarlStatLayoutV1.relay_layout_bits).  For the 4x4 grid (m = 16) the packet keeps the SAME
185-bit layout: its sender's own summary plus 8 relay slots, assigned to the 8 agents nearest to the sender on the grid
(Manhattan distance, ties by agent index).  The slot set is fixed and public, so the slots stay positional (no id bits).
Agents outside a sender's slots reach a receiver through other senders (multi-hop).

Nothing else changes, and the code reuses the old code instead of copying it:
  * `make_slot_merge(slots)` filters what each decoded packet carries to its slots, then calls the UNCHANGED
    `models.marl_relay_v2.merge_views` (freshest copy per agent, 4-bit ages saturated at 14 steps, the receiver's own
    direct cache unrestricted);
  * `make_slot_mirror(slots)` returns a subclass of the UNCHANGED `models.marl_delivery_music.AgeMirror` whose update
    masks every decoded sender's table to its slots and then runs the parent update.  The evaluators' per-step check
    "mirror == merged views" therefore remains a real check of the two implementations against each other.
With slots = all other agents (every sender carries everyone, as in v2), both are identical to v2; on the 3x3 grid the 8
nearest agents ARE all others, so v3 reproduces the 3x3 rows exactly (parity test in ledger L-186).
"""
from __future__ import annotations
from dataclasses import replace
import numpy as np
from models.marl_relay_v2 import merge_views as _merge_v2, AGE_CAP_STEPS
from models.marl_delivery_music import AgeMirror, NEVER


def grid_coords(agent_ids):
    """(row, col) of 'intersection_r_c' ids, in the env's (sorted) agent order."""
    out = []
    for a in agent_ids:
        _, r, c = str(a).rsplit('_', 2)
        out.append((int(r), int(c)))
    return out


def nearest_slots(rows, cols, n_slots=8):
    """Slot sets for a rows x cols grid in row-major order (the env's sorted-id order for single-digit indices)."""
    coords = [(r, c) for r in range(1, rows + 1) for c in range(1, cols + 1)]
    m = len(coords); slots = {}
    for k in range(m):
        others = sorted((j for j in range(m) if j != k),
                        key=lambda j: (abs(coords[j][0] - coords[k][0]) + abs(coords[j][1] - coords[k][1]), j))
        slots[k] = frozenset(others[:n_slots])
    return slots


def make_slot_merge(slots):
    def merge_views(views, prev_views, t, interval, mode='age', cap=AGE_CAP_STEPS):
        if prev_views is None:
            return _merge_v2(views, None, t, interval, mode, cap)
        restricted = {}
        for k, pv in prev_views.items():
            keep = slots[k]
            restricted[k] = replace(pv, inbox=tuple(e for e in pv.inbox if e.sender in keep),
                                    cache=tuple(e for e in pv.cache if e.sender in keep))
        return _merge_v2(views, restricted, t, interval, mode, cap)
    return merge_views


def make_slot_mirror(slots):
    class SlotAgeMirror(AgeMirror):
        def update(self, sets, meas_time):
            masked = self.table.copy()
            for k in range(self.m):
                for j in range(self.m):
                    if j != k and j not in slots[k]:
                        masked[k, j] = NEVER
            self.table = masked
            super().update(sets, meas_time)
    return SlotAgeMirror
