"""SAMPLED leaf walk for BudgetedCityFlowEnv.check_access_invariants, for TRAINING runs only (29/09 23:4x; ledger L-136).

Profile (29/09 23:2x): the per-step access audit costs about 30 % of a training iteration (4 iterations: 7 s with it, 5 s
without; identical training numbers).  Almost all of that is check 7, the recursive walk over every leaf of every view
(`iter_view_leaves`, 17.8 M calls in 6 iterations).  Checks 1-6 are cheap.  This module keeps checks 1-6 at EVERY call
and runs the leaf walk (non-data leaves, writeable arrays) only when the env's decision index t satisfies
t % every == 0 (t = 0 included).  The view types are built by the same code at every step, so a sampled walk still
catches a leaking type in the first episode.
The user approved this trade (23:4x).  It applies only to trainings launched with it, never to evaluation: every reported
number comes from evaluators that call the full, unpatched audit at every step.
The body below is copied from envs/external/cityflow_budgeted.py (check_access_invariants, lines 689-713 at sha256 of
that file recorded by the trainer's SOURCES); only the `if walk:` guard is new.
"""
from __future__ import annotations
from typing import List, Mapping
import numpy as np
import envs.external.cityflow_budgeted as CB

STATE = {'every': 1, 'installed': False, 'calls': 0, 'walks': 0}


def _sampled_check(self, views: Mapping[int, 'CB.AgentView']) -> List[str]:
    """Checks 1-6 of the original at every call; check 7 (leaf walk) at decision steps t % every == 0."""
    bad = []
    now = self._now()
    walk = (int(self._t) % STATE['every'] == 0)
    STATE['calls'] += 1; STATE['walks'] += int(walk)
    for i, v in views.items():
        if set(e.sender for e in v.inbox) - set(self.neighbours[i]):
            bad.append(f"agent {i}: inbox sender outside N(i)")
        if v.stage != "act" and v.inbox:
            bad.append(f"agent {i}: inbox before transmission")
        if v.stage == "act" and self.delivery_delay == 0 and self._final is not None:
            if not set(e.sender for e in v.inbox) <= set(self._final[i]):
                bad.append(f"agent {i}: inbox sender not in its final set")
        for e in v.cache:
            if e.measured_at >= now and e.delivered_step != self._t:
                bad.append(f"agent {i}: cache entry from {e.sender} is not older than now")
            if v.stage == "act" and e.sender in self._delivered_now[i]:
                bad.append(f"agent {i}: delivered sender {e.sender} listed as cache")
        if v.stage in ("rank", "reveal") and v.budget is not None:
            bad.append(f"agent {i}: budget visible before the reveal")
        if walk:
            for path, leaf in CB.iter_view_leaves(v):
                if not isinstance(leaf, (int, float, str, bool, type(None), np.ndarray, np.floating, np.integer)):
                    bad.append(f"agent {i}: non-data leaf at {path}: {type(leaf).__name__}")
                if isinstance(leaf, np.ndarray) and leaf.flags.writeable:
                    bad.append(f"agent {i}: writeable array at {path}")
    return bad


def install(every: int):
    """Replace the audit on the class (every >= 2), or leave the original untouched (every = 1)."""
    every = int(every)
    if every < 1:
        raise ValueError('every must be >= 1')
    STATE['every'] = every
    if every > 1:
        CB.BudgetedCityFlowEnv.check_access_invariants = _sampled_check
        STATE['installed'] = True
    return STATE
