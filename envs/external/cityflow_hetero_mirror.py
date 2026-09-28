"""HeteroBroadcastEnv plus the scheduler-owned receiver-cache mirror (legal history feature).

A subclass in a NEW file, so cityflow_hetero.py and the hashes recorded by earlier artifacts
are unchanged.  The mirror is updated in transmit() only from the payloads the scheduler itself
broadcast this step (its own cache entries for the transmitted set) and the submitted profile.
mirror_features() reads only the mirror and the public clock.  verify_mirror() compares the
mirror with the true receiver caches: a DIAGNOSTIC assertion, never a feature.
"""
from __future__ import annotations
from envs.external.cityflow_hetero import HeteroBroadcastEnv, make_hetero_env
from models.marl_receiver_mirror import ReceiverMirror


class HeteroMirrorEnv(HeteroBroadcastEnv):
    def reset(self, budget_seed=0):
        views = super().reset(budget_seed)
        self.mirror = ReceiverMirror(self.n_agents)
        return views

    def transmit(self):
        views = super().transmit()
        T = self._profile_cost[2]
        payloads = {j: self._scheduler_cache[j] for j in T}
        self.mirror.update(self._t, payloads, [self._final[i] for i in range(self.n_agents)])
        return views

    def mirror_features(self):
        return self.mirror.features(self._now())

    def verify_mirror(self):
        """Diagnostic only: the mirror must equal every receiver's true cache."""
        for i in range(self.n_agents):
            mine = {j: (e[0], e[1], e[2]) for j, e in self.mirror.cache[i].items()}
            true = {j: (e[0], e[1], e[2]) for j, e in self._cache[i].items()}
            if mine != true:
                raise AssertionError(f'receiver {i}: mirror {sorted(mine)} != cache {sorted(true)}')
        return True


def make_hetero_mirror_env(scenario, **kw):
    env = make_hetero_env(scenario, **kw)
    env.__class__ = HeteroMirrorEnv
    return env
