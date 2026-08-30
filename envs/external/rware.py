"""Robotic Warehouse adapter for CIG-AMF."""
from __future__ import annotations
import copy
import numpy as np

from envs.external_contract import BenchmarkCapabilities
from envs.external.common import ExternalPopulationMixin, pad_observations


class RWARECIGEnvironment(ExternalPopulationMixin):
    capabilities = BenchmarkCapabilities("RWARE", True, True, True, True, False, False, False)

    def __init__(self, warehouse, observation_width=192, max_steps=60):
        self.raw_env = warehouse
        self.max_steps = max(1, int(max_steps))
        self.n_agents = int(warehouse.n_agents)
        self.max_action_dim = 5
        self.obs_dim = int(observation_width)
        self._obs = [np.zeros(self.obs_dim, dtype=np.float32) for _ in range(self.n_agents)]
        self._finish_init()

    def reset(self, seed=None):
        result = self.raw_env.reset(seed=seed)
        observations = result[0] if isinstance(result, tuple) else result
        self._obs = pad_observations(observations, self.obs_dim)
        self.last_requested_actions = [0] * self.n_agents
        self.last_executed_actions = [0] * self.n_agents
        self.last_actions = list(self.last_executed_actions)
        return self._obs

    def step(self, actions):
        requested = [int(a) for a in actions]
        result = self.raw_env.step(requested)
        observations, rewards, terminated, truncated, info = result
        self._obs = pad_observations(observations, self.obs_dim)
        # The pinned RWARE resolver leaves each agent.req_action at the
        # post-conflict command (failed movement requests are rewritten to
        # NOOP).  This is an execution/resolution receipt, distinct from the
        # request tuple and from whether the state physically changed.
        resolved = []
        for idx, agent in enumerate(self.raw_env.agents):
            action = getattr(agent, "req_action", None)
            value = getattr(action, "value", action)
            if value is None:
                raise RuntimeError(
                    f"RWARE did not expose a post-resolution action receipt for agent {idx}"
                )
            resolved.append(int(value))
        self.last_requested_actions = requested
        self.last_executed_actions = resolved
        # Generic clone-state intervention code consumes last_actions as the
        # trusted execution receipt, so it must not contain the request tuple.
        self.last_actions = list(resolved)
        return self._obs, [float(x) for x in rewards], bool(terminated or truncated), dict(info)

    def valid_action_mask(self, agent):
        del agent
        return np.ones((self.max_action_dim,), dtype=bool)

    def relation_features(self, ego, neighbour):
        a = self.raw_env.agents[int(ego)]
        b = self.raw_env.agents[int(neighbour)]
        h, w = self.raw_env.grid_size
        dx = (float(b.x) - float(a.x)) / max(1.0, float(w - 1))
        dy = (float(b.y) - float(a.y)) / max(1.0, float(h - 1))
        manhattan = (abs(float(b.x) - float(a.x)) + abs(float(b.y) - float(a.y))) / max(1.0, float(h + w - 2))
        same_axis = float(a.x == b.x or a.y == b.y)
        carrying = float(getattr(b, "carrying_shelf", None) is not None)
        heading_match = float(getattr(a, "dir", None) == getattr(b, "dir", None))
        return np.asarray([dx, dy, manhattan, same_axis, carrying, heading_match], dtype=np.float32)

    def clone_state(self):
        return (
            copy.deepcopy(self.raw_env),
            copy.deepcopy(self._obs),
            list(self.last_actions),
            list(getattr(self, "last_requested_actions", self.last_actions)),
            list(getattr(self, "last_executed_actions", self.last_actions)),
            self._behaviour_override,
        )

    def restore_state(self, state):
        raw, obs, last, requested, executed, behaviour = copy.deepcopy(state)
        self.raw_env = raw
        self._obs = obs
        self.last_actions = list(last)
        self.last_requested_actions = list(requested)
        self.last_executed_actions = list(executed)
        self._behaviour_override = behaviour

    def fixed_continuation_policy(self, agent):
        # NOOP is a stable fixed reference action in RWARE.
        del agent
        return 0


def make_rware_environment(seed=0, n_agents=6, max_steps=60, observation_width=192, **_):
    from rware.warehouse import Warehouse, RewardType, ObservationType
    warehouse = Warehouse(
        shelf_columns=3,
        column_height=3,
        shelf_rows=2,
        n_agents=int(n_agents),
        msg_bits=0,
        sensor_range=1,
        request_queue_size=4,
        max_inactivity_steps=int(max_steps),
        max_steps=int(max_steps),
        reward_type=RewardType.GLOBAL,
        observation_type=ObservationType.FLATTENED,
        render_mode="rgb_array",
    )
    env = RWARECIGEnvironment(warehouse, observation_width=observation_width, max_steps=max_steps)
    env.reset(seed=int(seed))
    return env
