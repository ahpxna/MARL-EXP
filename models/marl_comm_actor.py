"""E3 communication-aware actor for PROTOCOL_HETERO_v0 (readiness audit P2; CTDE, MAPPO-style).

Three pieces, kept separate so that the information boundary is visible in code:

* ``CommAdapter`` builds the ACTOR input of receiver i from ITS OWN ``AgentView`` only, plus
  public topology.  It never touches the environment.  Per other agent j (fixed id order) the
  block is [fresh, heard, age, payload..., static topology]; a missing message is encoded as
  heard = 0 with a zero payload, so "never heard" and "heard a zero queue" differ by the heard
  flag.  Variants for the message-use check transform the view's messages only:
      actual   the view as delivered;
      none     every message removed (all heard = 0);
      stale    this step's deliveries removed; last step's messages kept with their age + interval;
      shuffle  payloads permuted among the heard senders (identity broken, content kept).
* ``ActorNet``: shared parameters over agents (agent one-hot in the input), logits over phases,
  invalid phases masked.
* ``CentralCritic``: V(s) on a PRIVILEGED global state (every agent's own sensor, phases, time).
  Training only; never used to act.
"""
from __future__ import annotations
import numpy as np
import torch
from torch import nn

N_PH = 9          # phase ids 0..8; the grid uses 1..8
SCALE_Q = 20.0    # own lane counts
SCALE_P = 30.0    # payload per-slot sums
SCALE_T = 100.0   # seconds


class CommAdapter:
    def __init__(self, topos, n_dec, interval=10):
        self.m = len(topos); self.n_dec = n_dec; self.interval = interval
        self.topos = topos
        self.static = {}
        for i in range(self.m):
            down = {j: sj for _, j, sj in topos[i].outgoing if j is not None}
            for j in range(self.m):
                if j == i:
                    continue
                up = [s for _, r, s in topos[j].outgoing if r == i]
                f = np.zeros(8, np.float32)
                if j in down:
                    f[down[j]] = 1.0
                if up:
                    f[4 + up[0]] = 1.0
                self.static[(i, j)] = f
        self.own_dim = 12 + 12 + N_PH + 1 + 1
        self.blk_dim = 3 + N_PH + 1 + 4 + 4 + 8
        self.dim = self.own_dim + self.m + (self.m - 1) * self.blk_dim
        self.prev = {}                                     # receiver -> last step's messages (for 'stale')

    def schema(self):
        return dict(dim=self.dim, own=['lane_vehicles/20 (4x3)', 'lane_waiting/20 (4x3)', 'own_phase onehot 9',
                                       'own_phase_elapsed/100', 't/n_dec'],
                    agent_onehot=self.m,
                    per_sender=['fresh', 'heard', 'age/100', 'phase onehot 9', 'phase_elapsed/100', 'vehicles/30 (4)',
                                'waiting/30 (4)', 'static: i->j downstream slot onehot 4', 'static: j->i upstream slot onehot 4'],
                    missing='heard = 0 and zero payload; fresh = 1 only for this step\'s deliveries')

    @staticmethod
    def _entries(view):
        out = {}
        for e in view.cache:
            out[e.sender] = (0, e)
        for e in view.inbox:                               # inbox overrides cache
            out[e.sender] = (1, e)
        return out

    def encode(self, view, variant='actual', rng=None):
        i = view.agent
        own = np.concatenate([np.asarray(view.lane_vehicles, np.float32).ravel() / SCALE_Q,
                              np.asarray(view.lane_waiting, np.float32).ravel() / SCALE_Q,
                              np.eye(N_PH, dtype=np.float32)[int(view.own_phase)],
                              [float(view.own_phase_elapsed) / SCALE_T, float(view.decision_step) / self.n_dec]])
        ent = self._entries(view)
        msgs = {j: (fr, float(e.age), e.payload) for j, (fr, e) in ent.items()}
        if variant == 'none':
            msgs = {}
        elif variant == 'stale':
            msgs = {j: (0, a + self.interval, p) for j, (a, p) in self.prev.get(i, {}).items()}
        elif variant == 'shuffle':
            js = sorted(msgs)
            if len(js) > 1:
                perm = list(js)
                while perm == js:
                    perm = list(rng.permutation(js))
                msgs = {j: (msgs[j][0], msgs[j][1], msgs[k][2]) for j, k in zip(js, perm)}
        elif variant != 'actual':
            raise ValueError(variant)
        blocks = []
        for j in range(self.m):
            if j == i:
                continue
            b = np.zeros(self.blk_dim, np.float32); b[-8:] = self.static[(i, j)]
            if j in msgs:
                fr, age, p = msgs[j]
                b[0] = fr; b[1] = 1.0; b[2] = age / SCALE_T
                b[3 + int(p.phase)] = 1.0; b[3 + N_PH] = float(p.phase_elapsed) / SCALE_T
                b[4 + N_PH:8 + N_PH] = np.asarray(p.vehicles, np.float32) / SCALE_P
                b[8 + N_PH:12 + N_PH] = np.asarray(p.waiting, np.float32) / SCALE_P
            blocks.append(b)
        x = np.concatenate([own, np.eye(self.m, dtype=np.float32)[i]] + blocks).astype(np.float32)
        assert x.shape[0] == self.dim
        return x

    def remember(self, views):
        """Store this step's messages (after acting) for the next step's 'stale' variant."""
        self.prev = {i: {j: (float(e.age), e.payload) for j, (_, e) in self._entries(v).items()} for i, v in views.items()}

    def reset(self):
        self.prev = {}

    def global_state(self, views, t):
        """PRIVILEGED (critic only): every agent's own sensor and phase, and time."""
        parts = []
        for i in range(self.m):
            v = views[i]
            parts += [np.asarray(v.lane_vehicles, np.float32).ravel() / SCALE_Q,
                      np.asarray(v.lane_waiting, np.float32).ravel() / SCALE_Q,
                      np.eye(N_PH, dtype=np.float32)[int(v.own_phase)], [float(v.own_phase_elapsed) / SCALE_T]]
        parts.append([t / self.n_dec])
        return np.concatenate(parts).astype(np.float32)

    def valid_mask(self):
        M = np.zeros((self.m, N_PH), bool)
        for i in range(self.m):
            M[i, list(self.topos[i].valid_phases)] = True
        return M


class ActorNet(nn.Module):
    def __init__(self, dim, hidden=128):
        super().__init__()
        self.body = nn.Sequential(nn.Linear(dim, hidden), nn.Tanh(), nn.Linear(hidden, hidden), nn.Tanh())
        self.head = nn.Linear(hidden, N_PH)

    def forward(self, x, mask):
        logits = self.head(self.body(x))
        return logits.masked_fill(~mask, -1e9)


class CentralCritic(nn.Module):
    def __init__(self, dim, hidden=128):
        super().__init__()
        self.net = nn.Sequential(nn.Linear(dim, hidden), nn.Tanh(), nn.Linear(hidden, hidden), nn.Tanh(), nn.Linear(hidden, 1))

    def forward(self, s):
        return self.net(s).squeeze(-1)
