"""Actor-input and actor-network VARIANTS for the E3 root-cause experiments (29/09 22:0x; ledger L-121).

Same input layout and schema as models.marl_comm_actor.CommAdapter (own 35 | agent one-hot 9 | 8 x 29 sender blocks
[fresh, heard, age, phase one-hot 9, elapsed, vehicles 4, waiting 4, static 8]), so trainers, schemas and checkpoints are
unchanged; each variant isolates ONE hypothesis about why the flat MLP is harmed by messages.
  NoiseCommAdapter      every sender block's dynamic part replaced by UNINFORMATIVE random values (deterministic in
                        agent, step and simulator time), statics kept: varying irrelevant input dimensions (H1).
  FreshOnlyCommAdapter  the view as delivered, but every NON-fresh (cached, stale) block is zeroed, statics kept:
                        only this step's deliveries reach the actor (H5, stale content misleads).
  SharedConcatActorNet  a shared per-sender encoder (29 -> 32, tanh), masked by 'heard', CONCATENATED over the 8 slots
                        (no pooling), then the policy MLP: weight sharing without aggregation (H3 vs H4).
  AttnActorNet          a TarMAC-style signature attention over the heard senders (query from the own block, keys and
                        values from the shared sender encoder), then the policy MLP (a stronger aggregator).
"""
from __future__ import annotations
import numpy as np
import torch
from torch import nn
from models.marl_comm_actor import CommAdapter, N_PH

BLK_DYN = 21                       # fresh, heard, age, phase(9), elapsed, vehicles(4), waiting(4)


class _BlockAdapter(CommAdapter):
    def _blocks(self, x):
        base = self.own_dim + self.m
        return [x[base + k * self.blk_dim: base + (k + 1) * self.blk_dim] for k in range(self.m - 1)]


class NoiseCommAdapter(_BlockAdapter):
    def encode(self, view, variant='actual', rng=None):
        x = super().encode(view, variant, rng).copy()
        g = np.random.default_rng([int(view.agent), int(view.decision_step), int(round(float(view.sim_time) * 10))])
        for b in self._blocks(x):
            b[0] = float(g.random() < 0.5); b[1] = 1.0; b[2] = g.random()
            b[3:12] = 0.0; b[3 + int(g.integers(0, N_PH))] = 1.0; b[12] = g.random()
            b[13:21] = np.abs(g.normal(0.0, 0.3, 8))
        return x


class FreshOnlyCommAdapter(_BlockAdapter):
    def encode(self, view, variant='actual', rng=None):
        x = super().encode(view, variant, rng).copy()
        for b in self._blocks(x):
            if b[0] < 0.5:
                b[:BLK_DYN] = 0.0
        return x


def _split(x, m, own_dim, blk_dim):
    head = x[..., :own_dim + m]
    B = x[..., own_dim + m:].reshape(*x.shape[:-1], m - 1, blk_dim)
    return head, B


class SharedConcatActorNet(nn.Module):
    def __init__(self, dim, hidden=128, m=9, own_dim=35, blk_dim=29, enc=32):
        super().__init__()
        self.m, self.own_dim, self.blk_dim = m, own_dim, blk_dim
        self.phi = nn.Sequential(nn.Linear(blk_dim, enc), nn.Tanh())
        self.body = nn.Sequential(nn.Linear(own_dim + m + (m - 1) * enc, hidden), nn.Tanh(), nn.Linear(hidden, hidden), nn.Tanh())
        self.head = nn.Linear(hidden, N_PH)

    def forward(self, x, mask):
        head, B = _split(x, self.m, self.own_dim, self.blk_dim)
        z = (self.phi(B) * B[..., 1:2]).flatten(-2)
        return self.head(self.body(torch.cat([head, z], -1))).masked_fill(~mask, -1e9)


class AttnActorNet(nn.Module):
    def __init__(self, dim, hidden=128, m=9, own_dim=35, blk_dim=29, enc=64):
        super().__init__()
        self.m, self.own_dim, self.blk_dim, self.enc = m, own_dim, blk_dim, enc
        self.phi = nn.Sequential(nn.Linear(blk_dim, hidden), nn.Tanh())
        self.key = nn.Linear(hidden, enc); self.val = nn.Linear(hidden, enc); self.query = nn.Linear(own_dim + m, enc)
        self.body = nn.Sequential(nn.Linear(own_dim + m + enc, hidden), nn.Tanh(), nn.Linear(hidden, hidden), nn.Tanh())
        self.head = nn.Linear(hidden, N_PH)

    def forward(self, x, mask):
        head, B = _split(x, self.m, self.own_dim, self.blk_dim)
        h = self.phi(B); heard = B[..., 1] > 0.5
        att = (self.key(h) * self.query(head).unsqueeze(-2)).sum(-1) / self.enc ** 0.5
        att = att.masked_fill(~heard, -1e9)
        w = torch.softmax(att, -1) * heard.any(-1, keepdim=True).float()
        ctx = (w.unsqueeze(-1) * self.val(h)).sum(-2)
        return self.head(self.body(torch.cat([head, ctx], -1))).masked_fill(~mask, -1e9)
