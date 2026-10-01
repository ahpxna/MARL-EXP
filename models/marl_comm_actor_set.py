"""Set-structured actor for E3 (29/09; ledger L-105 follow-up): an ALGORITHMIC change on the actor side.

Same input as models.marl_comm_actor.CommAdapter (own block, agent one-hot, 8 per-sender blocks of 29), same output
(masked logits over 9 phases), so adapters, trainers and schemas are unchanged.  Instead of one flat MLP over the fixed
276-dim vector, every sender block goes through a SHARED encoder phi (its static topology features let phi tell
neighbours apart), is masked by its 'heard' flag, and the encodings are MEAN-POOLED over heard senders (a DeepSets
encoder: invariant to which subset arrived, robust to a variable number of messages).  The pooled vector is
concatenated with the own block and the agent one-hot and fed to the policy MLP.
"""
from __future__ import annotations
import torch
from torch import nn
from models.marl_comm_actor import N_PH


class SetActorNet(nn.Module):
    def __init__(self, dim, hidden=128, m=9, own_dim=35, blk_dim=29):
        super().__init__()
        self.m, self.own_dim, self.blk_dim = m, own_dim, blk_dim
        if dim != own_dim + m + (m - 1) * blk_dim:
            raise ValueError(f'input dim {dim} does not match the CommAdapter layout')
        self.phi = nn.Sequential(nn.Linear(blk_dim, hidden), nn.Tanh(), nn.Linear(hidden, hidden), nn.Tanh())
        self.body = nn.Sequential(nn.Linear(own_dim + m + hidden, hidden), nn.Tanh(), nn.Linear(hidden, hidden), nn.Tanh())
        self.head = nn.Linear(hidden, N_PH)

    def forward(self, x, mask):
        head = x[..., :self.own_dim + self.m]
        B = x[..., self.own_dim + self.m:].reshape(*x.shape[:-1], self.m - 1, self.blk_dim)
        heard = B[..., 1:2]
        pooled = (self.phi(B) * heard).sum(-2) / (heard.sum(-2) + 1.0)
        logits = self.head(self.body(torch.cat([head, pooled], -1)))
        return logits.masked_fill(~mask, -1e9)
