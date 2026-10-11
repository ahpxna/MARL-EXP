"""Networks of the Midtown shared + local light (scripts/CITY_mt_train_light_moe.py, PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010 MT-A5),
in an importable module so that saved checkpoints load in any evaluator (pickle refers to scripts.CITY_mt_moe_net)."""
import torch
import torch.nn as nn


class LocalMLP(nn.Module):
    """Per-light MLPs evaluated in one batch: parameters indexed by the light id in the last input column."""

    def __init__(self, L, din, hidden, dout, zero_last):
        super().__init__()
        self.W = nn.ParameterList(); self.B = nn.ParameterList(); dims = [din] + list(hidden) + [dout]
        for a, b in zip(dims[:-1], dims[1:]):
            w = torch.empty(L, a, b); [nn.init.kaiming_uniform_(w[i].T, a=5 ** 0.5) for i in range(L)]
            self.W.append(nn.Parameter(w)); self.B.append(nn.Parameter(torch.zeros(L, b)))
        if zero_last:
            nn.init.zeros_(self.W[-1]); nn.init.zeros_(self.B[-1])

    def forward(self, f, i):
        h = f
        for n, (w, b) in enumerate(zip(self.W, self.B)):
            h = torch.einsum('bd,bdh->bh', h, w[i]) + b[i]
            if n < len(self.W) - 1:
                h = torch.relu(h)
        return h


class MoEQ(nn.Module):
    def __init__(self, arm, L, din, shared=None):
        super().__init__()
        self.arm, self.L = arm, L
        if arm in ('lg', 'ln'):
            self.shared = shared
            for p in self.shared.parameters():
                p.requires_grad_(False)
            self.local = LocalMLP(L, din, (32,), 2, zero_last=True)
            if arm == 'lg':
                self.emb = nn.Embedding(L, 8); self.gate = nn.Sequential(nn.Linear(din + 8, 32), nn.ReLU(), nn.Linear(32, 1))
        elif arm == 'lo':
            self.local = LocalMLP(L, din, (64, 64), 2, zero_last=False)
        else:
            raise ValueError(arm)

    def forward(self, x):
        f, i = x[:, :-1], x[:, -1].long().clamp(0, self.L - 1)
        if self.arm == 'lo':
            return self.local(f, i)
        q = self.shared(f); dq = self.local(f, i)
        if self.arm == 'ln':
            return q + dq
        g = torch.sigmoid(self.gate(torch.cat([f, self.emb(i)], 1)))
        return q + g * dq

    @torch.no_grad()
    def gate_mean(self, x):
        if self.arm != 'lg':
            return None
        f, i = x[:, :-1], x[:, -1].long().clamp(0, self.L - 1)
        return float(torch.sigmoid(self.gate(torch.cat([f, self.emb(i)], 1))).mean())
