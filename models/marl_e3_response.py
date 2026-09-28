"""E3 response head (stage A for a learned actor; readiness audit P2.5): shared by training and closed loop.

For candidate profile S and receiver i, predict whether the frozen actor's action at the current step
CHANGES from its action under the prefix P.  Target: the actor's actual joint actions stored in the
continuation labels (PRIVILEGED; training labels only).  Inputs, all LEGAL scheduler-side data:
  bid block (only with a bid): the receiver's 1-byte bid (top-2 phases one-hot, logit-gap bin);
  the edit at i: number of senders added and dropped;
  for the added and for the dropped senders separately: summed mirror age (never heard counts as age
  1.0 = 100 s), number never heard, summed |latest scheduler copy - receiver's cached copy| of waiting
  (z vs mirror, scaled /100), number physically adjacent to i (public grid topology).
"""
from __future__ import annotations
import numpy as np
import torch
from torch import nn

DIM = 22 + 2 + 4 + 4


def grid_adjacent(i, j, cols=3):
    return abs(i // cols - j // cols) + abs(i % cols - j % cols) == 1


def _pair(st, i, j):
    m = st['m']; k = i * (m - 1) + (j if j < i else j - 1); blk = st['mirror'][12 * k: 12 * (k + 1)]
    zz = st['z'][1 + 12 * j: 1 + 12 * (j + 1)]
    present = blk[0] > 0
    age = blk[1] if present else 1.0
    cached = np.asarray(blk[8:12]) if present else np.zeros(4)
    latest = np.asarray(zz[8:12]) if zz[0] > 0 else np.zeros(4)
    return age, 0.0 if present else 1.0, float(np.abs(latest - cached).sum()), 1.0 if grid_adjacent(i, j) else 0.0


def resp_features(st, bid, gap_thr):
    """(C, m, DIM) array for every candidate of state st (candidate 0 is the prefix)."""
    m = st['m']; P = st['cands'][0]['sets']; C = len(st['cands'])
    pair = {(i, j): _pair(st, i, j) for i in range(m) for j in range(m) if i != j}
    B = np.zeros((m, 22), np.float32)
    if bid:
        for i, b in enumerate(st['bid']):
            B[i, b['p1']] = 1; B[i, 9 + b['p2']] = 1; B[i, 18 + int(np.searchsorted(gap_thr, b['gap']))] = 1
    X = np.zeros((C, m, DIM), np.float32)
    for c, cand in enumerate(st['cands']):
        for i in range(m):
            add = set(cand['sets'][i]) - set(P[i]); drop = set(P[i]) - set(cand['sets'][i])
            X[c, i, :22] = B[i]; X[c, i, 22] = len(add); X[c, i, 23] = len(drop)
            for off, S in ((24, add), (28, drop)):
                for j in S:
                    X[c, i, off:off + 4] += pair[(i, j)]
    return X


def change_targets(st):
    P = st['cands'][0]['joint']
    return np.array([[float(c['joint'][i] != P[i]) for i in range(st['m'])] for c in st['cands']], np.float32)


class RespNet(nn.Module):
    def __init__(self, h=64):
        super().__init__()
        self.net = nn.Sequential(nn.Linear(DIM, h), nn.ReLU(), nn.Linear(h, h), nn.ReLU(), nn.Linear(h, 1))

    def forward(self, x):
        return self.net(x).squeeze(-1)
