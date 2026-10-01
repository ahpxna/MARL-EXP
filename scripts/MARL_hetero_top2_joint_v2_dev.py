#!/usr/bin/env python3
"""Mitigation M-F DEVELOPMENT screen: stage A v2 = stage A + STRUCTURAL FLIP features.

MARL_hetero_top2_joint_dev.py is unchanged and imported.  For receiver i with bid (p1, p2, gapbin)
the scheduler computes, from LEGAL data only,
    delta_ij = sum_slot [coef_i(p1; j, slot) - coef_i(p2; j, slot)] * (latest_j,slot - cached_ij,slot)
(latest: its own last broadcast copy of j, in z; cached: receiver i's copy, in the mirror; coef:
public topology + known MP2, research/marl_budget/mp2_coef_3x3.json).  Receiver i's own queues
cancel in the p1-p2 difference.  For candidate S:
    dS = mid(gapbin) + sum_{j in S_i} delta_ij,   dP = the same for the prefix,
plus the summed delta of added and of dropped senders.  These four numbers per (candidate,
receiver) are appended to the stage-A inputs; stage B is unchanged.  Same splits and trainer.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_hetero_top2_joint_dev as tj

MID = np.array([0.5, 1.5, 3.0, 6.0])
COEF = None


def load_coef(path):
    raw = json.loads(Path(path).read_text())
    return {int(i): {int(p): {tuple(int(x) for x in k.split(',')): v for k, v in c.items()} for p, c in d.items()} for i, d in raw.items()}


def deltas(g):
    m = g['m']; z = g['ctx_pub'][:1 + 12 * m] if len(g['ctx_pub']) >= 1 + 12 * m else g['ctx_pub']
    bid = g['top2'].reshape(m, 20); p1s = bid[:, :8].argmax(1); p2s = bid[:, 8:16].argmax(1)
    D = np.zeros((m, m))
    for i in range(m):
        p1 = int(p1s[i]) or 8; p2 = int(p2s[i]) or 8                     # onehot8 maps phase 8 -> 0
        c1, c2 = COEF[i].get(p1, {}), COEF[i].get(p2, {})
        for j in range(m):
            if j == i:
                continue
            k = i * (m - 1) + (j if j < i else j - 1); blk = g['mirror'][12 * k: 12 * (k + 1)]
            cached = np.asarray(blk[8:12]) * 100 if blk[0] > 0 else np.zeros(4)
            lat = np.asarray(z[1 + 12 * j + 8: 1 + 12 * j + 12]) * 100 if z[1 + 12 * j] > 0 else np.zeros(4)
            D[i, j] = sum((c1.get((j, s), 0.0) - c2.get((j, s), 0.0)) * (lat[s] - cached[s]) for s in range(4))
    return D


_orig = tj.a_features


def a_features_v2(g):
    X, y, p1, p2 = _orig(g)
    if 'flipf' not in g:
        m = g['m']; C = g['C']; D = deltas(g)
        M = g['masks'].reshape(C, m, m).astype(bool); MP = M[g['ev']['ip']]
        d0 = MID[g['gapbin']][None, :]
        dS = d0 + (M * D[None]).sum(2); dP = d0 + (MP[None] * D[None]).sum(2)
        add = ((M & ~MP[None]) * D[None]).sum(2); drop = ((MP[None] & ~M) * D[None]).sum(2)
        g['flipf'] = np.clip(np.stack([dS, np.broadcast_to(dP, dS.shape), add, drop], 2), -30, 30).astype(np.float32) / 10
    return np.concatenate([X, g['flipf']], 2), y, p1, p2


def main(a):
    global COEF
    COEF = load_coef(a.coef)
    tj.a_features = a_features_v2
    sys.argv = [sys.argv[0], '--run', a.run, '--out', a.out, '--threads', str(a.threads)] + \
               (['--seeds'] + [str(s) for s in a.seeds])
    p = tj.argparse.ArgumentParser()
    p.add_argument('--run'); p.add_argument('--out'); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--epochs', type=int, default=40); p.add_argument('--epochs-a', type=int, default=4)
    p.add_argument('--threads', type=int, default=3)
    tj.main(p.parse_args(sys.argv[1:]))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', required=True); ap.add_argument('--out', required=True)
    ap.add_argument('--coef', default='research/marl_budget/mp2_coef_3x3.json')
    ap.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2]); ap.add_argument('--threads', type=int, default=3)
    main(ap.parse_args())
