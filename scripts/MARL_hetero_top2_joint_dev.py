#!/usr/bin/env python3
"""Mitigation M-E DEVELOPMENT screen: emulate the privileged joint-action critic LEGALLY.

The privileged reference (+8.8 on B1) scores candidates by their counterfactual JOINT ACTIONS.
Here the joint action under each candidate is PREDICTED from what the scheduler may know after a
1-byte top-2 bid (MARL_hetero_bid_replay_v2.py): receiver i's (p1, p2, gapbin), the structural
refresh score s_i(S) (public topology + known MP2 + legal mirror ages), whether i is edited, K_i.

  stage A  per (candidate, receiver): P(action = p1 / p2 / other), a small MLP trained on the
           TRAIN split with the privileged counterfactual actions as LABELS only (auxiliary
           supervision, as MARL_E1/B1 independent audits suggest); inference uses legal+bid inputs
  stage B  the imported mitigation trainer on ctx = z, K, bids and per candidate the SOFT
           predicted joint action (p1/p2 mass, 'other' spread over the remaining phases) of the
           candidate and of the prefix, plus the mask.  Trained on stage-A predictions of the
           train split, so train and inference inputs match.  Bid 10 B inside the same total cap.
Splits as MARL_hetero_mitigation_dev.py; 501-508 are DEVELOPMENT (opened), not confirmatory.
Stage-A accuracy on development receivers is reported.
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_hetero_mitigation_dev as md
import scripts.MARL_hetero_bid_top2_dev as t2

SOURCES = ['scripts/MARL_hetero_top2_joint_dev.py', 'scripts/MARL_hetero_bid_top2_dev.py',
           'scripts/MARL_hetero_mitigation_dev.py', 'scripts/MARL_hetero_bid_replay_v2.py']


def a_features(g):
    """(C, m, d) stage-A inputs and (C, m) labels in {0: p1, 1: p2, 2: other}."""
    m = g['m']; C = g['C']
    bid = g['top2'].reshape(m, 20)                       # p1 onehot 8, p2 onehot 8, gapbin onehot 4
    K = g['ctx_pub'][-m:]
    X = np.concatenate([np.broadcast_to(bid[None], (C, m, 20)),
                        np.clip(g['s'], -30, 30)[..., None] / 10, g['edited'][..., None].astype(np.float32),
                        np.broadcast_to(K[None, :, None], (C, m, 1))], 2).astype(np.float32)
    p1 = bid[:, :8].argmax(1); p2 = bid[:, 8:16].argmax(1)
    a = g['tj'] % 8
    y = np.where(a == p1[None], 0, np.where(a == p2[None], 1, 2))
    return X, y, p1, p2


def soft_joint(prob, p1, p2):
    """(C, m, 3) class probabilities -> (C, m*8) soft one-hot joint action."""
    C, m, _ = prob.shape
    out = np.zeros((C, m, 8), np.float32)
    for i in range(m):
        out[:, i, :] = prob[:, i, 2:3] / 6.0
        out[:, i, p1[i]] = prob[:, i, 0]
        out[:, i, p2[i]] += prob[:, i, 1]
        if p1[i] == p2[i]:
            out[:, i, p1[i]] = prob[:, i, 0] + prob[:, i, 1]
    return out.reshape(C, m * 8)


def main(a):
    run = Path(a.run); out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    t0 = time.perf_counter(); torch.manual_seed(0); rng = np.random.default_rng(0); torch.set_num_threads(a.threads)
    G = md.build(run); t2.attach(G, run)
    fit = [g for g in G if g['split'] == 'train']
    # ---- stage A
    Xs, ys = [], []
    for g in fit:
        X, y, _, _ = a_features(g)
        pick = rng.choice(g['C'], size=min(40, g['C']), replace=False)
        Xs.append(X[pick].reshape(-1, X.shape[2])); ys.append(y[pick].reshape(-1))
    XA = torch.as_tensor(np.concatenate(Xs)); yA = torch.as_tensor(np.concatenate(ys)).long()
    netA = nn.Sequential(nn.Linear(XA.shape[1], 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, 3))
    opt = torch.optim.Adam(netA.parameters(), lr=1e-3)
    for ep in range(a.epochs_a):
        for b in np.array_split(rng.permutation(len(yA)), max(1, len(yA) // 2048)):
            loss = nn.functional.cross_entropy(netA(XA[b]), yA[b]); opt.zero_grad(); loss.backward(); opt.step()
    acc = {}
    with torch.no_grad():
        for g in G:
            X, y, p1, p2 = a_features(g)
            pr = torch.softmax(netA(torch.as_tensor(X.reshape(-1, X.shape[2]))), 1).numpy().reshape(g['C'], g['m'], 3)
            g['soft'] = soft_joint(pr, p1, p2)
            acc.setdefault(g['split'], []).append(((pr.argmax(2) == y).mean(), (y == 0).mean()))
    accr = {s: dict(stageA_acc=float(np.mean([x[0] for x in v])), always_p1=float(np.mean([x[1] for x in v])))
            for s, v in acc.items()}
    print(f'[{time.perf_counter() - t0:.0f}s] stage A accuracy by split: {accr}', flush=True)
    torch.save(netA.state_dict(), out / 'stageA.pt')

    # ---- stage B
    def feats(g, learner):
        if learner != 'mlp_top2_joint':
            return orig(g, learner)
        ip = g['ev']['ip']
        ctx = np.concatenate([g['ctx_pub'], g['top2'], g['soft'][ip]]).astype(np.float32)
        return ctx, np.concatenate([g['soft'], g['masks'].astype(np.float32)], 1)
    orig = md.features
    md.features = feats; md.BID_BYTES['mlp_top2_joint'] = 10
    for s in a.seeds:
        b = md.run_job(G, 'mlp_top2_joint', s, out, a.epochs, a.threads)
        r = b['results']['mlp_top2_joint']
        print(f'[{time.perf_counter() - t0:.0f}s] mlp_top2_joint s{s}: ' + ' | '.join(
            f'{k} R1 {v["repair_R1"]["summary"]["gain"]:+.3f} dir {v["direct"]["summary"]["gain"]:+.3f}'
            for k, v in r.items()), flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', run=str(run), source_hashes=h0, stageA=accr,
        seconds=time.perf_counter() - t0, evidence_class='DEVELOPMENT screen on opened B1 data'), indent=1))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', required=True); p.add_argument('--out', required=True)
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--epochs', type=int, default=40); p.add_argument('--epochs-a', type=int, default=4)
    p.add_argument('--threads', type=int, default=3)
    main(p.parse_args())
