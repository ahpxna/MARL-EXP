#!/usr/bin/env python3
"""Paired development comparison of E3 selector ARMS on one set of states (read-only; no rollouts, no training).

An arm is a list of saved selector checkpoints (normally the 3 init seeds of one variant).  For every state the arm's
realised gain is the MEAN over its checkpoints of y[chosen] (chosen by the checkpoint's own saved tau, direct policy,
MARL_e3_selector_diag_v2.predictions / choose -- the exact code path of diagnostic v2).  Arms are compared on the SAME
states: pairwise differences with a bootstrap over EPISODES (all snapshots of an episode together) and, as the
handoff F1.3 sensitivity, over TRAFFIC SEEDS (both loads of a seed together).
States: the label directory given by --labels (default <actor dir>/labels_dev); --restrict-to <label dir> keeps only
the (episode, t) states present there (the 'same state intersection' of handoff F1.2).
Self-check (abort): every arm's checkpoints read the same label ckpt as the states; every state is scored by every arm.
"""
from __future__ import annotations
import argparse, glob, gzip, json, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, Net, choose
from scripts.MARL_e3_selector_diag_v2 import predictions
from models.marl_e3_response import RespNet


def boot(vals, keys, B=5000, seed=0):
    by = defaultdict(list)
    for v, k in zip(vals, keys):
        by[k].append(v)
    K = sorted(by); rng = np.random.default_rng(seed)
    out = [np.mean(np.concatenate([by[K[i]] for i in rng.integers(0, len(K), len(K))])) for _ in range(B)]
    return [float(x) for x in np.quantile(out, [0.025, 0.975])], len(K)


def arm_gains(files, S):
    G = np.zeros((len(files), len(S))); E = np.zeros((len(files), len(S)), bool)
    for n, mf in enumerate(files):
        meta = torch.load(mf, weights_only=False)
        net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); hn = None
        if meta.get('resp'):
            hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
        tau = meta['tau']['direct']; tau = {None: -np.inf, '-inf': -np.inf, '+inf': np.inf}.get(tau, tau) if not isinstance(tau, float) else tau
        for s, st in enumerate(S):
            an, y, feas, r1 = predictions(meta, net, hn, st)
            j = choose(an, feas, np.ones_like(r1), tau); G[n, s] = y[j]; E[n, s] = j != 0
    return G.mean(0), E.mean(0)


def main(a):
    D = Path(a.actor_dir); L = Path(a.labels) if a.labels else D / 'labels_dev'
    S, ck = load([L])
    if a.restrict_to:
        keep = {(r['episode_id'], r['t']) for r in map(json.loads, gzip.open(Path(a.restrict_to) / 'labels.jsonl.gz', 'rt'))}
        S = [st for st in S if (st['episode_id'], st['t']) in keep]
    qd = L.parent / f'qbid_{L.name}'
    if (qd / 'manifest.json').exists():
        Q = {(r['episode_id'], r['t']): r['qbid'] for r in map(json.loads, gzip.open(qd / 'qbid.jsonl.gz', 'rt'))}
        for st in S:
            st['qbid'] = Q.get((st['episode_id'], st['t']))
    ep = [st['episode_id'] for st in S]; seed = [e.split('_')[0] for e in ep]
    arms = {}
    for spec in a.arm:
        name, pat = spec.split('=', 1); files = sorted(glob.glob(str(D / pat)))
        if not files:
            raise SystemExit(f'arm {name}: no checkpoint matches {pat}')
        for mf in files:
            job = Path(mf).with_name(Path(mf).name.replace('model_', 'job_').replace('.pt', '.json'))
            if not job.exists():
                raise SystemExit(f'SELF-CHECK FAIL: {mf} has no job record')
            jck = json.loads(job.read_text())['actor_ckpt']
            if {jck} != ck:
                raise SystemExit(f'SELF-CHECK FAIL: {mf} was trained on labels of {jck}, states are labelled by {ck}')
        g, e = arm_gains(files, S); arms[name] = dict(files=[str(f) for f in files], gain=g, edit=e)
        ci, _ = boot(g, ep)
        print(f'{name:18s} n_ckpt {len(files)} states {len(S)}: gain {g.mean():+.2f} [{ci[0]:+.2f},{ci[1]:+.2f}] edit {e.mean():.2f}', flush=True)
    res = dict(labels=str(L), restrict_to=a.restrict_to, states=len(S), episodes=len(set(ep)), traffic_seeds=len(set(seed)),
               arms={k: dict(files=v['files'], mean_gain=float(v['gain'].mean()), ci_episode=boot(v['gain'], ep)[0], edit_rate=float(v['edit'].mean()))
                     for k, v in arms.items()}, pairs={})
    names = list(arms)
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            d = arms[names[j]]['gain'] - arms[names[i]]['gain']
            ce, ne = boot(d, ep); cs, ns = boot(d, seed)
            res['pairs'][f'{names[j]} - {names[i]}'] = dict(mean=float(d.mean()), ci_episode=ce, n_episodes=ne, ci_traffic_seed=cs, n_seeds=ns)
            print(f'  {names[j]} - {names[i]}: {d.mean():+.2f}  episode CI [{ce[0]:+.2f},{ce[1]:+.2f}] (n={ne})  seed CI [{cs[0]:+.2f},{cs[1]:+.2f}] (n={ns})', flush=True)
    Path(a.out).write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor-dir', required=True); p.add_argument('--labels'); p.add_argument('--restrict-to')
    p.add_argument('--arm', action='append', required=True, help='name=<glob relative to the actor dir>, e.g. legal=selectors_v3/model_legal_bid_resp_s*.pt')
    p.add_argument('--out', required=True)
    main(p.parse_args())
