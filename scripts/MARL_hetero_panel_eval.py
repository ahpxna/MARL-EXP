#!/usr/bin/env python3
"""Descriptive evaluation of FROZEN selectors on a panel (PROTOCOL_B6_ROBUSTNESS_20260927.md).

--dev-map: learner -> development dir (frozen model_*.pt, job_*.json tau; stageA.pt for
mlp_top2_joint).  Groups of the panel (md.build + bid attach) are evaluated at caps +28/+56/+84,
policies repair_R1/direct, bids charged; --live-only keeps the live-K group of each snapshot (the
capacity process under test).  Reports seed-averaged mean gain, oracle at the method's cap,
fraction of oracle, and the difference to --control with a cluster bootstrap over episodes.
Nothing is refitted.  Check: oracle R1 gain >= 0 in every group.
"""
from __future__ import annotations
import argparse, gzip, json, sys
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_hetero_mitigation_dev as md
import scripts.MARL_hetero_bid_top2_dev as t2
import scripts.MARL_hetero_bid_request_dev as rq
import scripts.MARL_hetero_top2_joint_dev as tj
from scripts.MARL_hetero_diag_train_v2 import choose, outcome, anchor
from scripts.MARL_hetero_b2_confirm_v2 import features, BID
from scripts.MARL_hetero_b2_confirm import boot


def group_index(run):
    gi = []
    for lab in sorted(x for x in run.glob('labels_*') if x.is_dir()):
        for l in gzip.open(lab / 'labels.jsonl.gz', 'rt'):
            r = json.loads(l); gi += list(range(len(r['groups'])))
    return np.array(gi)


def main(a):
    run = Path(a.run); devmap = json.loads(Path(a.dev_map).read_text())
    G = md.build(run); t2.attach(G, run)
    if any(x.is_dir() for x in run.glob('bid2_*')):
        rq.attach_bids(G, run)
    gi = group_index(run)
    keep = [k for k, g in enumerate(G) if (gi[k] == 0 or not a.live_only)]
    G = [G[k] for k in keep]
    evs = [g['ev'] for g in G]; eps = [e['ep'] for e in evs]
    if 'mlp_top2_joint' in devmap:
        d = Path(devmap['mlp_top2_joint'])
        netA = nn.Sequential(nn.Linear(23, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, 3))
        netA.load_state_dict(torch.load(d / 'stageA.pt', weights_only=False)); netA.eval()
        with torch.no_grad():
            for g in G:
                X, _, p1, p2 = tj.a_features(g)
                pr = torch.softmax(netA(torch.as_tensor(X.reshape(-1, X.shape[2]))), 1).numpy().reshape(g['C'], g['m'], 3)
                g['soft'] = tj.soft_joint(pr, p1, p2)
    res = {}
    for learner, d in devmap.items():
        d = Path(d); per = []
        for seed in (0, 1, 2):
            f = d / f'job_{learner}_s{seed}.json'
            if not f.exists():
                continue
            job = json.loads(f.read_text()); ck = torch.load(d / f'model_{learner}_s{seed}.pt', weights_only=False)
            c0, d0 = features(G[0], learner)
            net = md.Net(len(c0) + d0.shape[1], G[0]['m']); net.load_state_dict(ck['state']); net.eval()
            anch = []
            with torch.no_grad():
                for g in G:
                    c, dd = features(g, learner)
                    x = torch.as_tensor(np.concatenate([np.tile((c - ck['cm']) / ck['cs'], (g['C'], 1)), (dd - ck['dm']) / ck['ds']], 1).astype(np.float32))
                    anch.append(anchor(g['ev'], net(x)[0].numpy().astype(float)))
            rs = {}
            for total in (28, 56, 84):
                key = f'+{total}'; cx = total - BID.get(learner, 0)
                for pol in ('repair_R1', 'direct'):
                    t = job['results'][learner][key][pol]['tau']; tau = np.inf if t is None else t
                    rs[(key, pol)] = [outcome(e, choose(e, an, cx, pol == 'repair_R1', tau))['gain'] for e, an in zip(evs, anch)]
                o = [outcome(e, choose(e, e['delta'].astype(float), cx, True, 0.0))['gain'] for e in evs]
                if min(o) < -1e-9:
                    raise AssertionError('oracle R1 gain < 0')
                rs[(key, 'oracle')] = o
            per.append(rs)
        res[learner] = per
    out = {}
    print(f'{a.run}: {len(G)} groups ({"live-K only" if a.live_only else "all"}), {len(set(eps))} episodes')
    for key in ('+28', '+56', '+84'):
        for pol in ('repair_R1', 'direct'):
            for learner, per in res.items():
                if not per:
                    continue
                g = np.mean([p[(key, pol)] for p in per], 0); orc = float(np.mean(per[0][(key, 'oracle')]))
                row = dict(gain=float(g.mean()), ci=boot(g, eps, a.boot, np.random.default_rng(0)), oracle=orc,
                           frac=float(g.mean() / orc) if orc > 0 else None, seeds=[float(np.mean(p[(key, pol)])) for p in per])
                if a.control in res and learner != a.control:
                    c = np.mean([p[(key, pol)] for p in res[a.control]], 0)
                    row['diff'] = float((g - c).mean()); row['diff_ci'] = boot(g - c, eps, a.boot, np.random.default_rng(1))
                out[f'{learner}|{key}|{pol}'] = row
                dtxt = f"  diff {row['diff']:+.3f} [{row['diff_ci'][0]:+.3f},{row['diff_ci'][1]:+.3f}]" if 'diff' in row else ''
                print(f'  {learner:16s} {key} {pol:9s} gain {row["gain"]:+.3f} [{row["ci"][0]:+.3f},{row["ci"][1]:+.3f}] '
                      f'orc {orc:+.2f} ({100 * (row["frac"] or 0):4.1f}%){dtxt}')
    Path(a.out).write_text(json.dumps(dict(run=str(run), live_only=a.live_only, dev_map=devmap, results=out), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', required=True); p.add_argument('--dev-map', required=True); p.add_argument('--out', required=True)
    p.add_argument('--live-only', action='store_true'); p.add_argument('--control', default='ctrl_history')
    p.add_argument('--boot', type=int, default=5000)
    main(p.parse_args())
