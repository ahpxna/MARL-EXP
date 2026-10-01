#!/usr/bin/env python3
"""CLOSED-LOOP evaluation v2: adds the frozen top-2 bid selectors (mlp_top2, mlp_top2_joint).

v1 (MARL_hetero_closed_loop.py) is unchanged; its environment, candidate family, episode loop and
endpoints are reused.  Here, at every decision step, the receiver-local top-2 bids (p1, p2,
gapbin) are computed before transmission from each receiver's own view; the scheduler derives the
refresh scores from the public topology, the known MP2 code and the legal mirror, runs the FROZEN
stage-A response model (mlp_top2_joint) and the frozen critic with its frozen tau, and transmits
the chosen profile; bid bytes (10 B) are charged inside the total cap and added to the bytes.
Methods: prefix, oracle_heldphase (reference), and any frozen learner in --dev-map.
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC, candidates, Labeler
from scripts.MARL_hetero_diag_train_v2 import choose, anchor
from scripts.MARL_hetero_response_replay import checked, gap_of
from scripts.MARL_hetero_bid_replay import coefficients
from scripts.MARL_hetero_bid_replay_v2 import gapbin
from scripts.MARL_hetero_closed_loop import make_env, receiver_bids, live_group
import scripts.MARL_hetero_mitigation_dev as md
import scripts.MARL_hetero_bid_top2_dev as t2
import scripts.MARL_hetero_top2_joint_dev as tj
from scripts.MARL_hetero_b2_confirm_v2 import features as conf_features, BID
from scripts.DIAG_cityflow_set_objective_hops import build_static

SOURCES = ['scripts/MARL_hetero_closed_loop_v2.py', 'scripts/MARL_hetero_closed_loop.py',
           'scripts/MARL_hetero_b2_confirm_v2.py', 'scripts/MARL_hetero_top2_joint_dev.py',
           'scripts/MARL_hetero_bid_top2_dev.py', 'scripts/MARL_hetero_mitigation_dev.py']


def add_top2(g, env, topo, down, onward, coef):
    m = g['m']; now = env._now(); bids = []
    for i in range(m):
        v = env._build_view(i)
        if v.inbox:
            raise AssertionError('receiver view has an inbox before transmission')
        _, sc = checked(v, topo[i], down, onward)
        o = sorted(sc, key=lambda p: -sc[p]); p1, p2 = o[0], o[1]
        c = [coef[i][p1].get(j, 0.0) - coef[i][p2].get(j, 0.0) for j in range(m)]
        age = []
        for j in range(m):
            e = env.mirror.entry(i, j) if j != i else None
            age.append(-1.0 if e is None else float(now - e[1]))
        bids.append(dict(p1=int(p1), p2=int(p2), gapbin=gapbin(gap_of(sc)), c=c, age=age))
    W = np.array([[abs(b['c'][j]) * t2.st(b['age'][j]) for j in range(m)] for b in bids])
    M = g['masks'].reshape(g['C'], m, m).astype(bool); MP = M[g['ev']['ip']]
    g['s'] = ((M & ~MP[None]) * W[None]).sum(2) - ((MP[None] & ~M) * W[None]).sum(2)
    g['edited'] = (M != MP[None]).any(2)
    g['gapbin'] = np.array([b['gapbin'] for b in bids])
    g['top2'] = np.concatenate([np.concatenate([md.onehot8(b['p1']), md.onehot8(b['p2']),
                                                np.eye(4, dtype=np.float32)[b['gapbin']]]) for b in bids])
    return bids


def soft_live(g, netA):
    m = g['m']; C = g['C']; bid = g['top2'].reshape(m, 20); K = g['ctx_pub'][-m:]
    X = np.concatenate([np.broadcast_to(bid[None], (C, m, 20)), np.clip(g['s'], -30, 30)[..., None] / 10,
                        g['edited'][..., None].astype(np.float32), np.broadcast_to(K[None, :, None], (C, m, 1))], 2).astype(np.float32)
    with torch.no_grad():
        pr = torch.softmax(netA(torch.as_tensor(X.reshape(-1, X.shape[2]))), 1).numpy().reshape(C, m, 3)
    g['soft'] = tj.soft_joint(pr, bid[:, :8].argmax(1), bid[:, 8:16].argmax(1))


def episode(out, seed, load, method, model, cap, policy, netA):
    eid, env, topo, down, onward = make_env(out, seed, load, method)
    coef = {i: coefficients(topo[i], down, onward) for i in range(env.n_agents)}
    m = env.n_agents; rng = np.random.default_rng(30000 + 10 * seed + int(load))
    total_bytes = 0; edits = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            ctx = env.scheduler_context(); z = ctx.features(); order = tuple(ctx.cached_queue_ranking())
            mir = env.mirror_features()
            env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        cands = candidates(order, K, m, rng)
        g, profs = live_group(z, K, mir, receiver_bids(env, topo, down, onward), order, cands)
        learner = None
        if method == 'prefix':
            j = g['ev']['ip']
        elif method == 'oracle_heldphase':
            lab = Labeler(env, lambda i, v: mp2_action(v, topo[i], down, onward))
            vals = np.asarray([lab.value(p) for p in profs], float)
            g['ev']['delta'] = vals - vals[g['ev']['ip']]
            j = choose(g['ev'], g['ev']['delta'], cap, policy == 'repair_R1', 0.0)
        else:
            net, ck, learner, tau = model
            if learner in ('mlp_top2', 'mlp_top2_joint'):
                add_top2(g, env, topo, down, onward, coef)
                if learner == 'mlp_top2_joint':
                    soft_live(g, netA)
            with no_oracle_access(env):
                c, d = conf_features(g, learner)
                x = torch.as_tensor(np.concatenate([np.tile((c - ck['cm']) / ck['cs'], (g['C'], 1)),
                                                    (d - ck['dm']) / ck['ds']], 1).astype(np.float32))
                with torch.no_grad():
                    an = anchor(g['ev'], net(x)[0].numpy().astype(float))
                cx = None if cap is None else cap - BID.get(learner, 0)
                j = choose(g['ev'], an, cx, policy == 'repair_R1', tau)
            total_bytes += BID.get(learner, 0)
        edits += int(j != g['ev']['ip'])
        if method == 'prefix':
            R_sub, cap_abs = 0, None
        else:
            R_sub = 1 if policy == 'repair_R1' else None
            cap_abs = None if cap is None else g['ev']['b0'] + cap - BID.get(learner, 0)
        with no_oracle_access(env):
            env.submit_profile([set(s) for s in profs[j]], R=R_sub, cap=cap_abs)
            views = env.transmit(); env.verify_mirror()
            _, _, rec = env.step({i: mp2_action(v, topo[i], down, onward) for i, v in views.items()})
            total_bytes += rec['accounted_bytes']
    return dict(episode=eid, method=method, queue_sum=float(sum(r['queue'] for r in env.step_records)),
                finished=int(env.step_records[-1]['finished']), bytes=int(total_bytes), edits=edits,
                summary=env.episode_summary())


class _Lazy:
    def __init__(self, ck):
        self.ck = ck; self.net = None

    def __call__(self, x):
        if self.net is None:
            self.net = md.Net(x.shape[1], len(self.ck['state']['change.bias'])); self.net.load_state_dict(self.ck['state']); self.net.eval()
        return self.net(x)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    devmap = json.loads(Path(a.dev_map).read_text())
    methods = ['prefix'] + (['oracle_heldphase'] if a.oracle else []); models = {}; netA = None
    key = 'none' if a.cap is None else f'+{a.cap}'
    for learner in a.learners:
        d = Path(devmap[learner])
        if learner == 'mlp_top2_joint':
            netA = nn.Sequential(nn.Linear(23, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, 3))
            netA.load_state_dict(torch.load(d / 'stageA.pt', weights_only=False)); netA.eval()
        for s in a.init_seeds:
            job = json.loads((d / f'job_{learner}_s{s}.json').read_text())
            t = job['results'][learner][key][a.policy]['tau']
            ck = torch.load(d / f'model_{learner}_s{s}.pt', weights_only=False)
            models[f'{learner}/s{s}'] = (_Lazy(ck), ck, learner, np.inf if t is None else t)
            methods.append(f'{learner}/s{s}')
    rows = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.loads:
            for meth in methods:
                r = episode(out, seed, load, meth, models.get(meth), a.cap, a.policy, netA)
                rows.append(r)
                print(f'[{time.perf_counter() - t0:.0f}s] {r["episode"]} {meth}: queue_sum {r["queue_sum"]:.0f} '
                      f'finished {r["finished"]} bytes {r["bytes"]} edits {r["edits"]}', flush=True)
                tmp = out / '.rows.json'; tmp.write_text(json.dumps(rows, default=float)); os.replace(tmp, out / 'rows.json')
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0,
        seconds=time.perf_counter() - t0, evidence_class='CLOSED LOOP, frozen MP2 actors, frozen selectors'),
        indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dev-map', required=True); p.add_argument('--out', required=True)
    p.add_argument('--learners', nargs='*', default=[]); p.add_argument('--init-seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--traffic-seeds', type=int, nargs='+', required=True)
    p.add_argument('--loads', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--cap', type=lambda s: None if s == 'none' else int(s), default=84)
    p.add_argument('--policy', default='direct'); p.add_argument('--oracle', action='store_true')
    main(p.parse_args())
