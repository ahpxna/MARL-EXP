#!/usr/bin/env python3
"""CLOSED-LOOP evaluation of frozen repair selectors on CityFlow (heterogeneous broadcast).

Unlike every earlier panel (held-phase values at snapshots of a prefix-driven trajectory), here
the selector's choice at EVERY decision step is transmitted, the frozen MP2 actors act on what
they actually received, and the simulation continues with that trajectory.  Endpoints are
episode-level traffic outcomes, paired by (traffic seed, headway, budget trace):
  queue_sum   sum over decisions of total waiting vehicles (lower is better)
  finished    completed trips at the end;  travel time from episode_summary (censoring stated)
  bytes       accounted transport bytes + charged bid bytes
Methods:
  prefix                 R = 0 (the public heuristic base order), the paired baseline
  <learner>/s<k>         frozen development model + its frozen tau, total cap C (bids charged
                         inside C), policy repair_R1 or direct; selection runs under
                         no_oracle_access; bids are computed receiver-side from own sensor+cache
  oracle_heldphase       REFERENCE: at each step the candidate with the best TRUE held-phase value
                         within the same cap (oracle rollouts); not deployable
Candidates at each step: the same family as the collectors (candidates(order, K, m, rng)).
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import BudgetTraceSpec, make_grid_scenario
from envs.external.cityflow_hetero_mirror import make_hetero_mirror_env
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets, profile_cost
from scripts.DIAG_cityflow_set_objective_hops import build_static, mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC, H, ROWS, COLS, candidates, Labeler
from scripts.MARL_hetero_diag_train import pmat
from scripts.MARL_hetero_diag_train_v2 import choose, anchor
from scripts.MARL_hetero_response_replay import checked, gap_of
from scripts.MARL_hetero_mitigation_dev import features, Net, BID_BYTES, onehot8, FRAGILE

SOURCES = ['scripts/MARL_hetero_closed_loop.py', 'scripts/MARL_hetero_mitigation_dev.py',
           'scripts/MARL_hetero_response_replay.py', 'scripts/MARL_hetero_pilot_collect.py',
           'envs/external/cityflow_hetero_mirror.py', 'envs/external/cityflow_hetero.py',
           'models/marl_hetero_selector.py']


def make_env(out, seed, load, tag):
    eid = f'seed{seed}_load{load:g}'
    scen = make_grid_scenario(out / 'scenarios' / tag.replace('/', '_') / eid, rows=ROWS, cols=COLS, traffic_seed=seed,
                              horizon_s=10 * (N_DEC + H + 5), mean_headway_s=load)
    env = make_hetero_mirror_env(scen, budget_spec=BudgetTraceSpec(kind='bursty', k=4, k_low=1),
                                 n_decisions=N_DEC, capacity_seed=5000 + 10 * seed + int(load), mode='oracle')
    env.reset(budget_seed=1000 + seed)
    topo = {i: env.public_topology(i) for i in range(env.n_agents)}
    down, onward = build_static(topo)
    return eid, env, topo, down, onward


def receiver_bids(env, topo, down, onward):
    out = []
    for i in range(env.n_agents):
        v = env._build_view(i)                                   # own sensor + own cache, no inbox
        if v.inbox:
            raise AssertionError('receiver view has an inbox before transmission')
        act, sc = checked(v, topo[i], down, onward)
        out.append(dict(pref=int(act), gap=gap_of(sc), own=[float(x) for x in np.asarray(v.lane_waiting).sum(axis=1)]))
    return out


def live_group(z, K, mirror, bids, order, cands):
    m = len(K); P = prefix_sets(order, K)
    profs = [list(p) for p in cands]
    ip = [i for i, p in enumerate(profs) if all(set(p[r]) == set(P[r]) for r in range(m))][0]
    cost = np.asarray([profile_cost(order, K, [set(s) for s in p])[0] for p in profs], float)
    r1 = np.asarray([all(len(set(p[r]) - P[r]) <= 1 for r in range(m)) for p in profs])
    return dict(m=m, C=len(profs), ctx_pub=np.asarray(list(z) + [x / m for x in K], np.float32),
                mirror=np.asarray(mirror, np.float32),
                bid_prefgap=np.concatenate([np.concatenate([onehot8(b['pref']) for b in bids]),
                                            np.asarray([min(31, round(b['gap'] * 2)) / 31 for b in bids], np.float32)]),
                bid_flag=np.asarray([float(b['gap'] <= FRAGILE) for b in bids], np.float32),
                bid_queue=np.asarray([min(255, round(sum(b['own']))) / 255 for b in bids], np.float32),
                masks=np.stack([pmat(p, m).reshape(-1) for p in profs]).astype(np.uint8),
                ev=dict(cost=cost, b0=cost[ip], r1=r1, ip=ip)), profs


def episode(out, seed, load, method, model, cap, policy):
    eid, env, topo, down, onward = make_env(out, seed, load, method)
    m = env.n_agents; rng = np.random.default_rng(30000 + 10 * seed + int(load))
    extra_bytes = 0; edits = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            ctx = env.scheduler_context(); z = ctx.features(); order = tuple(ctx.cached_queue_ranking())
            mir = env.mirror_features()
            env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        cands = candidates(order, K, m, rng)
        bids = receiver_bids(env, topo, down, onward)
        g, profs = live_group(z, K, mir, bids, order, cands)
        if method == 'prefix':
            j = g['ev']['ip']
        elif method == 'oracle_heldphase':
            lab = Labeler(env, lambda i, v: mp2_action(v, topo[i], down, onward))
            vals = np.asarray([lab.value(p) for p in profs], float)
            cx = None if cap is None else cap
            g['ev']['delta'] = vals - vals[g['ev']['ip']]
            j = choose(g['ev'], g['ev']['delta'], cx, policy == 'repair_R1', 0.0)
        else:
            net, ck, learner, tau = model
            with no_oracle_access(env):
                c, d = features(g, learner)
                x = torch.as_tensor(np.concatenate([np.tile((c - ck['cm']) / ck['cs'], (g['C'], 1)),
                                                    (d - ck['dm']) / ck['ds']], 1).astype(np.float32))
                with torch.no_grad():
                    an = anchor(g['ev'], net(x)[0].numpy().astype(float))
                cx = None if cap is None else cap - BID_BYTES.get(learner, 0)
                j = choose(g['ev'], an, cx, policy == 'repair_R1', tau)
            extra_bytes += BID_BYTES.get(learner, 0)
        edits += int(j != g['ev']['ip'])
        if method == 'prefix':
            R_sub, cap_abs = 0, None
        else:
            R_sub = 1 if policy == 'repair_R1' else None
            lrn = model[2] if model is not None else None
            cap_abs = None if cap is None else g['ev']['b0'] + cap - BID_BYTES.get(lrn, 0)
        with no_oracle_access(env):
            env.submit_profile([set(s) for s in profs[j]], R=R_sub, cap=cap_abs)
            views = env.transmit()
            env.verify_mirror()
            _, _, rec = env.step({i: mp2_action(v, topo[i], down, onward) for i, v in views.items()})
            extra_bytes += rec['accounted_bytes']
    summ = env.episode_summary()
    return dict(episode=eid, method=method, queue_sum=float(sum(r['queue'] for r in env.step_records)),
                finished=int(env.step_records[-1]['finished']), bytes=int(extra_bytes), edits=edits,
                summary=summ)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    methods = ['prefix'] + (['oracle_heldphase'] if a.oracle else [])
    models = {}
    for learner in a.learners:
        for s in a.init_seeds:
            job = json.loads((Path(a.dev) / f'job_{learner}_s{s}.json').read_text())
            key = 'none' if a.cap is None else f'+{a.cap}'
            t = job['results'][learner][key][a.policy]['tau']
            ck = torch.load(Path(a.dev) / f'model_{learner}_s{s}.pt', weights_only=False)
            models[f'{learner}/s{s}'] = (ck, learner, np.inf if t is None else t)
            methods.append(f'{learner}/s{s}')
    rows = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.loads:
            for meth in methods:
                model = None
                if meth in models:
                    ck, learner, tau = models[meth]
                    model = (_LazyNet(ck), ck, learner, tau)     # input width known at first call
                r = episode(out, seed, load, meth, model, a.cap, a.policy)
                rows.append(r)
                print(f'[{time.perf_counter() - t0:.0f}s] {r["episode"]} {meth}: queue_sum {r["queue_sum"]:.0f} '
                      f'finished {r["finished"]} bytes {r["bytes"]} edits {r["edits"]}', flush=True)
                tmp = out / '.rows.json'; tmp.write_text(json.dumps(rows, default=float)); os.replace(tmp, out / 'rows.json')
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0,
        seconds=time.perf_counter() - t0, evidence_class='CLOSED LOOP, frozen MP2 actors, frozen selectors'), indent=1, default=str))
    print('COMPLETE', out, flush=True)


class _LazyNet:
    """Builds the Net on first call, when the input width is known."""

    def __init__(self, ck):
        self.ck = ck; self.net = None

    def __call__(self, x):
        if self.net is None:
            self.net = Net(x.shape[1], len(self.ck['state']['change.bias'])); self.net.load_state_dict(self.ck['state'])
            self.net.eval()
        return self.net(x)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dev', required=True); p.add_argument('--out', required=True)
    p.add_argument('--learners', nargs='*', default=[]); p.add_argument('--init-seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--traffic-seeds', type=int, nargs='+', required=True)
    p.add_argument('--loads', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--cap', type=lambda s: None if s == 'none' else int(s), default=28)
    p.add_argument('--policy', default='repair_R1'); p.add_argument('--oracle', action='store_true')
    main(p.parse_args())
