#!/usr/bin/env python3
"""Latency of the frozen B2 design in closed loop (wall clock, CPU, torch 1 thread).

Per decision step, timed separately:
  receiver_bid     max over receivers of the local bid computation (MP2 scores on the own view);
                   receivers compute in parallel, so the max is the uplink-ready time
  scheduler_post   after the capacity reveal: candidate generation + group features + top-2
                   structure + stage A + critic + choose
  prefix_post      the prefix baseline's post-grant work (prefix sets)
The bid uplink itself is NOT timed (no network model); it is one extra uplink round of 10 B.
Deadline miss rates are reported for 10 / 50 / 100 ms on scheduler_post and on
receiver_bid + scheduler_post.  Machine: this host; numbers are indicative, not a hardware claim.
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC, candidates
from scripts.MARL_hetero_diag_train_v2 import choose, anchor
from scripts.MARL_hetero_response_replay import checked
from scripts.MARL_hetero_bid_replay import coefficients
from scripts.MARL_hetero_closed_loop import make_env, receiver_bids, live_group
from scripts.MARL_hetero_closed_loop_v2 import add_top2, soft_live, _Lazy
from scripts.MARL_hetero_b2_confirm_v2 import features as conf_features, BID


def main(a):
    torch.set_num_threads(1)
    devmap = json.loads(Path(a.dev_map).read_text()); d = Path(devmap['mlp_top2_joint'])
    netA = nn.Sequential(nn.Linear(23, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, 3))
    netA.load_state_dict(torch.load(d / 'stageA.pt', weights_only=False)); netA.eval()
    job = json.loads((d / 'job_mlp_top2_joint_s0.json').read_text()); t = job['results']['mlp_top2_joint']['+84']['direct']['tau']
    ck = torch.load(d / 'model_mlp_top2_joint_s0.pt', weights_only=False); net = _Lazy(ck); tau = np.inf if t is None else t
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    T = dict(receiver_bid=[], scheduler_post=[], prefix_post=[], candidates=[])
    for seed in a.traffic_seeds:
        for load in (8.0, 16.0):
            _, env, topo, down, onward = make_env(out, seed, load, 'lat')
            coef = {i: coefficients(topo[i], down, onward) for i in range(env.n_agents)}
            m = env.n_agents; rng = np.random.default_rng(30000 + 10 * seed + int(load))
            for step in range(N_DEC):
                with no_oracle_access(env):
                    ctx = env.scheduler_context(); z = ctx.features(); order = tuple(ctx.cached_queue_ranking())
                    mir = env.mirror_features(); env.commit_global_ranking(order)
                    Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
                # receiver-side bid: per-receiver time, receivers in parallel -> max
                per = []
                for i in range(m):
                    t0 = time.perf_counter(); v = env._build_view(i); checked(v, topo[i], down, onward); per.append(time.perf_counter() - t0)
                T['receiver_bid'].append(max(per))
                t0 = time.perf_counter(); P = prefix_sets(order, K); T['prefix_post'].append(time.perf_counter() - t0)
                t0 = time.perf_counter()
                cands = candidates(order, K, m, rng)
                g, profs = live_group(z, K, mir, receiver_bids(env, topo, down, onward), order, cands)
                add_top2(g, env, topo, down, onward, coef); soft_live(g, netA)
                c, dd = conf_features(g, 'mlp_top2_joint')
                x = torch.as_tensor(np.concatenate([np.tile((c - ck['cm']) / ck['cs'], (g['C'], 1)), (dd - ck['dm']) / ck['ds']], 1).astype(np.float32))
                with torch.no_grad():
                    an = anchor(g['ev'], net(x)[0].numpy().astype(float))
                j = choose(g['ev'], an, 84 - BID['mlp_top2_joint'], False, tau)
                T['scheduler_post'].append(time.perf_counter() - t0); T['candidates'].append(len(profs))
                with no_oracle_access(env):
                    env.submit_profile([set(s) for s in profs[j]], R=None, cap=g['ev']['b0'] + 84)
                    views = env.transmit(); env.step({i: mp2_action(v, topo[i], down, onward) for i, v in views.items()})
    ms = {k: np.asarray(v) * 1000 for k, v in T.items() if k != 'candidates'}
    tot = ms['receiver_bid'] + ms['scheduler_post']
    rep = {k: dict(median=float(np.median(v)), p95=float(np.quantile(v, .95)), max=float(v.max())) for k, v in ms.items()}
    rep['bid_plus_scheduler'] = dict(median=float(np.median(tot)), p95=float(np.quantile(tot, .95)), max=float(tot.max()))
    rep['deadline_miss'] = {f'{d}ms': dict(scheduler_post=float((ms['scheduler_post'] > d).mean()), bid_plus_scheduler=float((tot > d).mean()))
                            for d in (10, 50, 100)}
    rep['steps'] = len(tot); rep['candidates_mean'] = float(np.mean(T['candidates']))
    rep['note'] = 'CPU wall clock, torch 1 thread, this host; the 10 B bid uplink round is not timed'
    (out / 'latency.json').write_text(json.dumps(rep, indent=1)); print(json.dumps(rep, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dev-map', default='research/marl_budget/b2_freeze_20260927/dev_map.json')
    p.add_argument('--out', required=True); p.add_argument('--traffic-seeds', type=int, nargs='+', default=[601, 602])
    main(p.parse_args())
