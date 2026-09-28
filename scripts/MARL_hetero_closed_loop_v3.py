#!/usr/bin/env python3
"""CLOSED-LOOP evaluation v3: adds communication BASELINES (v1/v2 unchanged and reused).

  schednet_fresh   SchedNet adaptation: before the capacity reveal each SENDER sends a 1-byte weight
                   = min(255, its FRESH own total waiting) (own sensor; 9 B + 1 B header = 10 B, charged);
                   the stream order is by decreasing weight (ties by id); each receiver decodes its
                   first k_i senders (R = 0).  A hand-designed weight: SchedNet learns the weight
                   generator end to end, which needs a learned actor/critic loop (E3).
  where2comm_top2  Where2comm-style request baseline (rule, no learning): receivers send the 1-byte
                   top-2 bid (p1, p2, gapbin; 10 B charged); for receivers with gap < 2, fragile first,
                   the scheduler swaps in the sender j maximising |c_ij| * staleness_ij (public
                   topology + known MP2 + mirror ages) for the kept sender with the smallest
                   |c_ij| * staleness_ij, as long as the profile stays within the cap.
Learned methods (--learners, frozen) and prefix / oracle_heldphase are as in v2.
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
from models.marl_hetero_selector import prefix_sets, profile_cost
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_response_replay import checked, gap_of
from scripts.MARL_hetero_bid_replay import coefficients
from scripts.MARL_hetero_closed_loop import make_env
import scripts.MARL_hetero_closed_loop_v2 as v2
import scripts.MARL_hetero_bid_top2_dev as t2

SOURCES = ['scripts/MARL_hetero_closed_loop_v3.py', 'scripts/MARL_hetero_closed_loop_v2.py',
           'scripts/MARL_hetero_closed_loop.py']
BIDB = 10


def baseline_episode(out, seed, load, method, cap):
    eid, env, topo, down, onward = make_env(out, seed, load, method)
    coef = {i: coefficients(topo[i], down, onward) for i in range(env.n_agents)}
    m = env.n_agents; total = 0; edits = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            ctx = env.scheduler_context()
            if method == 'schednet_fresh':
                w = []
                for j in range(m):                                  # sender-side, own sensor only
                    v = env._build_view(j); w.append(min(255, int(round(float(np.asarray(v.lane_waiting).sum())))))
                order = tuple(sorted(range(m), key=lambda j: (-w[j], j)))
            else:
                order = tuple(ctx.cached_queue_ranking())
            env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        P = prefix_sets(order, K); sets = [set(s) for s in P]
        if method == 'where2comm_top2':
            now = env._now(); info = []
            for i in range(m):
                v = env._build_view(i); _, sc = checked(v, topo[i], down, onward)
                o = sorted(sc, key=lambda p: -sc[p]); p1, p2 = o[0], o[1]; g = gap_of(sc)
                imp = {}
                for j in range(m):
                    if j == i:
                        continue
                    cj = abs(coef[i][p1].get(j, 0.0) - coef[i][p2].get(j, 0.0))
                    e = env.mirror.entry(i, j); st = 10.0 if e is None else 1.0 + float(now - e[1]) / 10.0
                    imp[j] = cj * st
                info.append((g, i, imp))
            b0 = profile_cost(order, K, sets)[0]
            for g, i, imp in sorted(info):
                if g >= 2:
                    break
                out_c = [j for j in imp if j not in sets[i] and imp[j] > 0]
                if not out_c or not sets[i]:
                    continue
                add = max(out_c, key=lambda j: imp[j]); drop = min(sets[i], key=lambda j: imp.get(j, 0.0))
                if imp[add] <= imp.get(drop, 0.0):
                    continue
                trial = [set(s) for s in sets]; trial[i] = (trial[i] - {drop}) | {add}
                if profile_cost(order, K, trial)[0] <= b0 + cap - BIDB:
                    sets = trial; edits += 1
        with no_oracle_access(env):
            env.submit_profile(sets, R=None, cap=None if cap is None else profile_cost(order, K, [set(s) for s in P])[0] + cap)
            views = env.transmit(); env.verify_mirror()
            _, _, rec = env.step({i: mp2_action(v, topo[i], down, onward) for i, v in views.items()})
            total += rec['accounted_bytes'] + BIDB
    return dict(episode=eid, method=method, queue_sum=float(sum(r['queue'] for r in env.step_records)),
                finished=int(env.step_records[-1]['finished']), bytes=int(total), edits=edits, summary=env.episode_summary())


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    devmap = json.loads(Path(a.dev_map).read_text()) if a.dev_map else {}
    methods = ['prefix'] + a.baselines + (['oracle_heldphase'] if a.oracle else []); models = {}; netA = None
    key = f'+{a.cap}'
    for learner in a.learners:
        d = Path(devmap[learner])
        if learner == 'mlp_top2_joint':
            netA = nn.Sequential(nn.Linear(23, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, 3))
            netA.load_state_dict(torch.load(d / 'stageA.pt', weights_only=False)); netA.eval()
        for s in (0, 1, 2):
            job = json.loads((d / f'job_{learner}_s{s}.json').read_text())
            t = job['results'][learner][key][a.policy]['tau']
            ck = torch.load(d / f'model_{learner}_s{s}.pt', weights_only=False)
            models[f'{learner}/s{s}'] = (v2._Lazy(ck), ck, learner, np.inf if t is None else t); methods.append(f'{learner}/s{s}')
    rows = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in (8.0, 16.0):
            for meth in methods:
                if meth in a.baselines:
                    r = baseline_episode(out, seed, load, meth, a.cap)
                else:
                    r = v2.episode(out, seed, load, meth, models.get(meth), a.cap, a.policy, netA)
                rows.append(r)
                print(f'[{time.perf_counter() - t0:.0f}s] {r["episode"]} {meth}: queue_sum {r["queue_sum"]:.0f} '
                      f'finished {r["finished"]} bytes {r["bytes"]} edits {r["edits"]}', flush=True)
                tmp = out / '.rows.json'; tmp.write_text(json.dumps(rows, default=float)); os.replace(tmp, out / 'rows.json')
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0,
        seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dev-map', default=None); p.add_argument('--out', required=True)
    p.add_argument('--learners', nargs='*', default=[]); p.add_argument('--baselines', nargs='*', default=['schednet_fresh', 'where2comm_top2'])
    p.add_argument('--traffic-seeds', type=int, nargs='+', required=True)
    p.add_argument('--cap', type=int, default=84); p.add_argument('--policy', default='direct'); p.add_argument('--oracle', action='store_true')
    main(p.parse_args())
