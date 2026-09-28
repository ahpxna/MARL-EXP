#!/usr/bin/env python3
"""Receiver-local REQUEST bids (mitigation M-C), by deterministic replay of labelled episodes.

At every labelled snapshot, BEFORE transmission, each receiver i uses only its own sensor and its
own packet cache (its AgentView at the revise stage, empty inbox) to compute:
  pref, gap  its preferred MP2 phase and the score gap to the runner-up (as in the response replay)
  req        the sender whose information most affects that decision: for the best phase p1 and
             runner-up p2, the MP2 coefficient of sender j in score(p1) - score(p2) is c_j
             (dn1 terms -1, onward terms -LAMBDA/len); req = argmax_j |c_j| * staleness_j with
             staleness_j = 1 + age_j/10 (cached) or 10 (never heard); -1 if every c_j = 0
  req_age    the age (s) of i's cached copy of req, or -1 if never heard
These quantities reach the scheduler only through a charged bid.  No other agent's fresh payload,
no counterfactual view, no label.  Same trajectory checks as MARL_hetero_mirror_replay.py.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import BudgetTraceSpec, make_grid_scenario
from envs.external.cityflow_hetero_mirror import make_hetero_mirror_env
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.DIAG_cityflow_set_objective_hops import build_static, mp2_action, LAMBDA
from scripts.MARL_hetero_pilot_collect import N_DEC, H, ROWS, COLS
from scripts.MARL_hetero_response_replay import checked, gap_of

SOURCES = ['scripts/MARL_hetero_bid_replay.py', 'scripts/MARL_hetero_response_replay.py',
           'envs/external/cityflow_hetero_mirror.py', 'envs/external/cityflow_hetero.py',
           'scripts/MARL_hetero_pilot_collect.py', 'scripts/DIAG_cityflow_set_objective_hops.py']


def coefficients(topo, down, onward):
    """coef[p][j]: d score(p) / d (heard waiting of sender j), summed over slots."""
    i = topo.agent; out = {}
    for p in topo.valid_phases:
        c = {}
        for (s, road) in topo.phase_movements[p]:
            j, sj = down[i].get(road, (None, None))
            if j is None:
                continue
            c[j] = c.get(j, 0.0) - 1.0
            nxt = onward.get(j, {}).get(sj, [])
            for (j2, _) in nxt:
                c[j2] = c.get(j2, 0.0) - LAMBDA / len(nxt)
        out[p] = c
    return out


def request(view, sc, coef):
    order = sorted(sc, key=lambda p: -sc[p])
    if len(order) < 2:
        return -1, -1.0
    p1, p2 = order[0], order[1]
    js = set(coef[p1]) | set(coef[p2])
    best, bv, bage = -1, 0.0, -1.0
    for j in sorted(js):
        cj = coef[p1].get(j, 0.0) - coef[p2].get(j, 0.0)
        if abs(cj) < 1e-12:
            continue
        e = view.message_from(j)
        st = 10.0 if e is None else 1.0 + float(e.age) / 10.0
        if abs(cj) * st > bv + 1e-12:
            best, bv, bage = j, abs(cj) * st, (-1.0 if e is None else float(e.age))
    return best, bage


def run(a):
    shards = [Path(x) for x in a.labels]
    out = Path(a.out).resolve(); out.mkdir(parents=True, exist_ok=False)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    start = time.perf_counter(); n = 0
    with gzip.open(out / 'bid2_diag.jsonl.gz', 'wt') as raw:
        for labels_dir in shards:
            man = json.loads((labels_dir / 'manifest.json').read_text())
            if hashlib.sha256((labels_dir / 'labels.jsonl.gz').read_bytes()).hexdigest() != man['labels_sha256']:
                raise ValueError('labels hash mismatch')
            by_ep = {}
            for l in gzip.open(labels_dir / 'labels.jsonl.gz', 'rt'):
                r = json.loads(l); by_ep.setdefault((r['traffic_seed'], r['headway']), {})[r['t']] = r
            for (seed, load), snaps in sorted(by_ep.items()):
                eid = f'seed{seed}_load{load:g}'
                scen = make_grid_scenario(out / 'scenarios' / eid, rows=ROWS, cols=COLS, traffic_seed=seed,
                                          horizon_s=10 * (N_DEC + H + 5), mean_headway_s=load)
                env = make_hetero_mirror_env(scen, budget_spec=BudgetTraceSpec(kind='bursty', k=4, k_low=1),
                                             n_decisions=N_DEC, capacity_seed=5000 + 10 * seed + int(load),
                                             mode='oracle')
                env.reset(budget_seed=1000 + seed)
                topo = {i: env.public_topology(i) for i in range(env.n_agents)}
                down, onward = build_static(topo)
                coef = {i: coefficients(topo[i], down, onward) for i in range(env.n_agents)}
                m = env.n_agents
                for t in range(max(snaps) + 1):
                    with no_oracle_access(env):
                        ctx = env.scheduler_context()
                        z = ctx.features(); order = tuple(ctx.cached_queue_ranking())
                        env.commit_global_ranking(order)
                        Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
                    if t in snaps:
                        lab = snaps[t]
                        if lab['z'] != z or tuple(lab['order']) != order or lab['groups'][0]['K'] != K:
                            raise AssertionError(f'{eid} t={t}: replay does not reproduce the labelled snapshot')
                        bid = []
                        for i in range(m):
                            v = env._build_view(i)
                            if v.inbox:
                                raise AssertionError('receiver view has an inbox before transmission')
                            act, sc = checked(v, topo[i], down, onward)
                            rq, rage = request(v, sc, coef[i])
                            bid.append(dict(pref=int(act), gap=gap_of(sc), req=int(rq), req_age=rage))
                        raw.write(json.dumps(dict(episode_id=eid, split=lab['split'], traffic_seed=seed,
                                                  headway=load, t=t, bid=bid)) + '\n'); raw.flush(); n += 1
                    with no_oracle_access(env):
                        env.submit_profile(prefix_sets(order, K), R=0)
                        views = env.transmit()
                        env.verify_mirror()
                        env.step({i: mp2_action(v, topo[i], down, onward) for i, v in views.items()})
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during replay')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', records=n,
        labels=[str(s.resolve()) for s in shards], source_hashes=hashes,
        bid2_sha256=hashlib.sha256((out / 'bid2_diag.jsonl.gz').read_bytes()).hexdigest(),
        bid='RECEIVER-SIDE local request bids; usable by the scheduler only through a charged bid',
        seconds=time.perf_counter() - start), indent=2))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--labels', nargs='+', required=True); p.add_argument('--out', required=True)
    run(p.parse_args())
