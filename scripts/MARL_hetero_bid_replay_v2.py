#!/usr/bin/env python3
"""Receiver-local TOP-2 bids plus the scheduler-side quantities they unlock (mitigation M-D).

v1 (MARL_hetero_bid_replay.py) is unchanged; this file imports its helpers.  At every labelled
snapshot, before transmission:
  RECEIVER-SIDE (reaches the scheduler only through a 1-byte bid: 3+3+2 bits)
    p1, p2   best and runner-up MP2 phases under the receiver's own sensor and own cache
    gapbin   0: gap < 1, 1: < 2, 2: < 4, 3: >= 4
  SCHEDULER-SIDE, legal given the bid
    c[i][j]  coefficient of sender j in score(p1) - score(p2): from the PUBLIC topology and the
             known MP2 code, evaluated at the bid's (p1, p2)
    age[i][j] age (s) of receiver i's cached copy of j, from the receiver mirror; -1 if never heard
Same trajectory checks as the mirror replay.  The true gap is stored only for diagnostics.
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
from scripts.DIAG_cityflow_set_objective_hops import build_static, mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC, H, ROWS, COLS
from scripts.MARL_hetero_response_replay import checked, gap_of
from scripts.MARL_hetero_bid_replay import coefficients

SOURCES = ['scripts/MARL_hetero_bid_replay_v2.py', 'scripts/MARL_hetero_bid_replay.py',
           'scripts/MARL_hetero_response_replay.py', 'envs/external/cityflow_hetero_mirror.py',
           'envs/external/cityflow_hetero.py', 'scripts/MARL_hetero_pilot_collect.py',
           'scripts/DIAG_cityflow_set_objective_hops.py']


def gapbin(g):
    return 0 if g < 1 else (1 if g < 2 else (2 if g < 4 else 3))


def run(a):
    shards = [Path(x) for x in a.labels]
    out = Path(a.out).resolve(); out.mkdir(parents=True, exist_ok=False)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    start = time.perf_counter(); n = 0
    with gzip.open(out / 'bid3_diag.jsonl.gz', 'wt') as raw:
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
                        now = env._now()
                        bid = []
                        for i in range(m):
                            v = env._build_view(i)
                            if v.inbox:
                                raise AssertionError('receiver view has an inbox before transmission')
                            _, sc = checked(v, topo[i], down, onward)
                            order_p = sorted(sc, key=lambda p: -sc[p])
                            p1, p2 = order_p[0], order_p[1]
                            g = gap_of(sc)
                            # scheduler side, from the bid's (p1, p2), public topology and the mirror
                            c = [coef[i][p1].get(j, 0.0) - coef[i][p2].get(j, 0.0) for j in range(m)]
                            age = []
                            for j in range(m):
                                e = env.mirror.entry(i, j) if j != i else None
                                age.append(-1.0 if e is None else float(now - e[1]))
                            bid.append(dict(p1=int(p1), p2=int(p2), gapbin=gapbin(g), gap_true=g, c=c, age=age))
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
        bid3_sha256=hashlib.sha256((out / 'bid3_diag.jsonl.gz').read_bytes()).hexdigest(),
        bid='RECEIVER-SIDE (p1, p2, gapbin) 1 byte; c from public topology; age from the legal mirror',
        seconds=time.perf_counter() - start), indent=2))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--labels', nargs='+', required=True); p.add_argument('--out', required=True)
    run(p.parse_args())
