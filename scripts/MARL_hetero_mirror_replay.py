#!/usr/bin/env python3
"""Deterministic replay of the Step 3 pilot TRAIN/VAL episodes to add two diagnostic fields.

  mirror     LEGAL: every receiver's packet cache reconstructed by the scheduler from the
             payloads it transmitted and the profiles it submitted (ReceiverMirror).  Read with
             _summary and _sensor disabled, so no fresh sensor can enter.
  joint      PRIVILEGED CONTROL ONLY: the joint MP2 action induced by every labelled profile
             (oracle counterfactual views).  Never a deployable input.
Existing labels are REUSED, not relabelled.  Before joining, each snapshot must reproduce the
saved z, base order and live capacity vector exactly, and two stored values (the prefix and one
other labelled profile) must be reproduced by a fresh rollout.  After every live transmission the
mirror is asserted equal to the true receiver caches.  Any mismatch aborts; nothing is joined.
Test seeds 61-64 are not replayed.
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
from scripts.MARL_cheap_screen import fingerprint
from scripts.MARL_hetero_pilot_collect import SNAPS, N_DEC, H, ROWS, COLS

SOURCES = ['scripts/MARL_hetero_mirror_replay.py', 'envs/external/cityflow_hetero_mirror.py',
           'envs/external/cityflow_hetero.py', 'models/marl_receiver_mirror.py',
           'scripts/MARL_hetero_pilot_collect.py']


def unmask(x):
    return [j for j in range(16) if (x >> j) & 1]


def run(a):
    labels_dir = Path(a.labels)
    man = json.loads((labels_dir / 'manifest.json').read_text())
    if hashlib.sha256((labels_dir / 'labels.jsonl.gz').read_bytes()).hexdigest() != man['labels_sha256']:
        raise ValueError('labels hash mismatch')
    rows = [json.loads(l) for l in gzip.open(labels_dir / 'labels.jsonl.gz', 'rt')]
    by_ep = {}
    for r in rows:
        by_ep.setdefault((r['traffic_seed'], r['headway']), {})[r['t']] = r
    out = Path(a.out).resolve(); out.mkdir(parents=True, exist_ok=False)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    start = time.perf_counter(); n = 0
    with gzip.open(out / 'mirror_diag.jsonl.gz', 'wt') as raw:
        for (seed, load), snaps in sorted(by_ep.items()):
            eid = f'seed{seed}_load{load:g}'
            scen = make_grid_scenario(out / 'scenarios' / eid, rows=ROWS, cols=COLS, traffic_seed=seed,
                                      horizon_s=10 * (N_DEC + H + 5), mean_headway_s=load)
            env = make_hetero_mirror_env(scen, budget_spec=BudgetTraceSpec(kind='bursty', k=4, k_low=1),
                                         n_decisions=N_DEC, capacity_seed=5000 + 10 * seed + int(load),
                                         mode='oracle')
            env.reset(budget_seed=1000 + seed)
            if env.mirror_features() != [0.0] * len(env.mirror_features()):
                raise AssertionError('mirror not clean after reset')
            topo = {i: env.public_topology(i) for i in range(env.n_agents)}
            down, onward = build_static(topo)
            actor = lambda i, v: mp2_action(v, topo[i], down, onward)
            m = env.n_agents
            for t in range(max(snaps) + 1):
                with no_oracle_access(env):
                    ctx = env.scheduler_context()
                    z = ctx.features(); order = tuple(ctx.cached_queue_ranking())
                    def forbid(*_, **__):
                        raise AssertionError('fresh sensor read while building legal features')
                    env._summary = env._sensor = forbid          # instance attributes shadow the methods
                    try:
                        mir = env.mirror_features()
                    finally:
                        del env._summary, env._sensor            # restore the class methods
                    env.commit_global_ranking(order)
                    Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
                if t in snaps:
                    lab = snaps[t]
                    if lab['z'] != z or tuple(lab['order']) != order or lab['groups'][0]['K'] != K:
                        raise AssertionError(f'{eid} t={t}: replay does not reproduce the labelled snapshot')
                    before = fingerprint(env)
                    acts = {}
                    def act(i, mask):
                        if (i, mask) not in acts:
                            acts[(i, mask)] = actor(i, env.counterfactual_view(i, unmask(mask)))
                        return acts[(i, mask)]
                    joint = [[[act(i, pm[i]) for i in range(m)] for pm in g['profiles']] for g in lab['groups']]
                    g0 = lab['groups'][0]
                    P = [sum(1 << j for j in s) for s in prefix_sets(order, K)]
                    ip = g0['profiles'].index(P); io = len(g0['profiles']) // 2
                    for ix in (ip, io):
                        v = env.oracle_rollout_value(dict(enumerate(joint[0][ix])), H)
                        if v != g0['values'][ix]:
                            raise AssertionError(f'{eid} t={t}: stored value {g0["values"][ix]} != replayed {v}')
                    if fingerprint(env) != before:
                        raise AssertionError('diagnostics changed the live state')
                    raw.write(json.dumps(dict(episode_id=eid, split=lab['split'], traffic_seed=seed, headway=load,
                                              t=t, mirror=mir, joint=joint)) + '\n'); raw.flush(); n += 1
                    print(f'{lab["split"]} {eid} t={t}: replay matches labels; {len(acts)} actions; '
                          f'{n} records, {time.perf_counter() - start:.0f}s', flush=True)
                with no_oracle_access(env):
                    env.submit_profile(prefix_sets(order, K), R=0)
                    views = env.transmit()
                    env.verify_mirror()
                    env.step({i: actor(i, v) for i, v in views.items()})
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during replay')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', records=n, labels=str(labels_dir.resolve()),
        labels_sha256=man['labels_sha256'], source_hashes=hashes,
        mirror_sha256=hashlib.sha256((out / 'mirror_diag.jsonl.gz').read_bytes()).hexdigest(),
        checks='z/order/K reproduced; 2 stored values re-rolled per snapshot; mirror == receiver caches after every transmit; '
               'mirror features built with _summary/_sensor disabled; mirror clean after reset',
        joint='PRIVILEGED control only', seconds=time.perf_counter() - start), indent=2))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--labels', required=True); p.add_argument('--out', required=True)
    run(p.parse_args())
