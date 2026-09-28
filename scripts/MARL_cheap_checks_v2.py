#!/usr/bin/env python3
"""Cheap checks v2 collector: the pilot's episodes, plus three diagnostic fields per snapshot.

Same frozen MP2 actor, same held-phase value, same live protocol as MARL_cheap_screen.py
(profile 'pilot'); that script is imported, not modified.  Added per snapshot:

  fresh_features  ORACLE diagnostic: every agent's CURRENT summary (the packet it would send
                  now).  Used only for the information-ceiling selector.  Never deployable.
  bids            one byte per agent, min(255, own current waiting): computed by each agent
                  from its own sensor, sent as a charged control message (9 bytes/step here).
                  Used for the fresh-bid selector (SchedNet-style weight broadcast).
  hetero          heterogeneous-receiver broadcast: receiver i reads the first k_i packets of
                  ONE shared stream (own packet excluded).  Values of: heuristic shared order;
                  best shared order found by transposition local search from two starts;
                  per-receiver sets by coordinate ascent started at that best shared profile.
                  Both searches are heuristics; per-receiver >= best-found shared by construction.

All oracle calls happen at the snapshot, outside the live rank->reveal->submit->transmit->act
segment, which is wrapped in no_oracle_access as before.
"""
from __future__ import annotations
import argparse, dataclasses, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import BudgetTraceSpec, make_grid_scenario
from envs.external.cityflow_broadcast import make_broadcast_env
from models.marl_screening import no_oracle_access, headroom
from scripts.DIAG_cityflow_set_objective_hops import build_static, mp2_action, analyse
from scripts.MARL_cheap_screen import joint_table, fingerprint, profile

DEPENDENCIES = ['scripts/MARL_cheap_checks_v2.py', 'scripts/MARL_cheap_screen.py',
                'scripts/DIAG_cityflow_set_objective_hops.py', 'envs/external/cityflow_budgeted.py',
                'envs/external/cityflow_broadcast.py', 'models/marl_screening.py',
                'models/marl_revision_selector.py']


def source_hashes():
    return {n: hashlib.sha256((ROOT / n).read_bytes()).hexdigest() for n in DEPENDENCIES}


def payload_features(p):
    return [p.phase / 10.0, p.phase_elapsed / 100.0] + [x / 100.0 for x in p.vehicles] + \
           [x / 100.0 for x in p.waiting]


def fresh_payloads(env):
    m = env.n_agents
    pay = dict(env.oracle_payloads(0))
    pay[0] = env.oracle_payloads(1)[0]
    return [pay[j] for j in range(m)]


def hetero_analysis(env, actor, horizon, rng, sweeps):
    """Heterogeneous receiver budgets on one broadcast stream (oracle diagnostic)."""
    m = env.n_agents
    kr = [int(x) for x in rng.integers(1, m - 1, size=m)]      # receiver i reads k_i of m-1 packets
    view_cache, value_cache = {}, {}

    def action(i, heard):
        key = (i, tuple(sorted(heard)))
        if key not in view_cache:
            view_cache[key] = actor(i, env.counterfactual_view(i, list(key[1])))
        return view_cache[key]

    def value(joint):
        if joint not in value_cache:
            value_cache[joint] = env.oracle_rollout_value(dict(enumerate(joint)), horizon)
        return value_cache[joint]

    def shared_joint(order):
        return tuple(action(i, [j for j in order if j != i][:kr[i]]) for i in range(m))

    def local_search(order):
        order = list(order); best = value(shared_joint(order))
        for _ in range(sweeps):
            improved = False
            for a in range(m):
                for b in range(a + 1, m):
                    cand = order[:]; cand[a], cand[b] = cand[b], cand[a]
                    v = value(shared_joint(cand))
                    if v > best + 1e-9:
                        order, best, improved = cand, v, True
            if not improved:
                break
        return order, best

    ctx = env.scheduler_context()
    heur = list(ctx.cached_queue_ranking())
    v_heur = value(shared_joint(heur))
    starts = [heur, list(range(m))]
    found = [local_search(s) for s in starts]
    best_order, v_shared = max(found, key=lambda t: t[1])
    # achievable actions per receiver at its own budget
    from itertools import combinations
    achievable = []
    for i in range(m):
        others = [j for j in range(m) if j != i]
        achievable.append(sorted({action(i, list(S)) for S in combinations(others, kr[i])}))
    joint = list(shared_joint(best_order)); v_pr = value(tuple(joint))
    for _ in range(3):
        changed = False
        for i in range(m):
            for a in achievable[i]:
                cand = joint[:]; cand[i] = a
                v = value(tuple(cand))
                if v > v_pr + 1e-9:
                    joint, v_pr, changed = cand, v, True
        if not changed:
            break
    v_none = value(tuple(action(i, []) for i in range(m)))
    v_full = value(tuple(action(i, [j for j in range(m) if j != i]) for i in range(m)))
    return dict(receiver_budgets=kr, v_heuristic_shared=v_heur, v_best_shared=v_shared,
                best_shared_order=best_order, v_per_receiver=v_pr, v_no_comm=v_none,
                v_full_comm=v_full, n_distinct_joint=len(value_cache),
                n_achievable=[len(a) for a in achievable])


def run(args):
    out = args.out.resolve(); out.mkdir(parents=True, exist_ok=False)
    cfg = profile('pilot'); cfg['hetero_sweeps'] = args.sweeps
    hashes = source_hashes()
    (out / 'manifest.json').write_text(json.dumps(dict(status='RUNNING', config=cfg,
                                                       source_hashes=hashes), indent=2))
    n_rec, start = 0, time.perf_counter()
    with gzip.open(out / 'tables.jsonl.gz', 'wt') as raw:
        for seed, split in cfg['seeds']:
            for load in cfg['loads']:
                eid = f'seed{seed}_load{load:g}'
                n = cfg['warm'] + (cfg['snapshots'] - 1) * cfg['stride'] + 1
                scenario = make_grid_scenario(out / 'scenarios' / eid, rows=cfg['rows'], cols=cfg['cols'],
                    traffic_seed=seed, horizon_s=10 * (n + cfg['horizon'] + 5), mean_headway_s=load)
                env = make_broadcast_env(scenario, budget_spec=BudgetTraceSpec(kind='bursty',
                    k=cfg['rows'] * cfg['cols'] // 2, k_low=1), n_decisions=n, mode='oracle')
                env.reset(budget_seed=1000 + seed)
                topology = {i: env.public_topology(i) for i in range(env.n_agents)}
                down, onward = build_static(topology)
                actor = lambda i, v: mp2_action(v, topology[i], down, onward)
                rng = np.random.default_rng(7000 + seed * 10 + int(load))
                for t in range(n):
                    with no_oracle_access(env):
                        context = env.scheduler_context()
                        rotation = t % env.n_agents
                        ranking = tuple(range(rotation, env.n_agents)) + tuple(range(rotation))
                        env.commit_global_ranking(ranking)
                        k = env.reveal_budget()
                    rec = None
                    if t >= cfg['warm'] and (t - cfg['warm']) % cfg['stride'] == 0:
                        before = fingerprint(env)
                        f, joint, unique = joint_table(env, actor, cfg['horizon'])
                        pays = fresh_payloads(env)
                        het = hetero_analysis(env, actor, cfg['horizon'], rng, args.sweeps)
                        if fingerprint(env) != before:
                            raise AssertionError('diagnostics changed the live state')
                        rec = dict(episode_id=eid, split=split, traffic_seed=seed, headway=load, t=t,
                                   m=env.n_agents, features=context.features(),
                                   cached_queue_ranking=list(context.cached_queue_ranking()),
                                   values=f, unique_joint_actions=unique,
                                   fresh_features=[x for p in pays for x in payload_features(p)],
                                   bids=[min(255, int(sum(p.waiting))) for p in pays],
                                   hetero=het, cached_queue_headroom=headroom(f, context.cached_queue_ranking()))
                    with no_oracle_access(env):
                        env.submit_broadcast(ranking[:k])
                        views = env.transmit()
                        bad = env.check_access_invariants(views)
                        if bad:
                            raise AssertionError(bad)
                        _, _, step = env.step({i: actor(i, v) for i, v in views.items()})
                    if step['messages'] != k:
                        raise AssertionError('packet accounting failed')
                    if rec is not None:
                        raw.write(json.dumps(rec, allow_nan=False) + '\n'); raw.flush(); n_rec += 1
                        h = rec['hetero']
                        print(f'{eid} t={t}: {unique} joint actions; hetero shared {h["v_best_shared"]:.1f} '
                              f'per-recv {h["v_per_receiver"]:.1f} ({h["n_distinct_joint"]} rollouts); '
                              f'{n_rec} records, {time.perf_counter() - start:.0f}s', flush=True)
    if source_hashes() != hashes:
        raise RuntimeError('source changed during collection')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', config=cfg, source_hashes=hashes,
        evidence_class='ORACLE DIAGNOSTIC; frozen MP2, held-phase horizon; not learned MARL',
        fresh_features='ORACLE ONLY (information ceiling)', bids='1 byte/agent/step charged control',
        records=n_rec, table_sha256=hashlib.sha256((out / 'tables.jsonl.gz').read_bytes()).hexdigest(),
        seconds=time.perf_counter() - start), indent=2))
    print(f'COMPLETE: {out} ({n_rec} records)', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True, type=Path)
    p.add_argument('--sweeps', type=int, default=3)
    p.add_argument('--smoke', action='store_true', help='2 episodes only, for wiring')
    a = p.parse_args()
    if a.smoke:
        _orig = profile
        def profile(name):  # noqa: F811
            c = _orig('pilot'); c['seeds'] = [(11, 'train')]; c['loads'] = [8.0]; c['snapshots'] = 2
            return c
    run(a)
