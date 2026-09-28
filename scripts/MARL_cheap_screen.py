#!/usr/bin/env python3
"""Cheap test 1: exact global-broadcast repair headroom with a frozen MP2 actor.

This is an oracle screening dataset, NOT a learned-MARL comparison. Labels hold
phases for H decisions (no closed-loop continuation). All live collection actions
use paid packets and public-context round-robin scheduling. No zero-gap filtering.
Output is append-only raw tables + a COMPLETE manifest only after all assertions.
"""
from __future__ import annotations
import argparse
import dataclasses
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import BudgetTraceSpec, make_grid_scenario, view_fingerprint
from envs.external.cityflow_broadcast import make_broadcast_env
from models.marl_screening import no_oracle_access, headroom, episode_means
from scripts.DIAG_cityflow_set_objective_hops import build_static, mp2_action, analyse

DEPENDENCIES = ['scripts/MARL_cheap_screen.py', 'scripts/DIAG_cityflow_set_objective_hops.py',
 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_broadcast.py',
 'models/marl_revision_selector.py', 'models/marl_screening.py',
 'external_envs/repos/CityFlow/tools/generator/generate_json_from_grid.py',
 'external_envs/repos/CityFlow/tools/generator/generate_grid_scenario.py']


def source_hashes():
    return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
            for name in DEPENDENCIES if (ROOT/name).is_file()}


def fingerprint(env):
    return {'context': dataclasses.asdict(env.scheduler_context()),
            'views': {i: view_fingerprint(v) for i,v in env.views().items()},
            'stage': env.stage, 'step': env.decision_step, 'records': len(env.step_records)}


def joint_table(env, actor, horizon):
    m = env.n_agents
    if m > 10:
        raise ValueError('screening enumeration limited to m<=10')
    before = fingerprint(env)
    actions, values, cache = [], [], {}
    for mask in range(1 << m):
        selected = [i for i in range(m) if (mask >> i) & 1]
        views = env.counterfactual_broadcast_views(selected)
        joint = tuple(actor(i, views[i]) for i in range(m))
        if joint not in cache:
            cache[joint] = env.oracle_rollout_value(dict(enumerate(joint)), horizon)
        actions.append(list(joint)); values.append(cache[joint])
    # Same actions at the SAME restored state must give identical values. Check
    # both ends AFTER every other candidate was evaluated, not just twice in a row.
    for joint in (tuple(actions[0]), tuple(actions[-1])):
        again = env.oracle_rollout_value(dict(enumerate(joint)), horizon)
        if abs(again-cache[joint]) > 1e-9:
            raise AssertionError('rollout is not repeatable after other candidates')
    if fingerprint(env) != before:
        raise AssertionError('oracle labels changed the live state/context')
    return values, actions, len(cache)


def profile(name):
    if name == 'smoke':
        return dict(rows=2, cols=2, loads=[12.0], seeds=[(11,'train'),(21,'val'),(31,'test')],
                    warm=6, snapshots=2, stride=2, horizon=1)
    seeds = [(11,'train'), (21,'val'), (31,'test')] if name == 'screen' else [
             (11,'train'),(12,'train'),(13,'train'),(14,'train'),
             (21,'val'),(22,'val'),(31,'test'),(32,'test')]
    return dict(rows=3, cols=3, loads=[8.0,16.0], seeds=seeds,
                warm=10, snapshots=4 if name=='screen' else 12, stride=3, horizon=3)


def run(args):
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    cfg = profile(args.profile)
    hashes = source_hashes()
    (out/'manifest.json').write_text(json.dumps(dict(status='RUNNING', profile=args.profile,
        config=cfg, source_hashes=hashes), indent=2))
    summaries, episodes = [], []
    start = time.perf_counter()
    with gzip.open(out/'tables.jsonl.gz', 'wt') as raw:
        for seed, split in cfg['seeds']:
            for load in cfg['loads']:
                eid = f'seed{seed}_load{load:g}'
                n = cfg['warm']+(cfg['snapshots']-1)*cfg['stride']+1
                scenario = make_grid_scenario(out/'scenarios'/eid, rows=cfg['rows'], cols=cfg['cols'],
                    traffic_seed=seed, horizon_s=10*(n+cfg['horizon']+5), mean_headway_s=load)
                env = make_broadcast_env(scenario, budget_spec=BudgetTraceSpec(kind='bursty',
                    k=cfg['rows']*cfg['cols']//2, k_low=1), n_decisions=n, mode='oracle')
                env.reset(budget_seed=1000+seed)
                topology = {i: env.public_topology(i) for i in range(env.n_agents)}
                down, onward = build_static(topology)
                actor = lambda i, v: mp2_action(v, topology[i], down, onward)
                for t in range(n):
                    with no_oracle_access(env):
                        context = env.scheduler_context()
                        rotation = t % env.n_agents
                        ranking = tuple(range(rotation,env.n_agents))+tuple(range(rotation))
                        env.commit_global_ranking(ranking)
                        k = env.reveal_budget()
                    if t >= cfg['warm'] and (t-cfg['warm']) % cfg['stride'] == 0:
                        a0 = dict(env.access_log)
                        f, joint, unique = joint_table(env, actor, cfg['horizon'])
                        geometry, ok = analyse(f, env.n_agents)
                        if not ok:
                            raise AssertionError('frontier transcription failed')
                        heuristic = context.cached_queue_ranking()
                        rec = dict(episode_id=eid, split=split, traffic_seed=seed, headway=load,
                            t=t, m=env.n_agents, context=dataclasses.asdict(context),
                            features=context.features(), cached_queue_ranking=list(heuristic),
                            values=f, joint_actions=joint, unique_joint_actions=unique,
                            geometry_true_singletons=geometry, cached_queue_headroom=headroom(f,heuristic),
                            oracle_access_before=a0, oracle_access_after=dict(env.access_log))
                        # Live step assertion is attached before serializing this record.
                    else:
                        rec = None
                    before_live = dict(env.access_log)
                    with no_oracle_access(env):
                        env.submit_broadcast(ranking[:k])
                        views = env.transmit()
                        violations = env.check_access_invariants(views)
                        if violations:
                            raise AssertionError(violations)
                        _, _, step = env.step({i: actor(i,v) for i,v in views.items()})
                    if step['messages'] != k or step['payload_bytes'] != 25*k:
                        raise AssertionError('network-wide packet accounting failed')
                    if rec is not None:
                        rec.update(live_access_before=before_live, live_access_after=dict(env.access_log),
                                   live_step=step)
                        raw.write(json.dumps(rec, allow_nan=False)+'\n'); raw.flush()
                        summaries.append({key: rec[key] for key in ('episode_id','split','t','m',
                            'geometry_true_singletons','cached_queue_headroom')})
                        print(f'{eid} t={t}: {len(f)} sets, {unique} distinct actions; '
                              f'{len(summaries)} tables, {time.perf_counter()-start:.1f}s', flush=True)
                episodes.append(dict(episode_id=eid, split=split, scenario=scenario, summary=env.episode_summary()))
    if source_hashes() != hashes:
        raise RuntimeError('source changed during collection; refusing COMPLETE manifest')
    gains = episode_means(summaries, lambda r: sum(x['repair_gain'][1]
                for x in r['cached_queue_headroom'])/len(r['cached_queue_headroom']))
    manifest = dict(status='COMPLETE', profile=args.profile, config=cfg, source_hashes=hashes,
        evidence_class='ORACLE GLOBAL-BROADCAST SCREEN; frozen MP2, held-phase horizon; not learned MARL',
        scheduler_inputs='paid historical packets and public time only',
        value_units='negative sum of network waiting counts at H decision boundaries',
        timing_scope='zero transmission/computation delay; no runtime advantage claim',
        table_sha256=hashlib.sha256((out/'tables.jsonl.gz').read_bytes()).hexdigest(),
        records=len(summaries), episodes=episodes, cached_R1_gain_by_episode=gains,
        seconds=time.perf_counter()-start)
    (out/'summary.json').write_text(json.dumps(summaries, indent=2, allow_nan=False))
    (out/'manifest.json').write_text(json.dumps(manifest, indent=2, allow_nan=False))
    print(f'COMPLETE: {out} ({len(summaries)} tables)', flush=True)


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile', choices=['smoke','screen','pilot'], default='screen')
    p.add_argument('--out', required=True, type=Path)
    run(p.parse_args())
