#!/usr/bin/env python3
"""Step 3 pilot evaluation on the UNTOUCHED test panel (traffic seeds 61-64, never read before).

Replays each test episode with the same live protocol as the collector (heuristic base order,
R = 0).  At each preregistered snapshot, for the live K and 3 extra capacity vectors, and for each
predeclared byte cap (extra over the base prefix: 0, 28, 56, none):
  prefix               the fixed public heuristic base order, no repair
  learned_R1           same base + coordinate search over R<=1 moves scored by the critic
  direct_unrestricted  same critic, single-swap moves from the current set (no radius),
                       the SAME number of evaluator calls per pass
and privileged references (true values, not deployable):
  oracle_search_R1 / oracle_search_direct   the same searches scored by the TRUE value
  exact_R1 / exact_private                  exact optima (uncapped), by action-product enumeration
Search error of the deployable search = exact_R1 - oracle_search_R1 (uncapped).
True values: held-phase rollouts of the joint action each profile induces (oracle).
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import (prefix_sets, profile_cost, check_legal, coordinate_search,
                                         radius_moves, swap_moves, select, HeteroCritic)
from scripts.MARL_hetero_pilot_collect import SPLITS, LOADS, SNAPS, H, episode_env
from scripts.MARL_cheap_screen import fingerprint
from scripts.MARL_cheap_checks_v2 import payload_features, fresh_payloads
from scripts.MARL_hetero_exact_oracle import Snapshot

SOURCES = ['scripts/MARL_hetero_pilot_eval.py', 'scripts/MARL_hetero_pilot_collect.py',
           'scripts/MARL_hetero_exact_oracle.py', 'models/marl_hetero_selector.py',
           'envs/external/cityflow_hetero.py']
CAPS = [0, 28, 56, None]


def load_critics(folder):
    out = []
    for p in sorted(Path(folder).glob('critic_*.pt')):
        blob = torch.load(p, weights_only=False)
        c = HeteroCritic(blob['d_in'], hidden=blob['hidden'], seed=0)
        c.net.load_state_dict(blob['state']); c.net.eval(); c.mean = blob['mean']; c.std = blob['std']
        out.append((blob['variant'], blob['seed'], c))
    return out


def masks(prof):
    return [sum(1 << j for j in s) for s in prof]


def run(a):
    out = Path(a.out).resolve(); out.mkdir(parents=True, exist_ok=False)
    critics = load_critics(a.critics)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    (out / 'manifest.json').write_text(json.dumps(dict(status='RUNNING', critics=a.critics, source_hashes=hashes), indent=2))
    start = time.perf_counter(); n = 0
    with gzip.open(out / 'eval.jsonl.gz', 'wt') as raw:
        for seed in SPLITS['test']:
            for load in LOADS:
                eid, env, actor = episode_env(out, seed, load)
                m = env.n_agents
                rng = np.random.default_rng(30000 + 10 * seed + int(load))
                for t in range(max(SNAPS) + 1):
                    with no_oracle_access(env):
                        ctx = env.scheduler_context()
                        z = ctx.features(); order = tuple(ctx.cached_queue_ranking())
                        env.commit_global_ranking(order)
                        Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
                    if t in SNAPS:
                        before = fingerprint(env)
                        priv = [x for p in fresh_payloads(env) for x in payload_features(p)]
                        snap = Snapshot(env, actor, H)
                        truth = lambda prof: snap.value(tuple(snap.act[i][sum(1 << j for j in prof[i])] for i in range(m)))
                        Ks = [K] + [[int(x) for x in rng.integers(1, m - 1, size=m)] for _ in range(3)]
                        for kx, Kx in enumerate(Ks):
                            P = prefix_sets(order, Kx); b0 = profile_cost(order, Kx, P)[0]; v0 = truth(P)
                            ex1 = snap.best_profile(Kx, order, 1); exp_ = snap.best_profile(Kx, None, None)
                            base = dict(episode_id=eid, traffic_seed=seed, headway=load, t=t, k_index=kx, K=Kx,
                                        prefix_value=v0, prefix_bytes=b0,
                                        exact_R1=None if ex1 is None else ex1['value'],
                                        exact_private=None if exp_ is None else exp_['value'])
                            for extra in CAPS:
                                cap = None if extra is None else b0 + extra
                                recs = []
                                for name, moves, R in (('oracle_search_R1', radius_moves, 1),
                                                       ('oracle_search_direct', swap_moves, None)):
                                    S, _, calls = coordinate_search(order, Kx, lambda ps: [truth(p) for p in ps],
                                                                    moves, cap=cap)
                                    check_legal(order, Kx, S, R=R, cap=cap)
                                    recs.append(dict(method=name, critic=None, value=truth(S),
                                                     bytes=profile_cost(order, Kx, S)[0], calls=calls, profile=masks(S)))
                                for variant, cseed, critic in critics:
                                    zz = list(z) + (priv if variant == 'privileged' else [])
                                    for method in ('learned_R1', 'direct_unrestricted'):
                                        S, calls = select(method, zz, order, Kx, critic, m, cap=cap)
                                        recs.append(dict(method=method, critic=f'{variant}/{cseed}', value=truth(S),
                                                         bytes=profile_cost(order, Kx, S)[0], calls=calls,
                                                         profile=masks(S)))
                                for r in recs:
                                    raw.write(json.dumps(dict(base, cap_extra=extra, **r)) + '\n')
                        if fingerprint(env) != before:
                            raise AssertionError('evaluation changed the live state')
                        n += 1
                        print(f'{eid} t={t}: {len(snap.cache)} rollouts; {n} snapshots, '
                              f'{time.perf_counter() - start:.0f}s', flush=True)
                    with no_oracle_access(env):
                        env.submit_profile(prefix_sets(order, K), R=0)
                        views = env.transmit()
                        _, _, _ = env.step({i: actor(i, v) for i, v in views.items()})
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during evaluation')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', snapshots=n, critics=a.critics,
        source_hashes=hashes, eval_sha256=hashlib.sha256((out / 'eval.jsonl.gz').read_bytes()).hexdigest(),
        evidence_class='STEP 3 PILOT TEST; frozen MP2, held-phase H=3; test seeds 61-64 read once',
        seconds=time.perf_counter() - start), indent=2))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--critics', required=True); p.add_argument('--out', required=True)
    run(p.parse_args())
