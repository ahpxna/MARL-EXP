#!/usr/bin/env python3
"""B1 learning-curve collector (research/marl_budget/PROTOCOL_B1_LEARNING_CURVE_20260927.md).

Identical environment, actor, snapshots, capacity vectors and candidate family to
MARL_hetero_pilot_collect.py, whose episode_env / Labeler / candidates / masks are IMPORTED
unchanged.  Only the seeds and split names differ:
  train 301-364, select 401-408, test 501-508 (never used before), headway 8 and 16.
--shard i --nshards n collects every n-th episode of the fixed episode list, so shards can run in
parallel.  Test labels are written but sealed: only the final evaluation reads them.
--smoke: one episode per split, first headway, two snapshots, plus the pilot's contract-A check
(live actions == counterfactual actions for a non-prefix profile).  The contract-A step submits a
non-prefix profile, so smoke labels are NOT replayable by MARL_hetero_mirror_replay.py.
--mini: the same episodes and snapshots as --smoke but the live trajectory of the full run
(prefix, R = 0), so the replay and training path can be smoke-tested end to end.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.MARL_cheap_screen import fingerprint
from scripts.MARL_cheap_checks_v2 import payload_features, fresh_payloads
from scripts.MARL_hetero_pilot_collect import (episode_env, Labeler, candidates, masks, LOADS, SNAPS,
                                               DEPENDENCIES as PILOT_DEPS)

SPLITS = {'train': list(range(301, 365)), 'select': list(range(401, 409)), 'test': list(range(501, 509))}
DEPENDENCIES = PILOT_DEPS + ['scripts/MARL_hetero_lc_collect.py',
                            'research/marl_budget/PROTOCOL_B1_LEARNING_CURVE_20260927.md']


def source_hashes():
    return {n: hashlib.sha256((ROOT / n).read_bytes()).hexdigest() for n in DEPENDENCIES}


def episode_list(smoke):
    eps = []
    for split in ('train', 'select', 'test'):
        seeds = SPLITS[split][:1] if smoke else SPLITS[split]
        for seed in seeds:
            for load in (LOADS[:1] if smoke else LOADS):
                eps.append((split, seed, load))
    return eps


def run(a):
    out = Path(a.out).resolve(); out.mkdir(parents=True, exist_ok=False)
    hashes = source_hashes()
    eps = episode_list(a.smoke or a.mini)[a.shard::a.nshards]
    (out / 'manifest.json').write_text(json.dumps(dict(status='RUNNING', episodes=eps, source_hashes=hashes), indent=2))
    n, start = 0, time.perf_counter()
    with gzip.open(out / 'labels.jsonl.gz', 'wt') as raw:
        for split, seed, load in eps:
            eid, env, actor = episode_env(out, seed, load)
            m = env.n_agents
            rng = np.random.default_rng(20000 + 10 * seed + int(load))
            snaps = SNAPS[:2] if (a.smoke or a.mini) else SNAPS
            for t in range(max(snaps) + 1):
                with no_oracle_access(env):
                    ctx = env.scheduler_context()
                    z = ctx.features(); order = tuple(ctx.cached_queue_ranking())
                    env.commit_global_ranking(order)
                    Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
                if t in snaps:
                    before = fingerprint(env)
                    lab = Labeler(env, actor)
                    Ks = [K] + [[int(x) for x in rng.integers(1, m - 1, size=m)] for _ in range(3)]
                    groups = []
                    for Kx in Ks:
                        cands = candidates(order, Kx, m, rng)
                        groups.append(dict(K=Kx, profiles=[masks(p) for p in cands],
                                           values=[lab.value(p) for p in cands]))
                    priv = [x for p in fresh_payloads(env) for x in payload_features(p)]
                    if fingerprint(env) != before:
                        raise AssertionError('labels changed the live state')
                    raw.write(json.dumps(dict(episode_id=eid, split=split, traffic_seed=seed,
                        headway=load, t=t, m=m, z=z, privileged=priv, order=list(order),
                        groups=groups, rollouts=len(lab.vals))) + '\n'); raw.flush(); n += 1
                    print(f'{split} {eid} t={t}: {sum(len(g["profiles"]) for g in groups)} profiles, '
                          f'{len(lab.vals)} rollouts; {n} records, {time.perf_counter() - start:.0f}s', flush=True)
                prof = prefix_sets(order, K)
                if a.smoke and t in snaps:
                    P = prof
                    i0 = int(np.argmax(K)); outside = [b for b in range(m) if b != i0 and b not in P[i0]]
                    if outside:
                        prof = list(P); a0 = sorted(P[i0])[0]; prof[i0] = (P[i0] - {a0}) | {outside[0]}
                    cf = {i: actor(i, env.counterfactual_view(i, sorted(prof[i]))) for i in range(m)}
                with no_oracle_access(env):
                    env.submit_profile(prof, R=1 if a.smoke else 0)
                    views = env.transmit()
                    bad = env.check_access_invariants(views)
                    if bad:
                        raise AssertionError(bad)
                    live = {i: actor(i, v) for i, v in views.items()}
                    _, _, step = env.step(live)
                if a.smoke and t in snaps:
                    if live != cf:
                        raise AssertionError(f'live actions {live} != counterfactual {cf}')
                    print(f'  smoke t={t}: live == counterfactual for a non-prefix profile', flush=True)
    if source_hashes() != hashes:
        raise RuntimeError('source changed during collection')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', episodes=eps, records=n,
        source_hashes=hashes, labels_sha256=hashlib.sha256((out / 'labels.jsonl.gz').read_bytes()).hexdigest(),
        evidence_class='ORACLE LABELS for B1; frozen MP2, held-phase H=3; test split sealed',
        z='scheduler_context().features(): paid cache + time, saved before any diagnostic',
        privileged='ORACLE current summaries; diagnostic only', smoke=a.smoke, mini=a.mini,
        seconds=time.perf_counter() - start), indent=2))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    p.add_argument('--mini', action='store_true')
    p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1)
    run(p.parse_args())
