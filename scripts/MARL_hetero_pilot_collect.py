#!/usr/bin/env python3
"""Step 3 pilot collector on the heterogeneous-receiver objective (PROTOCOL_HETERO_v0).

NEW independent traffic seeds (never used before): train 41-48, val 51-52, test 61-64, headway
8 and 16, snapshots t = 10,13,16,19,22,25 (6 per episode): 96 train / 24 val / 48 test contexts.
Live trajectory: public heuristic base order, R = 0 prefix, the heterogeneous transport.

At each train/val snapshot, BEFORE any diagnostic, z = scheduler_context().features() is saved
(paid cache + time).  Labels (ORACLE, offline only): for the live K and 3 extra capacity vectors,
true held-phase values of a deterministic candidate family around the base prefix:
all single-receiver one-swap profiles, 24 random R<=1 profiles, 24 random R<=2 profiles, 24
random unrestricted profiles.  Values come from rollouts of the joint action each profile
induces through the frozen MP2 actor (oracle counterfactual views).  Privileged current
summaries are saved separately for a diagnostic critic; they never enter the public critic.

--smoke: one short episode that additionally checks (contract A) that a non-prefix profile
gives the same live actor actions as its diagnostic counterfactual views with the same old cache.
Test-split episodes are NOT collected here; they are evaluated online by MARL_hetero_pilot_eval.py.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import BudgetTraceSpec, make_grid_scenario
from envs.external.cityflow_hetero import make_hetero_env
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.DIAG_cityflow_set_objective_hops import build_static, mp2_action
from scripts.MARL_cheap_screen import fingerprint
from scripts.MARL_cheap_checks_v2 import payload_features, fresh_payloads

SPLITS = {'train': [41, 42, 43, 44, 45, 46, 47, 48], 'val': [51, 52], 'test': [61, 62, 63, 64]}
LOADS = [8.0, 16.0]
SNAPS = [10, 13, 16, 19, 22, 25]
N_DEC, H, ROWS, COLS = 26, 3, 3, 3
DEPENDENCIES = ['scripts/MARL_hetero_pilot_collect.py', 'envs/external/cityflow_hetero.py',
                'envs/external/cityflow_broadcast.py', 'envs/external/cityflow_budgeted.py',
                'models/marl_hetero_selector.py', 'models/marl_screening.py',
                'scripts/DIAG_cityflow_set_objective_hops.py', 'scripts/MARL_cheap_checks_v2.py',
                'research/marl_budget/PROTOCOL_HETERO_v0.md']


def source_hashes():
    return {n: hashlib.sha256((ROOT / n).read_bytes()).hexdigest() for n in DEPENDENCIES}


def episode_env(out, seed, load, mode='oracle'):
    eid = f'seed{seed}_load{load:g}'
    scen = make_grid_scenario(out / 'scenarios' / eid, rows=ROWS, cols=COLS, traffic_seed=seed,
                              horizon_s=10 * (N_DEC + H + 5), mean_headway_s=load)
    env = make_hetero_env(scen, budget_spec=BudgetTraceSpec(kind='bursty', k=4, k_low=1),
                          n_decisions=N_DEC, capacity_seed=5000 + 10 * seed + int(load), mode=mode)
    env.reset(budget_seed=1000 + seed)
    topo = {i: env.public_topology(i) for i in range(env.n_agents)}
    down, onward = build_static(topo)
    actor = lambda i, v: mp2_action(v, topo[i], down, onward)
    return eid, env, actor


class Labeler:
    """Oracle labels at one snapshot: joint action of a profile, and its rollout value."""

    def __init__(self, env, actor):
        self.env, self.actor, self.m = env, actor, env.n_agents
        self.acts, self.vals = {}, {}

    def action(self, i, s):
        key = (i, s)
        if key not in self.acts:
            self.acts[key] = self.actor(i, self.env.counterfactual_view(i, sorted(s)))
        return self.acts[key]

    def joint(self, prof):
        return tuple(self.action(i, prof[i]) for i in range(self.m))

    def value(self, prof):
        j = self.joint(prof)
        if j not in self.vals:
            self.vals[j] = self.env.oracle_rollout_value(dict(enumerate(j)), H)
        return self.vals[j]


def candidates(order, K, m, rng):
    P = prefix_sets(order, K)
    out = {tuple(P)}
    for i in range(m):
        outside = [b for b in range(m) if b != i and b not in P[i]]
        for a in sorted(P[i]):
            for b in outside:
                prof = list(P); prof[i] = (P[i] - {a}) | {b}; out.add(tuple(prof))

    def swap(i, s, r):
        s = set(s)
        for _ in range(r):
            ins = sorted(s & P[i]); outs = [b for b in range(m) if b != i and b not in s and b not in P[i]]
            if not ins or not outs:
                break
            s.discard(int(rng.choice(ins))); s.add(int(rng.choice(outs)))
        return frozenset(s)
    for _ in range(24):
        out.add(tuple(swap(i, P[i], int(rng.random() < 0.5)) for i in range(m)))
    for _ in range(24):
        out.add(tuple(swap(i, P[i], int(rng.integers(0, 3))) for i in range(m)))
    for _ in range(24):
        prof = []
        for i in range(m):
            others = [j for j in range(m) if j != i]
            prof.append(frozenset(int(x) for x in rng.choice(others, size=K[i], replace=False)))
        out.add(tuple(prof))
    return sorted(out, key=lambda p: [sorted(s) for s in p])


def masks(prof):
    return [sum(1 << j for j in s) for s in prof]


def run(a):
    out = Path(a.out).resolve(); out.mkdir(parents=True, exist_ok=False)
    hashes = source_hashes()
    splits = ['train', 'val'] if not a.smoke else ['train']
    (out / 'manifest.json').write_text(json.dumps(dict(status='RUNNING', splits=splits, source_hashes=hashes), indent=2))
    n, start = 0, time.perf_counter()
    with gzip.open(out / 'labels.jsonl.gz', 'wt') as raw:
        for split in splits:
            seeds = SPLITS[split][:1] if a.smoke else SPLITS[split]
            for seed in seeds:
                for load in (LOADS[:1] if a.smoke else LOADS):
                    eid, env, actor = episode_env(out, seed, load)
                    m = env.n_agents
                    rng = np.random.default_rng(20000 + 10 * seed + int(load))
                    snaps = SNAPS[:2] if a.smoke else SNAPS
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
                            # contract A: live actions == diagnostic counterfactual actions (non-prefix profile)
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
                            print(f'  smoke t={t}: live == counterfactual for a non-prefix profile; '
                                  f'bytes {step["accounted_bytes"]} ({step["description"]})', flush=True)
    if source_hashes() != hashes:
        raise RuntimeError('source changed during collection')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', splits=splits, records=n,
        source_hashes=hashes, labels_sha256=hashlib.sha256((out / 'labels.jsonl.gz').read_bytes()).hexdigest(),
        evidence_class='ORACLE LABELS for the Step 3 pilot; frozen MP2, held-phase H=3',
        z='scheduler_context().features(): paid cache + time, saved before any diagnostic',
        privileged='ORACLE current summaries; diagnostic critic only', seconds=time.perf_counter() - start), indent=2))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    run(p.parse_args())
