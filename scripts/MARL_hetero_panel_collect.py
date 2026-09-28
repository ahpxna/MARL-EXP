#!/usr/bin/env python3
"""General PANEL collector: prefix live policy, every development field computed LIVE.

Used for fresh confirmation panels, capacity-process panels and held-out-load panels.  The label
definition is the B1 one (live K + 3 random capacity vectors, the same candidate family, oracle
held-phase values, frozen MP2, H = 3).  Unlike the replay pipeline, every field is computed from
the SAME live state at the snapshot (as MARL_hetero_onpolicy_collect.py does), so capacity
processes that the replays cannot reproduce are supported:
  --capacity iid     k_i ~ U{1..m-2} i.i.d. per step (the environment default; B1-B4)
  --capacity fixed   k_i drawn once per episode from U{1..m-2}, constant over time
  --capacity bursty  per receiver Gilbert-Elliott chain: good -> k_hi_i ~ U{4..m-2} (per episode),
                     bad -> 1; P(good->bad) = 0.2, P(bad->good) = 0.3, start good
  --capacity low     k_i ~ U{1..3} i.i.d.      (shifted low)
  --capacity high    k_i ~ U{5..m-2} i.i.d.    (shifted high)
The process is written into the environment's trace right after reset, seeded by the capacity
seed; the 3 extra labelled capacity vectors stay U{1..m-2} (coverage), and endpoints that concern
the process use the LIVE-K group only.
Outputs (next to --out): labels_<n>, mirror_<n>, response_<n>, bid3_<n>, bid2_<n>.
Checks: labels leave the live state unchanged; mirror == receiver caches after every
transmission; the local MP2 score function matches mp2_action; sources unchanged.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import N_SLOTS
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.MARL_cheap_screen import fingerprint
from scripts.MARL_cheap_checks_v2 import payload_features, fresh_payloads
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC, candidates, Labeler, masks
from scripts.MARL_hetero_response_replay import checked, gap_of, LegalView
from scripts.MARL_hetero_bid_replay import coefficients, request
from scripts.MARL_hetero_bid_replay_v2 import gapbin
from scripts.MARL_hetero_closed_loop import make_env

SOURCES = ['scripts/MARL_hetero_panel_collect.py', 'scripts/MARL_hetero_closed_loop.py',
           'scripts/MARL_hetero_pilot_collect.py', 'scripts/MARL_hetero_response_replay.py',
           'scripts/MARL_hetero_bid_replay.py', 'scripts/MARL_hetero_bid_replay_v2.py',
           'envs/external/cityflow_hetero_mirror.py', 'envs/external/cityflow_hetero.py']
SNAPS = [10, 13, 16, 19, 22, 25]
NAMES = {'labels': 'labels.jsonl.gz', 'mirror': 'mirror_diag.jsonl.gz', 'response': 'response_diag.jsonl.gz',
         'bid3': 'bid3_diag.jsonl.gz', 'bid2': 'bid2_diag.jsonl.gz'}


def unmask(x):
    return [j for j in range(16) if (x >> j) & 1]


def capacity_trace(kind, n_dec, m, seed):
    rng = np.random.default_rng([int(seed), 0xCA9])
    hi = m - 2
    if kind == 'iid':
        return None
    if kind == 'fixed':
        return np.repeat(rng.integers(1, hi + 1, size=(1, m)), n_dec, axis=0)
    if kind == 'low':
        return rng.integers(1, 4, size=(n_dec, m))
    if kind == 'high':
        return rng.integers(5, hi + 1, size=(n_dec, m))
    if kind == 'bursty':
        khi = rng.integers(4, hi + 1, size=m); out = np.zeros((n_dec, m), np.int64); good = np.ones(m, bool)
        for t in range(n_dec):
            out[t] = np.where(good, khi, 1)
            u = rng.random(m); good = np.where(good, u >= 0.2, u < 0.3)
        return out
    raise ValueError(kind)


def run(a):
    out = Path(a.out).resolve()
    D = {k: out.parent / f'{k}_{out.name}' for k in NAMES}
    for d in D.values():
        d.mkdir(parents=True, exist_ok=False)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    eps = [(s, h) for s in a.seeds for h in a.headways][a.shard::a.nshards]
    fh = {k: gzip.open(D[k] / NAMES[k], 'wt') for k in D}
    n, start = 0, time.perf_counter()
    for seed, load in eps:
        eid0, env, topo, down, onward = make_env(out, seed, load, f'panel_{a.shard}')
        eid = f'{eid0}_{a.tag}'; m = env.n_agents
        tr = capacity_trace(a.capacity, N_DEC, m, 5000 + 10 * seed + int(load))
        if tr is not None:
            env._trace = tr
        coef = {i: coefficients(topo[i], down, onward) for i in range(m)}
        rngc = np.random.default_rng(20000 + 10 * seed + int(load))
        for t in range(N_DEC):
            with no_oracle_access(env):
                ctx = env.scheduler_context(); z = ctx.features(); order = tuple(ctx.cached_queue_ranking())
                def forbid(*_, **__):
                    raise AssertionError('fresh sensor read while building legal features')
                env._summary = env._sensor = forbid
                try:
                    mir = env.mirror_features()
                finally:
                    del env._summary, env._sensor
                env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
            if t in SNAPS:
                lab = Labeler(env, lambda i, v: mp2_action(v, topo[i], down, onward))
                before = fingerprint(env)
                Ks = [K] + [[int(x) for x in rngc.integers(1, m - 1, size=m)] for _ in range(3)]
                groups, joint = [], []
                for Kx in Ks:
                    cands = candidates(order, Kx, m, rngc)
                    groups.append(dict(K=Kx, profiles=[masks(p) for p in cands], values=[lab.value(p) for p in cands]))
                    joint.append([list(lab.joint(p)) for p in cands])
                priv = [x for p in fresh_payloads(env) for x in payload_features(p)]
                pk = ctx.packets
                own = [list(pk[i].waiting) if pk[i] is not None else [0] * N_SLOTS for i in range(m)]
                memo = {}
                def pact(i, mask):
                    if (i, mask) not in memo:
                        S = set(unmask(mask)); ent = {}
                        for j in env.neighbours[i]:
                            if j in S:
                                ent[j] = pk[j]
                            else:
                                e = env.mirror.entry(i, j); ent[j] = None if e is None else e[0]
                        memo[(i, mask)] = checked(LegalView(own[i], ent), topo[i], down, onward)
                    return memo[(i, mask)]
                pjoint = [[[int(pact(i, pm[i])[0]) for i in range(m)] for pm in g['profiles']] for g in groups]
                lgapP = [[gap_of(pact(i, sum(1 << j for j in s))[1]) for i, s in enumerate(prefix_sets(order, g['K']))] for g in groups]
                rbid, b3, b2 = [], [], []; now = env._now()
                for i in range(m):
                    v = env._build_view(i)
                    if v.inbox:
                        raise AssertionError('receiver view has an inbox before transmission')
                    act, sc = checked(v, topo[i], down, onward)
                    g_ = gap_of(sc)
                    rbid.append(dict(pref=int(act), gap=g_, own=[float(x) for x in np.asarray(v.lane_waiting).sum(axis=1)]))
                    o = sorted(sc, key=lambda p: -sc[p]); p1, p2 = o[0], o[1]
                    c = [coef[i][p1].get(j, 0.0) - coef[i][p2].get(j, 0.0) for j in range(m)]
                    age = [(-1.0 if env.mirror.entry(i, j) is None else float(now - env.mirror.entry(i, j)[1])) if j != i else -1.0
                           for j in range(m)]
                    b3.append(dict(p1=int(p1), p2=int(p2), gapbin=gapbin(g_), gap_true=g_, c=c, age=age))
                    rq, rage = request(v, sc, coef[i])
                    b2.append(dict(pref=int(act), gap=g_, req=int(rq), req_age=rage))
                if fingerprint(env) != before:
                    raise AssertionError('labels changed the live state')
                base = dict(episode_id=eid, split=a.split, traffic_seed=seed, headway=load, t=t)
                fh['labels'].write(json.dumps(dict(base, m=m, z=z, privileged=priv, order=list(order), groups=groups,
                                                   rollouts=len(lab.vals), capacity=a.capacity)) + '\n')
                fh['mirror'].write(json.dumps(dict(base, mirror=mir, joint=joint)) + '\n')
                fh['response'].write(json.dumps(dict(base, pjoint=pjoint, lgapP=lgapP, bid=rbid)) + '\n')
                fh['bid3'].write(json.dumps(dict(base, bid=b3)) + '\n')
                fh['bid2'].write(json.dumps(dict(base, bid=b2)) + '\n')
                for f in fh.values():
                    f.flush()
                n += 1
            with no_oracle_access(env):
                env.submit_profile(prefix_sets(order, K), R=0)
                views = env.transmit(); env.verify_mirror()
                env.step({i: mp2_action(v, topo[i], down, onward) for i, v in views.items()})
        print(f'{a.split} {eid}: {n} snapshots, {time.perf_counter() - start:.0f}s', flush=True)
    for f in fh.values():
        f.close()
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during collection')
    lab_sha = hashlib.sha256((D['labels'] / 'labels.jsonl.gz').read_bytes()).hexdigest()
    for k, d in D.items():
        (d / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', records=n, episodes=eps, split=a.split,
            capacity=a.capacity, tag=a.tag, source_hashes=hashes, labels_sha256=lab_sha,
            evidence_class='PANEL labels (prefix live policy); oracle held-phase values; PRIVILEGED joint in mirror files'),
            indent=1))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True); p.add_argument('--split', required=True); p.add_argument('--tag', required=True)
    p.add_argument('--seeds', type=int, nargs='+', required=True)
    p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--capacity', default='iid', choices=['iid', 'fixed', 'bursty', 'low', 'high'])
    p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1)
    run(p.parse_args())
