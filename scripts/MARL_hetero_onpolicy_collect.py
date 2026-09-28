#!/usr/bin/env python3
"""B4 (DAgger-style) ON-POLICY collector: label states visited by a MIXED live policy.

B3 showed covariate shift: selectors trained on PREFIX-trajectory states stop editing once their
own patches move the system.  Here the live profile at every decision step is chosen by
  with probability beta        the oracle held-phase choice within the cap (expert)
  otherwise                    the frozen B2 selector (mlp_top2_joint, init seed rotating by
                               episode) with its frozen tau, bids charged inside the cap
and at snapshots t in SNAPS the same labels as the B1 collector are recorded (live K + 3 random
capacity vectors, the same candidate family, oracle held-phase values), together with every
field the development pipeline reads, computed LIVE from the same state (so no replay is needed):
  labels_*/labels.jsonl.gz, mirror_*/mirror_diag.jsonl.gz (legal mirror + PRIVILEGED joint
  actions), response_*/response_diag.jsonl.gz (legal MP2 response + receiver bids),
  bid3_*/bid3_diag.jsonl.gz (top-2 bids + scheduler-side quantities).
Episode ids carry the suffix '_op' so they never collide with prefix-trajectory episodes.
Checks: labels leave the live state unchanged (fingerprint); mirror == receiver caches after
every transmission; the local MP2 score function matches mp2_action; sources unchanged.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import N_SLOTS
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.MARL_cheap_screen import fingerprint
from scripts.MARL_cheap_checks_v2 import payload_features, fresh_payloads
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC, candidates, Labeler, masks
from scripts.MARL_hetero_diag_train_v2 import choose, anchor
from scripts.MARL_hetero_response_replay import checked, gap_of, LegalView
from scripts.MARL_hetero_bid_replay import coefficients
from scripts.MARL_hetero_bid_replay_v2 import gapbin
from scripts.MARL_hetero_closed_loop import make_env, receiver_bids, live_group
from scripts.MARL_hetero_closed_loop_v2 import add_top2, soft_live, _Lazy
from scripts.MARL_hetero_b2_confirm_v2 import features as conf_features, BID

SOURCES = ['scripts/MARL_hetero_onpolicy_collect.py', 'scripts/MARL_hetero_closed_loop_v2.py',
           'scripts/MARL_hetero_closed_loop.py', 'scripts/MARL_hetero_pilot_collect.py',
           'scripts/MARL_hetero_response_replay.py', 'scripts/MARL_hetero_bid_replay_v2.py',
           'envs/external/cityflow_hetero_mirror.py', 'envs/external/cityflow_hetero.py']
SNAPS = [4, 7, 10, 13, 16, 19, 22, 25]
SPLITS = {'train': list(range(301, 365)), 'select': list(range(401, 409))}


def unmask(x):
    return [j for j in range(16) if (x >> j) & 1]


def run(a):
    out = Path(a.out).resolve()
    for sub in ('labels', 'mirror', 'response', 'bid3'):
        (out.parent / f'{sub}_{out.name}').mkdir(parents=True, exist_ok=False)
    D = {sub: out.parent / f'{sub}_{out.name}' for sub in ('labels', 'mirror', 'response', 'bid3')}
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    devmap = json.loads(Path(a.dev_map).read_text()); d = Path(devmap['mlp_top2_joint'])
    netA = nn.Sequential(nn.Linear(23, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, 3))
    netA.load_state_dict(torch.load(d / 'stageA.pt', weights_only=False)); netA.eval()
    pols = []
    for s in (0, 1, 2):
        job = json.loads((d / f'job_mlp_top2_joint_s{s}.json').read_text())
        t = job['results']['mlp_top2_joint']['+84']['direct']['tau']
        ck = torch.load(d / f'model_mlp_top2_joint_s{s}.pt', weights_only=False)
        pols.append((_Lazy(ck), ck, np.inf if t is None else t))
    eps = [(sp, s, load) for sp in ('train', 'select') for s in (SPLITS[sp][:1] if a.smoke else SPLITS[sp])
           for load in ((8.0,) if a.smoke else (8.0, 16.0))][a.shard::a.nshards]
    snaps = SNAPS[:2] if a.smoke else SNAPS
    NAMES = {'labels': 'labels.jsonl.gz', 'mirror': 'mirror_diag.jsonl.gz', 'response': 'response_diag.jsonl.gz',
             'bid3': 'bid3_diag.jsonl.gz'}
    fh = {k: gzip.open(D[k] / NAMES[k], 'wt') for k in D}
    n, start = 0, time.perf_counter(); cap = 84
    for ei, (split, seed, load) in enumerate(eps):
        eid0, env, topo, down, onward = make_env(out, seed, load, f'op_{a.shard}')
        eid = eid0 + '_op'; m = env.n_agents
        coef = {i: coefficients(topo[i], down, onward) for i in range(m)}
        rng = np.random.default_rng(40000 + 10 * seed + int(load)); rngc = np.random.default_rng(20000 + 10 * seed + int(load))
        net, ck, tau = pols[(seed + int(load)) % 3]
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
            lab = Labeler(env, lambda i, v: mp2_action(v, topo[i], down, onward))
            if t in snaps:
                before = fingerprint(env)
                Ks = [K] + [[int(x) for x in rngc.integers(1, m - 1, size=m)] for _ in range(3)]
                groups, joint = [], []
                for Kx in Ks:
                    cands = candidates(order, Kx, m, rngc)
                    groups.append(dict(K=Kx, profiles=[masks(p) for p in cands], values=[lab.value(p) for p in cands]))
                    joint.append([list(lab.joint(p)) for p in cands])
                priv = [x for p in fresh_payloads(env) for x in payload_features(p)]
                # legal response model + receiver bids (as MARL_hetero_response_replay.py)
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
                rbid, b3 = [], []; now = env._now()
                for i in range(m):
                    v = env._build_view(i)
                    act, sc = checked(v, topo[i], down, onward)
                    rbid.append(dict(pref=int(act), gap=gap_of(sc), own=[float(x) for x in np.asarray(v.lane_waiting).sum(axis=1)]))
                    o = sorted(sc, key=lambda p: -sc[p]); p1, p2 = o[0], o[1]
                    c = [coef[i][p1].get(j, 0.0) - coef[i][p2].get(j, 0.0) for j in range(m)]
                    age = [(-1.0 if env.mirror.entry(i, j) is None else float(now - env.mirror.entry(i, j)[1])) if j != i else -1.0
                           for j in range(m)]
                    b3.append(dict(p1=int(p1), p2=int(p2), gapbin=gapbin(gap_of(sc)), gap_true=gap_of(sc), c=c, age=age))
                if fingerprint(env) != before:
                    raise AssertionError('labels changed the live state')
                base = dict(episode_id=eid, split=split, traffic_seed=seed, headway=load, t=t)
                fh['labels'].write(json.dumps(dict(base, m=m, z=z, privileged=priv, order=list(order), groups=groups,
                                                   rollouts=len(lab.vals))) + '\n')
                fh['mirror'].write(json.dumps(dict(base, mirror=mir, joint=joint)) + '\n')
                fh['response'].write(json.dumps(dict(base, pjoint=pjoint, lgapP=lgapP, bid=rbid)) + '\n')
                fh['bid3'].write(json.dumps(dict(base, bid=b3)) + '\n')
                for f in fh.values():
                    f.flush()
                n += 1
            # live mixed policy on the live-K candidate family
            cands = candidates(order, K, m, rng)
            g, profs = live_group(z, K, mir, receiver_bids(env, topo, down, onward), order, cands)
            if rng.random() < a.beta:
                vals = np.asarray([lab.value(p) for p in profs], float)
                j = choose(g['ev'], vals - vals[g['ev']['ip']], cap, False, 0.0); who = 'expert'
            else:
                add_top2(g, env, topo, down, onward, coef); soft_live(g, netA)
                c, dd = conf_features(g, 'mlp_top2_joint')
                x = torch.as_tensor(np.concatenate([np.tile((c - ck['cm']) / ck['cs'], (g['C'], 1)), (dd - ck['dm']) / ck['ds']], 1).astype(np.float32))
                with torch.no_grad():
                    an = anchor(g['ev'], net(x)[0].numpy().astype(float))
                j = choose(g['ev'], an, cap - BID['mlp_top2_joint'], False, tau); who = 'policy'
            with no_oracle_access(env):
                env.submit_profile([set(s) for s in profs[j]], R=None, cap=g['ev']['b0'] + cap)
                views = env.transmit(); env.verify_mirror()
                env.step({i: mp2_action(v, topo[i], down, onward) for i, v in views.items()})
        print(f'{split} {eid}: {n} snapshots, {time.perf_counter() - start:.0f}s', flush=True)
    for f in fh.values():
        f.close()
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during collection')
    lab_sha = hashlib.sha256((D['labels'] / 'labels.jsonl.gz').read_bytes()).hexdigest()
    for k, dd in D.items():
        (dd / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', records=n, episodes=eps, beta=a.beta,
            source_hashes=hashes, labels_sha256=lab_sha, dev_map=devmap,
            evidence_class='ON-POLICY (mixed expert/frozen-selector) labels; oracle held-phase values; PRIVILEGED joint in mirror files'),
            indent=1, default=str))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True, help='suffix path: writes labels_<name>, mirror_<name>, response_<name>, bid3_<name> next to it')
    p.add_argument('--dev-map', required=True); p.add_argument('--beta', type=float, default=0.5)
    p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1)
    p.add_argument('--smoke', action='store_true')
    run(p.parse_args())
