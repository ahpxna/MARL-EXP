#!/usr/bin/env python3
"""E3 evaluator labels with a DECLARED continuation for a FROZEN learned actor (readiness audit §5).

    cont_H(S) = - sum_{h=1..H} waiting_h   when profile S is transmitted at step t and steps
                                           t+1..t+H-1 run the live loop with c = (prefix scheduler,
                                           the same frozen actor, greedy);
the base trajectory up to t is (prefix scheduler, frozen actor).  This is f_X^{pi,c}(S) of the audit
with pi = c's actor; it is NOT the held-phase label.  Candidates: the B1 family on live K.
Per state it also stores the LEGAL scheduler inputs (z = SchedulerContext.features, K, the receiver
mirror features, the committed order) and the receiver-side bid of the new actor: from each
receiver's OWN pre-transmission view, the actor's top-2 phases and the logit gap (to be quantised
into 1 byte by the bid consumer).  Continuation values are computed by deterministic replay from
reset on a fresh engine per candidate (as in MARL_hetero_target_diag.py).
Self-checks (reported; the run is marked SELF-CHECK FAIL if any fails): replay reproduces order and
K at t; cont_H(P) equals the base run's queues; every actor step passes the access invariants.
Evidence class: ORACLE LABELS (training/diagnostic data), not a learner.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets, profile_cost
from models.marl_comm_actor import CommAdapter, ActorNet
from scripts.MARL_hetero_pilot_collect import N_DEC, H, candidates
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios

SOURCES = ['scripts/MARL_e3_continuation_labels.py', 'scripts/MARL_e3_actor_train.py', 'models/marl_comm_actor.py',
           'scripts/MARL_hetero_target_diag.py', 'scripts/MARL_hetero_pilot_collect.py', 'envs/external/cityflow_hetero.py',
           'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py', 'models/marl_receiver_mirror.py']
SPLITS = {'train': range(301, 365), 'select': range(401, 409), 'dev': range(501, 509)}


class Policy:
    def __init__(self, ck, topo, interval):
        self.adapter = CommAdapter(topo, N_DEC, interval)
        if self.adapter.schema() != ck['schema']:
            raise SystemExit('adapter schema differs from the checkpoint')
        self.actor = ActorNet(self.adapter.dim, ck['config']['hidden']); self.actor.load_state_dict(ck['actor']); self.actor.eval()
        self.mask = torch.as_tensor(self.adapter.valid_mask())

    def logits(self, views):
        X = np.stack([self.adapter.encode(views[i], 'actual') for i in range(len(views))])
        with torch.no_grad():
            return self.actor(torch.as_tensor(X), self.mask).numpy()

    def act(self, views):
        return {i: int(a) for i, a in enumerate(self.logits(views).argmax(-1))}


def step_with(env, pol, sets):
    with no_oracle_access(env):
        env.submit_profile([set(s) for s in sets], R=None)
        views = env.transmit(); env.verify_mirror()
        bad = env.check_access_invariants(views)
        if bad:
            raise AssertionError(f'access invariant: {bad[:3]}')
        acts = pol.act(views)
        _, _, rec = env.step(acts)
    return float(rec['queue']), tuple(acts[i] for i in range(env.n_agents))


def replay(sc, seed, load, pol, t, S):
    env, _, _, _ = sc.env(seed, load)
    for _ in range(t):
        with no_oracle_access(env):
            order, K = grant(env)
        step_with(env, pol, prefix_sets(order, K))
    with no_oracle_access(env):
        order, K = grant(env)
    q = []; q0, j0 = step_with(env, pol, S); q.append(q0)
    for _ in range(H - 1):
        with no_oracle_access(env):
            o, k = grant(env)
        q.append(step_with(env, pol, prefix_sets(o, k))[0])
    return order, K, q, j0


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    ck = torch.load(Path(a.ckpt), weights_only=False); sc = Scenarios(out)
    eps = [(s, h) for s in SPLITS[a.split] for h in (8.0, 16.0)]
    if a.limit:
        eps = eps[:a.limit]
    eps = eps[a.shard::a.nshards]
    fh = gzip.open(out / 'labels.jsonl.gz', 'wt'); fails = []; n = 0; t0 = time.perf_counter()
    for seed, load in eps:
        env, topo, _, _ = sc.env(seed, load); m = env.n_agents; pol = Policy(ck, topo, env.action_interval)
        rngc = np.random.default_rng(60000 + 10 * seed + int(load)); base_q = []; snap = {}
        for t in range(max(a.snaps) + H):
            with no_oracle_access(env):
                ctx = env.scheduler_context(); z = ctx.features(); mir = env.mirror_features()
                order, K = grant(env)
                pre = {i: env._build_view(i) for i in range(m)}            # receiver-local, before transmission
            if t in a.snaps:
                lg = pol.logits(pre); bid = []
                for i in range(m):
                    o = np.argsort(-lg[i]); bid.append(dict(p1=int(o[0]), p2=int(o[1]), gap=float(lg[i][o[0]] - lg[i][o[1]])))
                P = tuple(frozenset(s) for s in prefix_sets(order, K))
                cands = [P] + [tuple(frozenset(s) for s in c) for c in candidates(order, K, m, rngc) if tuple(frozenset(s) for s in c) != P]
                b0 = profile_cost(order, K, [set(s) for s in P])[0]
                snap[t] = dict(order=list(order), K=K, z=[float(x) for x in z], mirror=[float(x) for x in mir], bid=bid, b0=int(b0),
                               cands=[dict(sets=[sorted(s) for s in c], bytes=int(profile_cost(order, K, [set(s) for s in c])[0])) for c in cands])
            base_q.append(step_with(env, pol, prefix_sets(order, K))[0])
        for t, st in snap.items():
            for ci, c in enumerate(st['cands']):
                order, K, q, j0 = replay(sc, seed, load, pol, t, [set(s) for s in c['sets']])
                if list(order) != st['order'] or K != st['K']:
                    fails.append(f'{seed}/{load}/t{t}/c{ci}: replay order or K differs')
                c['cont'] = -float(sum(q)); c['cont_1'] = -float(q[0]); c['joint'] = list(j0)
            ref = -float(sum(base_q[t:t + H]))
            if abs(st['cands'][0]['cont'] - ref) > 1e-9:
                fails.append(f'{seed}/{load}/t{t}: cont(P) {st["cands"][0]["cont"]} != base {ref}')
            g = np.array([c['cont'] for c in st['cands']]) - st['cands'][0]['cont']
            fh.write(json.dumps(dict(episode_id=f'seed{seed}_load{load:g}', split=a.split, traffic_seed=seed, headway=load, t=t, m=m, **st)) + '\n'); fh.flush(); n += 1
            print(f'[{time.perf_counter() - t0:.0f}s] seed{seed}_load{load:g} t{t}: {len(st["cands"])} cands, best cont gain {g.max():+.0f}, '
                  f'positive {int((g > 0).sum())}, fails {len(fails)}', flush=True)
    fh.close()
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS' if not fails else 'SELF-CHECK FAIL',
        failures=fails[:50], args=vars(a), states=n, source_hashes=h0, ckpt_it=ck['it'], ckpt_select=ck['select'],
        seconds=time.perf_counter() - t0, evidence_class='ORACLE continuation labels for a frozen learned actor'), indent=1))
    print('COMPLETE', out, 'states', n, 'fails', len(fails), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ckpt', required=True); p.add_argument('--out', required=True)
    p.add_argument('--split', choices=list(SPLITS), required=True); p.add_argument('--snaps', type=int, nargs='+', default=[10, 16])
    p.add_argument('--limit', type=int, default=0); p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1)
    main(p.parse_args())
