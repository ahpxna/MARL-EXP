#!/usr/bin/env python3
"""Is the full-episode effect of a single edit carried by the PERSISTENCE of its off-schedule deliveries in the
receivers' caches?  (novelty-direction test, 29/09; diagnostic; oracle labels only; no learner, no selector)

MARL_e3_label_horizon_probe.py found that one edit followed by the prefix changes the full-episode waiting by much more
than its 3-step label, in both directions, and that the size depends on the actor (BC >> scratch > mix).  Hypothesis:
the edit's delivery (receiver r decodes sender j although the prefix P_r at t does not contain j) stays in r's cache for
the rest of the episode; the actor, trained under the prefix schedule, keeps acting on an off-schedule cache.
Counterfactual deployment rule tested here, REVERT-AFTER-L: at the start of step t + L, every such (r, j) entry that has
not been refreshed since t is restored, in the receiver cache AND the scheduler mirror, to its value before the edit
(None = never heard).  A receiver can apply it with public information (the committed order and K give P_r).
Same states and the same candidate subset as the label horizon probe (asserted against its rows); for every L in --ttls
the queues of steps t..N_DEC-1.  Self-checks (abort): replayed state at t equals the stored one; the prefix row equals
the label horizon probe's prefix row; the steps before t + L equal the label horizon probe's queues for the same
candidate; the mirror equals the caches after every revert (verify_mirror runs at every step).
Evidence class: oracle diagnostic of a deployment rule, not a method result.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.MARL_hetero_target_diag import grant, scenario
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_continuation_labels import Policy, step_with
from scripts.MARL_e3_selector_train import load
from scripts.MARL_e3_hindsight_probe import OneScenario, base_until

SOURCES = ['scripts/MARL_e3_edit_ttl_probe.py', 'scripts/MARL_e3_label_horizon_probe.py', 'scripts/MARL_e3_hindsight_probe.py',
           'scripts/MARL_e3_continuation_labels.py', 'scripts/MARL_hetero_target_diag.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py', 'envs/external/cityflow_hetero_mirror.py', 'models/marl_receiver_mirror.py']


def replay_revert(sc, seed, load_, pol, t, S, L):
    """Prefix for steps < t, profile S at t, prefix later; off-schedule (r, j) entries of step t reverted at t + L."""
    env, _, _, _ = sc.env(seed, load_)
    for _ in range(t):
        with no_oracle_access(env):
            order, K = grant(env)
        step_with(env, pol, prefix_sets(order, K))
    with no_oracle_access(env):
        order, K = grant(env)
    P = prefix_sets(order, K); added = [(r, j) for r in range(env.n_agents) for j in S[r] if j not in P[r]]
    before = {(r, j): (env._cache[r].get(j), env.mirror.cache[r].get(j)) for r, j in added}
    q = [step_with(env, pol, S)[0]]; reverted = 0
    for s in range(t + 1, N_DEC):
        if s == t + L:
            for (r, j), (c_old, m_old) in before.items():
                e = env._cache[r].get(j)
                if e is not None and e[2] == t:                      # not refreshed since the edit
                    for store, old in ((env._cache[r], c_old), (env.mirror.cache[r], m_old)):
                        if old is None:
                            store.pop(j, None)
                        else:
                            store[j] = old
                    reverted += 1
            env.verify_mirror()
        with no_oracle_access(env):
            o, k = grant(env)
        q.append(step_with(env, pol, prefix_sets(o, k))[0])
    return q, len(added), reverted


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    D = Path(a.actor_dir); S, ck = load([D / 'labels_dev']); ckp = torch.load(ck.pop(), weights_only=False)
    ref = {(r['episode'], r['t']): r for r in json.loads((Path(a.horizon_dir) / 'rows.json').read_text())}
    if json.loads((Path(a.horizon_dir) / 'manifest.json').read_text()).get('status') != 'COMPLETE':
        raise SystemExit('refusing: the label horizon probe directory is not COMPLETE')
    by_ep = defaultdict(list)
    for st in S:
        by_ep[(st['traffic_seed'], st['headway'])].append(st)
    eps = sorted(by_ep)[a.shard::a.nshards]; rows = []; t0 = time.perf_counter()
    for seed, load_ in eps:
        orig = scenario(out / 'orig', seed, load_); so = OneScenario(orig)
        env0, topo, _, _ = so.env(seed, load_); pol = Policy(ckp, topo, env0.action_interval)
        for st in sorted(by_ep[(seed, load_)], key=lambda s: s['t']):
            t = st['t']; R0 = ref[(f'seed{seed}_load{load_:g}', t)]
            ok = [i for i, c in enumerate(st['cands']) if i == 0 or c['bytes'] <= st['b0'] + 74]
            best = max(ok, key=lambda i: st['cands'][i]['cont'])
            rng = np.random.default_rng([seed, int(load_), t, 7])
            others = [i for i in ok if i not in (0, best)]; pick = [0, best] + sorted(rng.choice(others, size=min(a.cands, len(others)), replace=False).tolist())
            if pick != R0['picked']:
                raise SystemExit(f'SELF-CHECK FAIL: candidate subset differs from the label horizon probe at {seed}/{load_}/t{t}')
            _, o_ref, k_ref, z_ref = base_until(so, seed, load_, pol, t)
            if o_ref != st['order'] or k_ref != st['K'] or max(abs(x - y) for x, y in zip(z_ref, st['z'])) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: replay does not reproduce the stored state {seed}/{load_}/t{t}')
            res = {}
            for L in a.ttls:
                Q, nadd, nrev = [], [], []
                for ci, i in enumerate(pick):
                    q, na, nr = replay_revert(so, seed, load_, pol, t, [set(s) for s in st['cands'][i]['sets']], L)
                    base = R0['queues'][ci]
                    if q[:L] != base[:L] or (ci == 0 and q != base):
                        raise SystemExit(f'SELF-CHECK FAIL: {seed}/{load_}/t{t}/c{i}/L{L}: steps before the revert differ from the label horizon probe')
                    Q.append(q); nadd.append(na); nrev.append(nr)
                res[str(L)] = dict(queues=Q, added=nadd, reverted=nrev)
            rows.append(dict(episode=f'seed{seed}_load{load_:g}', t=t, picked=pick, stored_best=best, no_revert_queues=R0['queues'],
                             prefix_episode_queue_sum=R0['prefix_episode_queue_sum'], ttl=res))
            Qn = np.array(R0['queues']); gn = -(Qn.sum(1) - Qn[0].sum())
            msg = ' | '.join(f"L{L}: best {-(np.sum(res[str(L)]['queues'][1]) - Qn[0].sum()):+.0f} random {np.mean([-(np.sum(q) - Qn[0].sum()) for q in res[str(L)]['queues'][2:]]):+.1f}" for L in a.ttls)
            print(f'[{time.perf_counter() - t0:.0f}s] seed{seed}_load{load_:g} t{t}: no revert best {gn[1]:+.0f} random {gn[2:].mean():+.1f} | {msg}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), states=len(rows), N_DEC=N_DEC,
                                                       source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor-dir', required=True); p.add_argument('--horizon-dir', required=True, help='the COMPLETE label horizon probe output of the same actor')
    p.add_argument('--ttls', type=int, nargs='+', default=[3]); p.add_argument('--cands', type=int, default=15)
    p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1); p.add_argument('--out', required=True)
    main(p.parse_args())
