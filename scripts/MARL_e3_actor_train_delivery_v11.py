#!/usr/bin/env python3
"""v11 (30/09 12:5x; ledger L-164): v10 with the CAPACITY process applied in relay episodes.  v10's episode_relay ignored
--capacity (it never set env._trace); runs with the default iid were unaffected.  Identical to v10 for --capacity iid.
Also --order {prefix (default), agefirst}: agefirst replaces the broadcast order by models/marl_delivery_agefirst.py (oldest
last-broadcast first; scheduler information only).
v10 docstring follows.
v10 (30/09 11:1x; ledger L-162): v9 plus --relay {none, age, fresh}: the actor's inputs are RELAY-MERGED views
(models/marl_relay.py): each 25 B packet of the unchanged HETERO_v0 channel carries 3 B summaries of its sender and of every agent
the sender knew (use with --quant 4); receivers merge the relays of the packets they decoded.  The access audit runs on the env's
own views before the merge.  --relay none is exactly v9.
v9 docstring follows.
v9 (29/09 23:4x; ledger L-136): v8 plus --audit-every N: the per-step access audit keeps checks 1-6 at every step and
walks the view leaves (check 7) only at decision steps t % N == 0 (envs/external/cityflow_audit_sampled.py), TRAINING only,
approved by the user 23:4x.  --audit-every 1 is exactly v8.  Evaluation never uses this.
v8 docstring follows.
v8 (29/09 23:0x; ledger L-133): trainer v7 (imported unchanged) plus --quant L --codebook JSON.  The actor is TRAINED on
sender-side compressed payloads (models/marl_comm_actor_quant.py; codebook fitted on TRAIN traffic by
scripts/MARL_e3_payload_codebook.py), so that the byte-budget variant of PROTOCOL_E3_BYTEBUDGET_20260929 is trained
end to end, not only compressed at evaluation.  Evaluate with scripts/MARL_e3_delivery_eval_v7.py --quant L (the same
codebook).  Without --quant this is exactly v7.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_e3_actor_train_delivery_v7 as V7
from models.marl_comm_actor_quant import quantized
import envs.external.cityflow_audit_sampled as AUD
import numpy as np
from models.marl_relay import merge_views
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC

RELAY = {'mode': 'none'}


def episode_relay(sc, seed, load, policy, adapter=None, record=False, variant='actual', rng=None, p_mix=0.0, mix_rng=None):
    """V7.episode with the actor's inputs built from relay-merged views."""
    if p_mix:
        raise ValueError('p_mix is not supported with --delivery')
    env, topo, down, onward = sc.env(seed, load); m = env.n_agents
    if V7.DELIVERY['capacity'] != 'iid':
        from scripts.MARL_hetero_panel_collect import capacity_trace
        env._trace = capacity_trace(V7.DELIVERY['capacity'], N_DEC, m, 5000 + 10 * seed + int(load))
    if adapter is not None:
        adapter.reset()
    traj = dict(X=[], S=[], A=[], LP=[], R=[]); queues = []; prev = None
    for t in range(N_DEC):
        with no_oracle_access(env):
            V7.deliver(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            if policy == 'mp2':
                acts = {i: V7.mp2_action(v, topo[i], down, onward) for i, v in views.items()}
            else:
                mv = merge_views(views, prev, t, RELAY['mode']); prev = mv
                X = np.stack([adapter.encode(mv[i], variant, rng) for i in range(m)])
                a, lp = policy(X)
                acts = {i: int(a[i]) for i in range(m)}
                if record:
                    traj['X'].append(X); traj['S'].append(adapter.global_state(views, t)); traj['A'].append(a); traj['LP'].append(lp)
                adapter.remember(views)
            _, _, rec = env.step(acts)
        queues.append(float(rec['queue']))
        if record:
            traj['R'].append(-rec['queue'] / 100.0)
    return queues, traj, env.episode_summary()

R = V7.R


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', required=True); p.add_argument('--seed', type=int, default=0)
    p.add_argument('--iters', type=int, default=200); p.add_argument('--eps-per-iter', type=int, default=8)
    p.add_argument('--epochs', type=int, default=4); p.add_argument('--minibatch', type=int, default=64)
    p.add_argument('--lr', type=float, default=3e-4); p.add_argument('--ent', type=float, default=0.01)
    p.add_argument('--hidden', type=int, default=128); p.add_argument('--eval-every', type=int, default=10)
    p.add_argument('--threads', type=int, default=2); p.add_argument('--p-mix', type=float, default=0.0)
    p.add_argument('--init-from'); p.add_argument('--stop-after', type=int, default=0)
    p.add_argument('--capacity', choices=['iid', 'fixed', 'high', 'low', 'bursty'], default='iid'); p.add_argument('--mask-nonneighbors', action='store_true'); p.add_argument('--set-actor', action='store_true'); p.add_argument('--arch', choices=['flat', 'set', 'sharedconcat', 'attn'], default='flat'); p.add_argument('--adapter', choices=['default', 'noise', 'freshonly'], default='default')
    p.add_argument('--delivery', choices=['prefix', 'full', 'none', 'random', 'nbr', 'rxq', 'rxold', 'mixrand0.25', 'mixrand0.5'] + [f'cap{c}' for c in range(1, 9)], required=True)
    p.add_argument('--quant', type=int, default=0); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--audit-every', type=int, default=1)
    p.add_argument('--relay', choices=['none', 'age', 'fresh'], default='none')
    p.add_argument('--order', choices=['prefix', 'agefirst'], default='prefix')
    a = p.parse_args()
    V7.DELIVERY['mode'] = a.delivery; V7.DELIVERY['capacity'] = a.capacity
    if a.set_actor:
        a.arch = 'set'
    import models.marl_comm_actor_variants as VAR
    from models.marl_comm_actor_set import SetActorNet
    R.ActorNet = {'flat': R.ActorNet, 'set': SetActorNet, 'sharedconcat': VAR.SharedConcatActorNet, 'attn': VAR.AttnActorNet}[a.arch]
    if a.adapter != 'default':
        R.CommAdapter = {'noise': VAR.NoiseCommAdapter, 'freshonly': VAR.FreshOnlyCommAdapter}[a.adapter]
    if a.mask_nonneighbors:
        from models.marl_comm_actor_masked import MaskedCommAdapter
        R.CommAdapter = MaskedCommAdapter
    if a.quant:
        R.CommAdapter = quantized(R.CommAdapter, json.loads((ROOT / a.codebook).read_text()), a.quant)
    AUD.install(a.audit_every)
    RELAY['mode'] = a.relay
    if a.order == 'agefirst':
        from models.marl_delivery_agefirst import deliver_agefirst
        V7.deliver = deliver_agefirst
        R.SOURCES = R.SOURCES + ['models/marl_delivery_agefirst.py']
    R.episode = V7.episode if a.relay == 'none' else episode_relay
    R.SOURCES = R.SOURCES + ['scripts/MARL_e3_actor_train_delivery_v11.py', 'scripts/MARL_e3_actor_train_delivery_v10.py', 'models/marl_relay.py', 'scripts/MARL_e3_actor_train_delivery_v9.py', 'envs/external/cityflow_audit_sampled.py', 'scripts/MARL_e3_actor_train_delivery_v8.py', 'models/marl_comm_actor_quant.py', a.codebook,
                             'scripts/MARL_e3_actor_train_delivery_v7.py', 'models/marl_comm_actor_variants.py', 'scripts/MARL_e3_actor_train_delivery_v6.py',
                             'scripts/MARL_hetero_panel_collect.py', 'scripts/MARL_e3_actor_train_delivery_v5.py', 'models/marl_comm_actor_set.py',
                             'scripts/MARL_e3_actor_train_delivery_v4.py', 'models/marl_comm_actor_masked.py', 'models/marl_hetero_selector.py', 'scripts/MARL_hetero_target_diag.py']
    R.main(a)
