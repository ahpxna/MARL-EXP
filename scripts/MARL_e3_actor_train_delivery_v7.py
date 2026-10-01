#!/usr/bin/env python3
"""v7 (29/09 22:0x): v6 (unchanged; in use) plus the root-cause variants of models/marl_comm_actor_variants.py:
  --adapter {default, noise, freshonly}   rebinding the resume trainer's CommAdapter (input variant)
  --arch {flat, set, sharedconcat, attn}   rebinding its ActorNet (network variant); --set-actor is --arch set
Both are recorded in config.json.
v6 docstring follows.
v6 (29/09 19:5x): v5 (unchanged; in use) plus --capacity {iid, fixed, high, low, bursty}: the receiver capacity
process of scripts/MARL_hetero_panel_collect.capacity_trace (seed 5000 + 10 seed + headway, as every closed-loop script),
set on the env of every training AND select episode; iid keeps the env's own trace (identity).
Also (20:0x) delivery rxq: the SAME prefix stream and capacities; receiver i itself chooses which K_i streamed packets to
decode, from its OWN view: physical neighbours first, ordered by the waiting in ITS cached copy of them (never-heard
first), then the others in the committed order (MASTER: put the choice where the information is).  Receiver-side
selection needs no per-receiver description, so its honest byte cost is the prefix stream's; the env still charges the
patched description, and reports must use the stream bytes.
Also (20:1x) rxold: as rxq but the receiver decodes its neighbours OLDEST cached copy first, then the others oldest first
(ADAPTIVE: a refresh-tracking rule that bounds every pair's staleness); and mixrand<b>: at each step, with probability
b (seeded by seed, headway, step) the committed order is a uniformly random permutation, otherwise the cached-queue
order (paper A: a b-mixture repair of the prefix surrogate).
v5 docstring follows.
v5 (29/09 19:1x): v4 (unchanged; in use) plus --set-actor: the actor network is
models.marl_comm_actor_set.SetActorNet (shared per-sender encoder, heard-masked mean pooling) instead of the flat
ActorNet (the resume trainer's ActorNet name is rebound; recorded in config.json).
v4 docstring follows.
v4 (29/09 18:4x): v3 (unchanged; in use) plus --mask-nonneighbors: the actor input is built by
models.marl_comm_actor_masked.MaskedCommAdapter (every non-physical-neighbour sender block zeroed), for training AND the
select evaluation (the resume trainer's CommAdapter name is rebound).  Recorded in config.json.
v3 docstring follows.
v3 (29/09 18:2x): v2 (unchanged; in use) plus
  nbr     the SAME prefix stream (order[:L0]) and the same capacities K_i, but receiver i decodes, among the streamed
          packets, its PHYSICAL neighbours first (in the committed order), then the others in the committed order, up
          to K_i: a topology-aware decode rule inside the receiver capacity.  Bytes by the shared profile_cost
          (patched: 3 B per replacement, or explicit).
v2 docstring follows.
v2 (29/09 18:1x): v1 (MARL_e3_actor_train_delivery.py, unchanged; in use by a running job) plus
  cap<c>  the prefix stream capped at its first c packets (the blind cap_<c> rule of MARL_e3_truncation_closed_loop_v2):
          the BUDGET-MATCHED actor, the strongest same-byte baseline for decision-aware truncation.
v1 docstring follows.
E3 actor trained under a DIFFERENT delivery rule (29/09; ledger L-90 follow-up): the information ceiling and the
side-channel-free actor.  The training loop, resume, checkpoints and selection are MARL_e3_actor_train_resume.py's,
unchanged; only its episode() is replaced, so every delivery (training AND the select evaluation) uses --delivery:
  full    every receiver decodes all m-1 other senders every step (capacities ignored; 9 packets, 225 B per step):
          the full-information actor, an upper reference for what any budgeted scheduler could make useful;
  none    no deliveries at all (capacities 0): the no-communication actor, the lower reference;
  random  the capacities of the env trace, but the committed base order is a uniformly random permutation every
          step (seeded by seed, headway, step: no training RNG is consumed) instead of the cached-queue order, so
          the per-sender 'fresh' flag carries no congestion information (the L-90 side channel is removed);
  prefix  the original rule (identity check: must reproduce the resume trainer).
Scheduler-side protocol stages are kept (commit, reveal, submit, transmit) and every call is inside no_oracle_access.
Evaluation of the trained actors on the closed-loop panel is a separate script.
"""
from __future__ import annotations
import sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_e3_actor_train_resume as R
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets, stream_length
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_target_diag import grant

DELIVERY = {'mode': 'prefix', 'capacity': 'iid'}


def deliver(env, seed, load, t):
    """Commit, reveal and submit this step's profile under DELIVERY['mode']; returns the submitted sets."""
    m = env.n_agents; mode = DELIVERY['mode']
    if mode.startswith('mixrand'):
        mode = 'random' if np.random.default_rng([int(seed), int(load), int(t), 0xB7]).random() < float(mode[7:]) else 'prefix'
    if mode == 'random':
        perm = tuple(int(j) for j in np.random.default_rng([int(seed), int(load), int(t), 0xD1]).permutation(m))
        env.commit_global_ranking(perm); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        sets = prefix_sets(perm, K)
    else:
        order, K = grant(env)
        if mode == 'prefix':
            sets = prefix_sets(order, K)
        elif mode == 'nbr':
            P = prefix_sets(order, K); L0 = stream_length(order, P); stream = list(order[:L0]); sets = []
            for i in range(m):
                nb = set(env.physical_neighbours[i]); cand = [j for j in stream if j != i]
                pri = [j for j in cand if j in nb] + [j for j in cand if j not in nb]
                sets.append(frozenset(pri[:K[i]]))
        elif mode == 'rxq':
            P = prefix_sets(order, K); L0 = stream_length(order, P); stream = list(order[:L0]); sets = []
            for i in range(m):
                nb = set(env.physical_neighbours[i]); cand = [j for j in stream if j != i]
                def key(j):
                    e = env._cache[i].get(j)
                    return (0, 0.0) if e is None else (1, -float(sum(e[0].waiting)))
                pri = sorted([j for j in cand if j in nb], key=key) + [j for j in cand if j not in nb]
                sets.append(frozenset(pri[:K[i]]))
        elif mode == 'rxold':
            P = prefix_sets(order, K); L0 = stream_length(order, P); stream = list(order[:L0]); sets = []; now = env._now()
            for i in range(m):
                nb = set(env.physical_neighbours[i]); cand = [j for j in stream if j != i]
                def age(j):
                    e = env._cache[i].get(j)
                    return float('inf') if e is None else now - float(e[1])
                pri = sorted([j for j in cand if j in nb], key=lambda j: -age(j)) + sorted([j for j in cand if j not in nb], key=lambda j: -age(j))
                sets.append(frozenset(pri[:K[i]]))
        elif mode.startswith('cap'):
            P = prefix_sets(order, K); head = set(order[:int(mode[3:])])
            sets = [frozenset(j for j in P[i] if j in head) for i in range(m)]; env._k = {i: len(sets[i]) for i in range(m)}
        elif mode == 'full':
            env._k = {i: m - 1 for i in range(m)}; sets = [frozenset(j for j in range(m) if j != i) for i in range(m)]
        elif mode == 'none':
            env._k = {i: 0 for i in range(m)}; sets = [frozenset() for _ in range(m)]
        else:
            raise ValueError(mode)
    env.submit_profile([set(s) for s in sets], R=0 if mode in ('prefix', 'random') or mode.startswith('cap') else None)
    return sets


def episode(sc, seed, load, policy, adapter=None, record=False, variant='actual', rng=None, p_mix=0.0, mix_rng=None):
    """MARL_e3_actor_train_mix.episode with p_mix = 0, the profile replaced by deliver()."""
    if p_mix:
        raise ValueError('p_mix is not supported with --delivery')
    env, topo, down, onward = sc.env(seed, load); m = env.n_agents
    if DELIVERY['capacity'] != 'iid':
        from scripts.MARL_hetero_panel_collect import capacity_trace
        env._trace = capacity_trace(DELIVERY['capacity'], N_DEC, m, 5000 + 10 * seed + int(load))
    if adapter is not None:
        adapter.reset()
    traj = dict(X=[], S=[], A=[], LP=[], R=[]); queues = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            deliver(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            if policy == 'mp2':
                acts = {i: mp2_action(v, topo[i], down, onward) for i, v in views.items()}
            else:
                X = np.stack([adapter.encode(views[i], variant, rng) for i in range(m)])
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


if __name__ == '__main__':
    import argparse
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
    a = p.parse_args()
    DELIVERY['mode'] = a.delivery; DELIVERY['capacity'] = a.capacity
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
    R.episode = episode                                          # R.main's evaluate() and training loop call R.episode
    R.SOURCES = R.SOURCES + ['scripts/MARL_e3_actor_train_delivery_v7.py', 'models/marl_comm_actor_variants.py', 'scripts/MARL_e3_actor_train_delivery_v6.py', 'scripts/MARL_hetero_panel_collect.py', 'scripts/MARL_e3_actor_train_delivery_v5.py', 'models/marl_comm_actor_set.py', 'scripts/MARL_e3_actor_train_delivery_v4.py', 'models/marl_comm_actor_masked.py', 'models/marl_hetero_selector.py', 'scripts/MARL_hetero_target_diag.py']
    R.main(a)
