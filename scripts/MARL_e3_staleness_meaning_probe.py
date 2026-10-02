#!/usr/bin/env python3
"""STALENESS-MEANING probe (01/10/2026 21:4x EDT; PROTOCOL_E3_COMPAT_MAP_20261001.md Part A, EXPLORATORY).
Does the age of a copy carry information about its sender's CURRENT state, and does that change with capacity?
The zero-byte student Z acts on its LOCAL view only, so the traffic is the same in every cell of an episode and only the
channel differs.  Cells: order {agefirst, prefix (cached-queue congestion ranking)} x capacity {iid, cap4, low, const1,
const2}; relay v2 merge ('age').  Per receiver-step and merged-view entry: sender, age (decision steps), the copy's waiting
and vehicle sums, and the sender's TRUE current sums (env._summary, read outside the no-oracle guard: DIAGNOSTIC ORACLE,
recorded only).  SELF-CHECK: the episode queue sum is identical in all cells (the channel cannot reach the world); the
evaluators' mirror and access-invariant checks.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from dataclasses import replace
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_zero_loss_truncation import make
import scripts.MARL_e3_continuation_labels as CLAB
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery
from scripts.MARL_e3_negflip_probe import ZPol

SOURCES = ['scripts/MARL_e3_staleness_meaning_probe.py', 'scripts/MARL_e3_negflip_probe.py', 'models/marl_relay_v2.py',
           'models/marl_delivery_music.py', 'scripts/MARL_e3_zero_loss_truncation.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py']
ORDERS = ('agefirst', 'prefix'); CAPS = ('iid', 'cap4', 'low', 'const1', 'const2')
COLS = ('ep', 't', 'recv', 'sender', 'age', 'w_copy', 'v_copy', 'w_now', 'v_now')


def local_only(v):
    return replace(v, inbox=(), cache=(), never_heard=tuple(sorted(int(j) for j in v.neighbours)))


def run(sc, seed, load, ckz, zpol, order, cap, ep):
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    env, _ = make(sc, seed, load, ckz, 'low' if cap == 'low' else 'iid')
    if cap.startswith('const'):
        env._trace = np.full_like(np.asarray(env._trace), int(cap[5:]))
    mus = MusicDelivery(order); mus.mode = 'cap4' if cap == 'cap4' else 'prefix'
    m = env.n_agents; prev = None; q = 0.0; rows = []; never = []; iv = float(env.action_interval)
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            az = zpol.act_views([local_only(mv[i]) for i in range(m)])
        truth = [env._summary(j) for j in range(m)]                                   # DIAGNOSTIC oracle, recorded only
        for i in range(m):
            for e in mv[i].inbox:
                j = int(e.sender); p = e.payload
                rows.append((ep, t, i, j, int(round(float(e.age) / iv)), sum(p.waiting), sum(p.vehicles),
                             sum(truth[j].waiting), sum(truth[j].vehicles)))
            never.append(len(mv[i].neighbours) - len(mv[i].inbox))
        with no_oracle_access(env):
            _, _, rec = env.step({i: int(az[i]) for i in range(m)})
        q += float(rec['queue'])
    return q, rows, float(np.mean(never))


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    ckz = torch.load(Path(a.z), weights_only=False); sc = Scenarios(out)
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    _, zp0 = make(sc, a.traffic_seeds[0], a.headways[0], ckz, 'iid'); zpol = ZPol(ckz, zp0.adapter.topos, zp0.adapter.interval)
    data = {(o, c): [] for o in ORDERS for c in CAPS}; nev = {(o, c): [] for o in ORDERS for c in CAPS}; eps = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = len(eps); qs = {}
            for o in ORDERS:
                for c in CAPS:
                    q, rows, nv = run(sc, seed, load, ckz, zpol, o, c, ep); qs[(o, c)] = q; data[(o, c)] += rows; nev[(o, c)].append(nv)
            if max(qs.values()) - min(qs.values()) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: seed{seed}_load{load:g} queue sums differ across cells: {sorted(set(qs.values()))}')
            eps.append(dict(episode=f'seed{seed}_load{load:g}', seed=seed, load=load, queue_sum=next(iter(qs.values()))))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done ({len(eps)} episodes)', flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    for (o, c), rows in data.items():
        arr = np.array(rows, np.int64)
        np.savez_compressed(out / f'{o}_{c}.npz', **{k: arr[:, n] for n, k in enumerate(COLS)}, never_mean=np.array(nev[(o, c)]))
    (out / 'episodes.json').write_text(json.dumps(eps))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), cells=[f'{o}_{c}' for o, c in data],
        rows={f'{o}_{c}': len(r) for (o, c), r in data.items()}, z_sha256=hashlib.sha256(Path(a.z).read_bytes()).hexdigest(),
        source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--z', default='research/marl_budget/e3_delivery_actors_20260929/distill_none_s0/ckpt_best.pt')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 917)))
    p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
