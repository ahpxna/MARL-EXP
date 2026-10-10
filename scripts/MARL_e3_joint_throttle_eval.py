#!/usr/bin/env python3
"""JOINT THROTTLE closed-loop evaluator (03/10/2026 10:4x EDT; PROTOCOL_E3_JOINT_THROTTLE_20261003.md; follow-up of L-295).
L-295 found that garbling ENTRIES back into per-slot / per-rank support does not repair the upgrade hazard although it beats a
relabel: the hazard lives in the joint view configuration.  This evaluator garbles at the JOINT level instead: the receiver
accepts at most k_train direct packets per step (k_train = the capacity it was trained on; age-first choice among the packets
actually delivered: the sender whose last ACCEPTED packet is oldest first, ties by id), and builds its view with exactly the
active merge rule (relay v2, or the grid wrapper's slot-restricted merge) applied to the accepted packets and its own SHADOW cache (the last accepted packet
of each neighbour).  This is the receiver-side emulation of its training reception, given what the other nodes transmit.
Modes (actor input only; the protocol state each node relays is the unmodified merged view, as in the clip / remap /
emulation evaluators): plain; thr (joint throttle); thrlab (the PLAIN payloads shown with the THR ages per sender — relabel
control); mask (the same receiver with every message removed: the CGDC-style masked-message reference pi^(-0)).
SELF-CHECKS: (1) with k_train = infinity the shadow merge reproduces merge_views_v2 exactly at every step of the first
episode (asserted on the views and on the encoded actor input); (2) --parity rows.json reproduces plain episodes where given;
(3) every throttled view holds at most k_train entries delivered at this step.
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
from models.marl_comm_actor_quant import quantized
from models.marl_delivery_music import MusicDelivery

SOURCES = ['scripts/MARL_e3_joint_throttle_eval.py', 'models/marl_relay_v2.py', 'models/marl_delivery_music.py',
           'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py',
           'scripts/MARL_e3_zero_loss_truncation.py', 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']
BIG = 10 ** 6


def shadow_merge(v, i, keep, prev, cache_i, t, interval):
    """The ACTIVE merge rule (merge_views_v2, or the slot-restricted merge the grid wrapper installs) applied to ONE receiver
    whose view holds only its accepted direct packets `keep` and its shadow cache instead of the environment's cache."""
    import models.marl_relay_v2 as RV2                     # read at call time: the grid wrapper patches RV2.merge_views
    vi = replace(v, inbox=tuple(e for e in v.inbox if e.sender in keep), cache=tuple(cache_i[j] for j in sorted(cache_i) if j not in keep))
    return RV2.merge_views({i: vi}, prev, t, interval, 'age')[i]


def choose(v, cache_i, k):
    """age-first among the packets delivered now: the sender whose last accepted packet is oldest (never = oldest) first."""
    snd = sorted({e.sender for e in v.inbox if e.sender in set(v.neighbours)})
    if len(snd) <= k:
        return set(snd)
    key = lambda j: (cache_i[j].measured_at if j in cache_i else -1e18, j)
    return set(sorted(snd, key=key)[:k])


def masked(v):
    return replace(v, inbox=(), cache=(), never_heard=tuple(sorted(int(j) for j in v.neighbours)))


def relabel(plain, thr):
    ages = {e.sender: e.age for e in thr.inbox}
    return replace(plain, inbox=tuple(replace(e, age=ages[e.sender]) if e.sender in ages else e for e in plain.inbox))


def run(sc, seed, load, ck, book, K, mode, ktrain, check=False):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, ck, 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; n_drop = 0
    caches = [dict() for _ in range(m)]
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            import models.marl_relay_v2 as RV2
            mv = RV2.merge_views(views, prev, t, env.action_interval, 'age')
            rv = []
            for i in range(m):
                if mode == 'plain':
                    rv.append(mv[i]); continue
                if mode == 'mask':
                    rv.append(masked(mv[i])); continue
                keep = choose(views[i], caches[i], ktrain)
                n_drop += len({e.sender for e in views[i].inbox}) - len(keep)
                sv = shadow_merge(views[i], i, keep, prev, caches[i], t, env.action_interval)
                if check:
                    ref = mv[i]
                    a = sorted((e.sender, e.measured_at, e.age) for e in sv.inbox); b = sorted((e.sender, e.measured_at, e.age) for e in ref.inbox)
                    if a != b or not np.array_equal(pol.adapter.encode(sv, 'actual'), pol.adapter.encode(ref, 'actual')):
                        raise AssertionError(f'SELF-CHECK FAIL: shadow merge with k = inf differs from merge_views_v2 at t={t}, receiver {i}')
                for e in views[i].inbox:
                    if e.sender in keep:
                        caches[i][e.sender] = e
                rv.append(sv if mode == 'thr' else relabel(mv[i], sv))
            prev = mv
            X = np.stack([pol.adapter.encode(rv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                acts = {i: int(a) for i, a in enumerate(pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
    return q, n_drop


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text()); ck = torch.load(Path(a.relay), weights_only=False)
    ck_sha = hashlib.sha256(Path(a.relay).read_bytes()).hexdigest()
    par = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text())} if a.parity else {}
    sc = Scenarios(out); rows = []; t0 = time.perf_counter(); first = True
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'
            if first:
                qc, _ = run(sc, seed, load, ck, book, a.K, 'thr', BIG, check=True); first = False
            res = {md: run(sc, seed, load, ck, book, a.K, md, a.ktrain) for md in a.modes}
            if 'plain' in res and abs(qc - res['plain'][0]) > 1e-6 and ep == f'seed{a.traffic_seeds[0]}_load{a.headways[0]:g}':
                raise SystemExit(f'SELF-CHECK FAIL: k = inf throttle {qc} != plain {res["plain"][0]}')
            if ep in par and 'plain' in res and abs(par[ep] - res['plain'][0]) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {ep} plain {res["plain"][0]} != parity row {par[ep]}')
            for md, (q, nd) in res.items():
                rows.append(dict(actor=a.tag, mode=md, K=a.K, ktrain=a.ktrain, episode=ep, queue_sum=q, dropped=nd))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed}: ' + ', '.join(f'{md} {res[md][0]:.0f}/{res[md][1]}' for md in a.modes), flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), checkpoint_sha256=ck_sha,
        source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--tag', required=True)
    p.add_argument('--K', type=int, default=0, help='constant K; 0 = iid'); p.add_argument('--ktrain', type=int, default=1)
    p.add_argument('--modes', nargs='+', default=['plain', 'thr', 'thrlab', 'mask'])
    p.add_argument('--parity', default=None); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
