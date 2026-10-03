#!/usr/bin/env python3
"""SWITCHING-CHANNEL closed-loop evaluator (02/10/2026 15:1x EDT; PROTOCOL_E3_SWITCH_20261002.md): MARL_e3_ageclip_eval.py
with --schedule replacing --K: the capacity trace of the episode (26 decision steps × receivers) is the env's own iid trace in
iid phases and constant 1 in K1 phases — k1 (all K1), iid (all iid), k1_iid (K1 for steps 0–12, iid after), iid_k1 (the
reverse), alt4 (K1 / iid alternating every 4 steps, starting with K1).  Everything else is the age-clip evaluator with --A −1.
Original docstring follows.
AGE-CLIP closed-loop evaluator (01/10/2026 12:1x EDT; PROTOCOL_E3_AGECLIP_PROSPECTIVE_20261001.md).

relay6Cage_st_s<s> closed loop under age-first, capacity const K (K = 0: the iid process of make(..., 'iid')), relay v2 merge,
3 B codebook (the code path of MARL_e3_negflip_probe.py / MARL_e3_protocol_demand_probe.py).  With --A a >= 0 the ACTOR
reads the merged view with every entry older than a decision steps re-labelled to age a (content unchanged); the protocol
state (what is relayed next step) is the unmodified merged view.  --A -1 = no clipping (the plain relay system).
Deployable: the rule uses only the receiver's own merged view (ages it already holds); no oracle call.
SELF-CHECK: --parity rows.json (episode -> queue_sum) must be reproduced exactly where given.
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
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery

SOURCES = ['scripts/MARL_e3_switch_eval.py', 'scripts/MARL_e3_ageclip_eval.py', 'models/marl_relay_v2.py', 'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py',
           'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py',
           'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']


def clipped(v, interval, A):
    """(view the actor reads, number of entries re-labelled)."""
    if A < 0:
        return v, 0
    old = [float(e.age) / float(interval) > A + 1e-9 for e in v.inbox]
    if not any(old):
        return v, 0
    return replace(v, inbox=tuple(replace(e, age=A * float(interval)) if o else e for e, o in zip(v.inbox, old))), sum(old)


def run(sc, seed, load, ck, book, K, A):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, ck, 'iid')
    tr = np.array(env._trace, copy=True); T = tr.shape[0]
    k1 = {'k1': [True] * T, 'iid': [False] * T, 'k1_iid': [t < T // 2 for t in range(T)],
          'iid_k1': [t >= T // 2 for t in range(T)], 'alt4': [(t // 4) % 2 == 0 for t in range(T)]}[K]
    for t in range(T):
        if k1[t]:
            tr[t] = 1
    env._trace = tr
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; n_clip = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            cv = [clipped(mv[i], env.action_interval, A) for i in range(m)]
            rv = [c[0] for c in cv]; n_clip += sum(c[1] for c in cv)
            X = np.stack([pol.adapter.encode(rv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                acts = {i: int(a) for i, a in enumerate(pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
    return q, n_clip


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text()); ck = torch.load(Path(a.relay), weights_only=False)
    ck_sha = hashlib.sha256(Path(a.relay).read_bytes()).hexdigest()
    par = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text())} if a.parity else {}
    sc = Scenarios(out); rows = []; t0 = time.perf_counter(); rule = 'prefix' if a.A < 0 else f'clip{a.A:g}'
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'; q, nc = run(sc, seed, load, ck, book, a.schedule, a.A)
            if ep in par and abs(par[ep] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != parity row {par[ep]}')
            rows.append(dict(actor=a.tag, rule=rule, episode=ep, queue_sum=q, clipped_views=nc, parity_checked=ep in par))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', schedule=a.schedule, A=a.A, rule=rule, args=vars(a),
        parity_episodes=sum(r['parity_checked'] for r in rows), checkpoint_sha256=ck_sha, source_hashes=h0,
        seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--tag', required=True)
    p.add_argument('--schedule', choices=['k1', 'iid', 'k1_iid', 'iid_k1', 'alt4'], required=True); p.add_argument('--A', type=float, required=True, help='clip age (steps); -1 = off')
    p.add_argument('--parity', default=None); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', required=True); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
