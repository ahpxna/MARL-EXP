#!/usr/bin/env python3
"""SILENCE-FALLBACK GATE closed-loop evaluator (01/10/2026 16:0x EDT; EXPLORATORY development look, then a pre-registered test).

relay6Cage_st_s<s> closed loop under age-first, capacity const K (K = 0: iid), relay v2 merge, 3 B codebook (the code path of
MARL_e3_ageclip_eval.py).  Every receiver carries BOTH its relay student and its zero-byte student Z (distill_none_s<s>, 0
bytes).  At each step, from its OWN merged view only (no oracle):
  b3 = sum_j (a_j - 3)+ over the entries' ages (decision steps), nev = audible senders with no entry;
  if b3 > --bmax or nev >= --nmax : act with Z on the local-only view (compiled silence)
  else                            : act with the relay student on the view with ages clipped at --A (--A -1: no clip).
The protocol state (what is relayed next step) is the unmodified merged view in every case.
SELF-CHECKS: --parity-z rows: with a gate that always falls back (--bmax -1) the closed loop must reproduce Z's rows;
--parity rows: reproduced where given (e.g. --bmax 1e9 --nmax 1e9 --A -1 must reproduce the plain relay rows).
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
from scripts.MARL_e3_ageclip_eval import clipped
from scripts.MARL_e3_negflip_probe import ZPol

SOURCES = ['scripts/MARL_e3_gate_eval.py', 'scripts/MARL_e3_ageclip_eval.py', 'scripts/MARL_e3_negflip_probe.py', 'models/marl_relay_v2.py',
           'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py',
           'scripts/MARL_e3_zero_loss_truncation.py', 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']


def local_only(v, nbrs):
    return replace(v, inbox=(), cache=(), never_heard=tuple(sorted(int(j) for j in nbrs)))


def run(sc, seed, load, ck, ckz, book, K, A, bmax, nmax):
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    _, zp0 = make(sc, seed, load, ckz, 'iid'); zpol = ZPol(ckz, zp0.adapter.topos, zp0.adapter.interval)
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, ck, 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; nz = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            gate = []
            for i in range(m):
                ages = [float(e.age) / float(env.action_interval) for e in mv[i].inbox]
                b3 = sum(max(a - 3.0, 0.0) for a in ages); nev = len(mv[i].neighbours) - len(ages)
                gate.append(b3 > bmax or nev >= nmax)
            X = np.stack([pol.adapter.encode(clipped(mv[i], env.action_interval, A)[0], 'actual') for i in range(m)])
            with torch.no_grad():
                ar = pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1)
            az = zpol.act_views([local_only(mv[i], mv[i].neighbours) for i in range(m)])
            acts = {i: int(az[i] if gate[i] else ar[i]) for i in range(m)}; nz += sum(gate)
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
    return q, nz


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    ck = torch.load(Path(a.relay), weights_only=False); ckz = torch.load(Path(a.z), weights_only=False)
    par = {}
    for f in (a.parity, a.parity_z):
        if f:
            par.update({r['episode']: r['queue_sum'] for r in json.loads(Path(f).read_text())})
    sc = Scenarios(out); rows = []; t0 = time.perf_counter(); rule = f'gate_b{a.bmax:g}_n{a.nmax:g}_A{a.A:g}'
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'; q, nz = run(sc, seed, load, ck, ckz, book, a.K, a.A, a.bmax, a.nmax)
            if ep in par and abs(par[ep] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != parity row {par[ep]}')
            rows.append(dict(actor=a.tag, rule=rule, episode=ep, queue_sum=q, fallback_decisions=nz, parity_checked=ep in par))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', K=a.K, A=a.A, bmax=a.bmax, nmax=a.nmax, rule=rule,
        args=vars(a), parity_episodes=sum(r['parity_checked'] for r in rows), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--z', required=True); p.add_argument('--tag', required=True)
    p.add_argument('--K', type=int, required=True); p.add_argument('--A', type=float, default=-1.0)
    p.add_argument('--bmax', type=float, required=True); p.add_argument('--nmax', type=float, required=True)
    p.add_argument('--parity', default=None); p.add_argument('--parity-z', default=None)
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', required=True); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
