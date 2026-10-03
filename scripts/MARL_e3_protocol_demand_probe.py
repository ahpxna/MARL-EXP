#!/usr/bin/env python3
"""PROTOCOL-CONDITIONED DEMAND PROBE (01/10/2026 11:0x EDT; PROTOCOL_E3_PROTOCOL_CONDITIONED_DEMAND_20261001.md, EXPLORATORY).
DIAGNOSTIC ORACLE: counterfactual views and the teacher RECORD flags; nothing here chooses an executed action.

System: relay6Cage_st_s<s> closed loop, age-first, capacity const K (the relay v6 evaluator's construction: make(..., 'iid')
then a constant trace), relay v2 merge, 3 B adapter.  At every receiver-step, from the same state:
  need   teacher argmax on the EMPTY view (local observation only) not in A_0.25 of the teacher's full fresh logits
  bestK  some CACHE-base subset of size <= K has an acceptable teacher argmax (exhaustive 2^|N|)
  protoT teacher argmax on the receiver's ACTUAL relay-merged view, 3 B encoding, in A_0.25
  protoS the relay student's executed action in A_0.25
SELF-CHECKS: the closed-loop waiting equals the relay v6 evaluator's rows where given (--parity); teacher and student
encodings have the same dimension; with every neighbour fresh the cache and empty bases coincide.
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
from scripts.MARL_e3_theory_probe import net_of

SOURCES = ['scripts/MARL_e3_protocol_demand_probe.py', 'scripts/MARL_e3_theory_probe.py', 'models/marl_relay_v2.py',
           'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py',
           'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py']
EPS = 0.25


def pre_flags(env, i, teacher, raw, mask, K):
    N = sorted(int(j) for j in env.neighbours[i]); n = len(N)
    heard = [tuple(N[b] for b in range(n) if s >> b & 1) for s in range(1 << n)]
    views = [env.counterfactual_view(i, list(h)) for h in heard]
    v0 = views[0]; ve = replace(v0, cache=(), never_heard=tuple(N))
    X = np.stack([raw.encode(v, 'actual') for v in views] + [raw.encode(ve, 'actual'),
                                                            raw.encode(replace(views[-1], cache=()), 'actual')])
    with torch.no_grad():
        L = teacher(torch.as_tensor(X), mask[i:i + 1].expand(X.shape[0], -1)).numpy()
    full = L[(1 << n) - 1]
    if np.abs(L[-1] - full).max() > 1e-5:
        raise AssertionError(f'bases differ with every neighbour fresh at receiver {i}')
    top = full.max(); ok = full[L[:1 << n].argmax(-1)] >= top - EPS - 1e-9
    size = np.array([bin(s).count('1') for s in range(1 << n)])
    need = not (full[int(L[1 << n].argmax())] >= top - EPS - 1e-9)
    best = bool(ok[size <= K].any())
    return need, best, full, top


def run(sc, seed, load, cks, book, K):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], 'iid')
    env._trace = np.full_like(np.asarray(env._trace), int(K))
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    if raw.dim != pol.adapter.dim:
        raise AssertionError('teacher and student encodings differ in dimension')
    teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; recs = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        pre = [pre_flags(env, i, teacher, raw, mask, K) for i in range(m)]                     # DIAGNOSTIC oracle
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                Lr = pol.actor(torch.as_tensor(X), pol.mask).numpy()
                Lt = teacher(torch.as_tensor(X), mask).numpy()                                  # DIAGNOSTIC: teacher on the delivered view
            acts = {i: int(a) for i, a in enumerate(Lr.argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
        for i in range(m):
            need, best, full, top = pre[i]
            recs.append(dict(t=t, recv=i, need=need, best=best, protoT=bool(full[int(Lt[i].argmax())] >= top - EPS - 1e-9),
                             protoS=bool(full[acts[i]] >= top - EPS - 1e-9)))
    return q, recs


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in (('relay', a.relay), ('teacher', a.teacher))}
    ck_sha = {k: hashlib.sha256(Path(p).read_bytes()).hexdigest() for k, p in (('relay', a.relay), ('teacher', a.teacher))}
    sc = Scenarios(out)
    parity = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text()) if r['rule'] == 'prefix'} if a.parity else {}
    rows = []; allrec = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'; q, rr = run(sc, seed, load, cks, book, a.K)
            if ep in parity and abs(parity[ep] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != relay v6 row {parity[ep]}')
            rows.append(dict(episode=ep, queue_sum=q, parity_checked=ep in parity))
            allrec += [dict(seed=seed, load=load, **r) for r in rr]
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
    keys = ['seed', 'load', 't', 'recv', 'need', 'best', 'protoT', 'protoS']
    np.savez_compressed(out / 'flags.npz', **{k: np.array([r[k] for r in allrec]) for k in keys})
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', eps=EPS, K=a.K, args=vars(a),
        parity_episodes=sum(r['parity_checked'] for r in rows), checkpoint_sha256=ck_sha, source_hashes=h0,
        records=len(allrec), seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--K', type=int, required=True)
    p.add_argument('--parity', default=None); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
