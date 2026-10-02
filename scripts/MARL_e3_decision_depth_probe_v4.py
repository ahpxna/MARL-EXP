#!/usr/bin/env python3
"""DECISION-DEPTH PROBE v4 (01/10/2026 10:5x EDT; PROTOCOL_E3_EXACT_DEMAND_1B_20261001.md).  DIAGNOSTIC: the simulator's
counterfactual views (an oracle) RECORD what the TEACHER would do; no oracle quantity chooses an executed action.

Same executed system, teacher and acceptable set as V-D v1 (scripts/MARL_e3_decision_depth_probe.py): relay6Cage closed loop,
age-first, low capacity, A_0.25 of the teacher's full-view logits (a teacher-defined proxy).  New at every receiver-step:
  * EXHAUSTIVE subsets S of the receiver's neighbours (2^|N|, no size cap), on two bases:
      CACHE: counterfactual view with S fresh, stale cache kept (the V-D v1 / N_s base);
      EMPTY: the same with the cache removed (local observation plus S only: the zero-byte student's information plus S);
  * d_min[B]  = least |S| with an acceptable teacher argmax (exact, 0..|N|);
    d_prefix[B] = least k with the first k senders of the executed stream (exact);
  * ok bits of every subset (packed), the teacher's full-view top-2 margin.
SELF-CHECKS: the executed waiting equals the satrot row (parity); with S = N both bases give identical logits; the full view
equals the v1 construction.
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

SOURCES = ['scripts/MARL_e3_decision_depth_probe_v4.py', 'scripts/MARL_e3_theory_probe.py', 'models/marl_relay_v2.py',
           'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py',
           'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py']
EPS = 0.25


def per_receiver(env, i, teacher, raw, mask, stream):
    N = sorted(int(j) for j in env.neighbours[i]); n = len(N); subs = range(1 << n)
    heard = [tuple(N[b] for b in range(n) if s >> b & 1) for s in subs]
    views = []
    for h in heard:
        v = env.counterfactual_view(i, list(h))
        views.append(v)                                                     # CACHE base
        views.append(replace(v, cache=(), never_heard=tuple(j for j in N if j not in h)))   # EMPTY base
    X = np.stack([raw.encode(v, 'actual') for v in views])
    with torch.no_grad():
        L = teacher(torch.as_tensor(X), mask[i:i + 1].expand(X.shape[0], -1)).numpy()
    Lc, Le = L[0::2], L[1::2]
    full = Lc[(1 << n) - 1]
    if np.abs(Le[(1 << n) - 1] - full).max() > 1e-5:
        raise AssertionError(f'bases differ with every neighbour fresh at receiver {i}')
    top = full.max(); srt = np.sort(full); margin = float(srt[-1] - srt[-2])
    okc = full[Lc.argmax(-1)] >= top - EPS - 1e-9; oke = full[Le.argmax(-1)] >= top - EPS - 1e-9
    size = np.array([bin(s).count('1') for s in subs])
    seq = [j for j in stream if j in N]; pre = [0]
    for j in seq:
        pre.append(pre[-1] | (1 << N.index(j)))
    out = {}
    for name, ok in (('cache', okc), ('empty', oke)):
        out[f'dmin_{name}'] = int(size[ok].min())
        out[f'dpre_{name}'] = next(k for k in range(n + 1) if ok[pre[k]])
        out[f'bits_{name}'] = np.packbits(ok.astype(np.uint8))
    out['margin'] = margin; out['nN'] = n
    return out


def run(sc, seed, load, cks, book):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], 'low')
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; recs = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        stream = tuple(mus.last_order)
        per = [per_receiver(env, i, teacher, raw, mask, stream) for i in range(m)]          # DIAGNOSTIC oracle
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                Lr = pol.actor(torch.as_tensor(X), pol.mask).numpy()
            _, _, rec = env.step({i: int(a) for i, a in enumerate(Lr.argmax(-1))})
        q += float(rec['queue'])
        for i in range(m):
            recs.append(dict(t=t, recv=i, **per[i]))
    return q, recs


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in (('relay', a.relay), ('teacher', a.teacher))}
    ck_sha = {k: hashlib.sha256(Path(p).read_bytes()).hexdigest() for k, p in (('relay', a.relay), ('teacher', a.teacher))}
    sc = Scenarios(out)
    parity = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text()) if r['rule'] == 'prefix'}
    rows = []; allrec = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'; q, rr = run(sc, seed, load, cks, book)
            if ep in parity and abs(parity[ep] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != satrot row {parity[ep]}')
            rows.append(dict(episode=ep, queue_sum=q, parity_checked=ep in parity))
            allrec += [dict(seed=seed, load=load, **r) for r in rr]
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
    keys = ['seed', 'load', 't', 'recv', 'nN', 'margin', 'dmin_cache', 'dpre_cache', 'dmin_empty', 'dpre_empty']
    arr = {k: np.array([r[k] for r in allrec]) for k in keys}
    arr['bits_cache'] = np.stack([r['bits_cache'] for r in allrec]); arr['bits_empty'] = np.stack([r['bits_empty'] for r in allrec])
    np.savez_compressed(out / 'depth_v4.npz', **arr); (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', eps=EPS, args=vars(a),
        parity_episodes=sum(r['parity_checked'] for r in rows), checkpoint_sha256=ck_sha, source_hashes=h0, records=len(allrec),
        seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--parity', required=True)
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 917))); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
