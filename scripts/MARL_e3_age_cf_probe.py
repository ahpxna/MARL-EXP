#!/usr/bin/env python3
"""AGE COUNTERFACTUAL PROBE (01/10/2026 12:0x EDT; PROTOCOL_E3_AGE_COUNTERFACTUAL_20261001.md, EXPLORATORY).
DIAGNOSTIC ORACLE: counterfactual views, the teacher and Z RECORD flags; the executed actions are the relay student's on
its actual merged view (the closed loop of MARL_e3_negflip_probe.py, parity with its queue sums required).
Per receiver-step, the relay student's argmax on: the actual merged view (protoS), the view with every entry older than
A steps re-labelled to age A (clip), and the view without those entries (drop); each in A_0.25 of the teacher's full view.
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
from scripts.MARL_e3_negflip_probe import ZPol, pre_flags, EPS, SOURCES as NF_SOURCES

SOURCES = ['scripts/MARL_e3_age_cf_probe.py'] + NF_SOURCES


def cf_views(v, interval, A):
    old = [e for e in v.inbox if float(e.age) / float(interval) > A + 1e-9]
    if not old:
        return v, v, 0
    clip = replace(v, inbox=tuple(replace(e, age=A * float(interval)) if e in old else e for e in v.inbox))
    drop = replace(v, inbox=tuple(e for e in v.inbox if e not in old))
    return clip, drop, len(old)


def run(sc, seed, load, cks, book, K, zpol, A):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; recs = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        pre = [pre_flags(env, i, teacher, raw, mask, zpol) for i in range(m)]                   # DIAGNOSTIC oracle
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            cf = [cf_views(mv[i], env.action_interval, A) for i in range(m)]
            X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)]
                         + [pol.adapter.encode(cf[i][0], 'actual') for i in range(m)] + [pol.adapter.encode(cf[i][1], 'actual') for i in range(m)])
            with torch.no_grad():
                Lr = pol.actor(torch.as_tensor(X), pol.mask.repeat(3, 1)).numpy()
            acts = {i: int(a) for i, a in enumerate(Lr[:m].argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
        for i in range(m):
            need, zok, full, top = pre[i]
            okf = lambda a: bool(full[int(a)] >= top - EPS - 1e-9)
            recs.append(dict(t=t, recv=i, need=need, zok=zok, protoS=okf(acts[i]), clip=okf(Lr[m + i].argmax()),
                             drop=okf(Lr[2 * m + i].argmax()), n_old=cf[i][2]))
    return q, recs


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    paths = (('relay', a.relay), ('teacher', a.teacher), ('z', a.z))
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in paths}
    ck_sha = {k: hashlib.sha256(Path(p).read_bytes()).hexdigest() for k, p in paths}
    sc = Scenarios(out); par = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text())}
    rows = []; allrec = []; t0 = time.perf_counter(); zpol = None
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'
            if zpol is None:
                CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
                _, zp0 = make(sc, seed, load, cks['z'], 'iid'); zpol = ZPol(cks['z'], zp0.adapter.topos, zp0.adapter.interval)
            q, rr = run(sc, seed, load, cks, book, a.K, zpol, a.A)
            if ep not in par or abs(par[ep] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != negflip row {par.get(ep)}')
            rows.append(dict(episode=ep, queue_sum=q)); allrec += [dict(seed=seed, load=load, **r) for r in rr]
            print(f'[{time.perf_counter() - t0:.0f}s] {ep} done (parity ok)', flush=True)
    keys = ['seed', 'load', 't', 'recv', 'need', 'zok', 'protoS', 'clip', 'drop', 'n_old']
    np.savez_compressed(out / 'flags.npz', **{k: np.array([r[k] for r in allrec]) for k in keys})
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', eps=EPS, K=a.K, A=a.A, args=vars(a),
        checkpoint_sha256=ck_sha, source_hashes=h0, records=len(allrec), seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--z', required=True)
    p.add_argument('--parity', required=True); p.add_argument('--K', type=int, required=True); p.add_argument('--A', type=float, default=2.0)
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
