#!/usr/bin/env python3
"""v3 (01/10/2026 19:5x EDT; PROTOCOL_E3_ORDER_DOSE_20261001.md): v2 with --order {agefirst, prefix} (prefix = the congestion
ranking of models/marl_delivery_music.MusicDelivery) and --capacity {iid, low, high, bursty, const<k>, cap<c>} (cap<c> = the
iid process with the cap<c> delivery mode); --parity-dir optional.  With --order agefirst --capacity const<k> / iid and a
parity dir this is exactly v2.
v2 docstring follows.
v2 (01/10/2026 14:5x EDT; PROTOCOL_E3_G4_CONSTK_ADDENDUM1_20261001.md): v1 plus, per receiver-step, the tail staleness
burdens b2 = sum_j (a_j - 2)+ and b3 = sum_j (a_j - 3)+ over the entries of the merged view (ages in decision steps), for the
exposure-response curve P(flip_Z | burden).  Everything else is v1 (same closed loop, flags and parity checks).
v1 docstring follows.
VIEW-STATISTICS PROBE (01/10/2026 12:2x EDT; PROTOCOL_E3_VIEW_OOD_20261001.md, EXPLORATORY, development panel).
The closed loop of MARL_e3_negflip_probe.py (relay6Cage_st_s<s>, age-first, relay v2 merge, 3 B codebook; K = 0: iid,
the training process) plus, per receiver-step, the COMPOSITION of the merged view the relay student reads:
  n_fresh  entries delivered fresh this step (direct inbox); n_relay  relayed copies; n_ent = n_fresh + n_relay;
  n_nbr    senders the receiver could hear; n_stale  entries older than 2 decision steps; max_age, mean_age (steps);
  fresh_d  per Manhattan distance 1..4 on the grid, the number of fresh entries from senders at that distance;
  need / zok / protoS as in the negative-flip probe (teacher A_0.25; DIAGNOSTIC oracle, records only).
Per cell also the age histogram (0..14 steps) of fresh and of relayed entries.
SELF-CHECK: queue sums and need / zok / protoS equal e3_negflip_20261001/s<s>_K<K> (--parity-dir).
"""
from __future__ import annotations
import argparse, hashlib, json, re, sys, time
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
from models.marl_relay_v2 import merge_views as merge_views_v2, AGE_CAP_STEPS
from models.marl_delivery_music import MusicDelivery
from scripts.MARL_e3_theory_probe import net_of
from scripts.MARL_e3_negflip_probe import ZPol, pre_flags, EPS, SOURCES as NF_SOURCES

SOURCES = ['scripts/MARL_e3_viewstats_probe_v3.py', 'scripts/MARL_e3_viewstats_probe_v2.py', 'scripts/MARL_e3_viewstats_probe.py'] + NF_SOURCES
STALE = 2


def coords(env):
    out = []
    for iid in env.agent_ids:
        a, b = map(int, re.findall(r'(\d+)_(\d+)$', iid)[0]); out.append((a, b))
    return out


def run(sc, seed, load, cks, book, K, zpol, order='agefirst', cap='iid'):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    kind = cap if cap in ('iid', 'low', 'high', 'bursty') else 'iid'
    env, pol = make(sc, seed, load, cks['relay'], kind)
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    xy = coords(env); dist = lambda i, j: abs(xy[i][0] - xy[j][0]) + abs(xy[i][1] - xy[j][1])
    mus = MusicDelivery(order); mus.mode = cap if cap.startswith('cap') else 'prefix'; m = env.n_agents; prev = None; q = 0.0; recs = []
    hist = np.zeros((2, AGE_CAP_STEPS + 2), np.int64)
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
            X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                Lr = pol.actor(torch.as_tensor(X), pol.mask).numpy()
            acts = {i: int(a) for i, a in enumerate(Lr.argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
        for i in range(m):
            need, zok, full, top = pre[i]
            direct = {e.sender for e in views[i].inbox}
            ages = []; nf = 0; fd = [0, 0, 0, 0]
            for e in mv[i].inbox:
                a = int(round(float(e.age) / float(env.action_interval))); ages.append(a)
                kind = 0 if e.sender in direct else 1; hist[kind, min(a, AGE_CAP_STEPS + 1)] += 1
                if kind == 0:
                    nf += 1; fd[min(dist(i, e.sender), 4) - 1] += 1
            recs.append(dict(t=t, recv=i, need=need, zok=zok, protoS=bool(full[acts[i]] >= top - EPS - 1e-9), n_fresh=nf,
                             n_relay=len(ages) - nf, n_nbr=len(env.neighbours[i]), n_stale=sum(a > STALE for a in ages),
                             max_age=max(ages) if ages else -1, mean_age=float(np.mean(ages)) if ages else -1.0,
                             fd1=fd[0], fd2=fd[1], fd3=fd[2], fd4=fd[3], b2=sum(max(a - 2, 0) for a in ages), b3=sum(max(a - 3, 0) for a in ages)))
    return q, recs, hist


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    paths = (('relay', a.relay), ('teacher', a.teacher), ('z', a.z))
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in paths}
    sc = Scenarios(out); pdir = Path(a.parity_dir) if a.parity_dir else None
    par = {r['episode']: r['queue_sum'] for r in json.loads((pdir / 'rows.json').read_text())} if pdir else {}
    pf = np.load(pdir / 'flags.npz') if pdir else None
    rows = []; allrec = []; H = None; t0 = time.perf_counter(); zpol = None
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'
            if zpol is None:
                CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
                _, zp0 = make(sc, seed, load, cks['z'], 'iid'); zpol = ZPol(cks['z'], zp0.adapter.topos, zp0.adapter.interval)
            q, rr, h = run(sc, seed, load, cks, book, a.K, zpol, a.order, a.capacity)
            if pdir and (ep not in par or abs(par[ep] - q) > 1e-6):
                raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != negflip row {par.get(ep)}')
            rows.append(dict(episode=ep, queue_sum=q)); allrec += [dict(seed=seed, load=load, **r) for r in rr]
            H = h if H is None else H + h
            print(f'[{time.perf_counter() - t0:.0f}s] {ep} done (parity ok)', flush=True)
    keys = ['seed', 'load', 't', 'recv', 'need', 'zok', 'protoS', 'n_fresh', 'n_relay', 'n_nbr', 'n_stale', 'max_age', 'mean_age',
            'fd1', 'fd2', 'fd3', 'fd4', 'b2', 'b3']
    F = {k: np.array([r[k] for r in allrec]) for k in keys}
    for k in (('need', 'zok', 'protoS', 'seed', 'load', 't', 'recv') if pf is not None else ()):
        if not np.array_equal(F[k], pf[k]):
            raise SystemExit(f'SELF-CHECK FAIL: flag {k} differs from the negative-flip probe')
    np.savez_compressed(out / 'flags.npz', age_hist=H, **F)
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', eps=EPS, K=a.K, args=vars(a),
        source_hashes=h0, records=len(allrec), seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--z', required=True)
    p.add_argument('--parity-dir', default=None); p.add_argument('--K', type=int, default=0)
    p.add_argument('--order', choices=['agefirst', 'prefix'], default='agefirst'); p.add_argument('--capacity', default='iid')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
