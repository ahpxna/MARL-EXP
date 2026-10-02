#!/usr/bin/env python3
"""NEGATIVE-FLIP PROBE vs the actual zero-byte student Z (01/10/2026 11:5x EDT; PROTOCOL_E3_NEGFLIP_VS_Z_20261001.md,
EXPLORATORY).  DIAGNOSTIC ORACLE: counterfactual views, the teacher and Z RECORD flags; nothing here chooses an executed
action of the relay system.

System: relay6Cage_st_s<s> closed loop, age-first, capacity const K (K = 0: the iid training process, the trace of
make(..., 'iid') kept), relay v2 merge, 3 B adapter (the code path of MARL_e3_protocol_demand_probe.py).  Per receiver-step:
  need   teacher argmax on the EMPTY view (local observation only) not in A_0.25 of the teacher's full fresh logits
  protoS the relay student's executed action in A_0.25
  zok    Z's argmax on the EMPTY view in A_0.25 (Z = distill_none_s<s>, default adapter, no messages)
  n_ent / mean_age / max_age  entries of the merged view the relay student reads and their ages in decision steps
SELF-CHECKS: (1) per episode, Z acting from the EMPTY view in a no-delivery closed loop equals Z acting from its real
transmit views at every step and reproduces the e3_dev_Z_20261001 queue sum (--zrows); (2) with every neighbour fresh the
cache and empty bases coincide; (3) teacher, relay and Z encodings have the same dimension.
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
import scripts.MARL_e3_actor_train_delivery_v7 as DV
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery
from scripts.MARL_e3_theory_probe import net_of

SOURCES = ['scripts/MARL_e3_negflip_probe.py', 'scripts/MARL_e3_protocol_demand_probe.py', 'scripts/MARL_e3_theory_probe.py',
           'models/marl_relay_v2.py', 'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py',
           'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py',
           'scripts/MARL_e3_actor_train_delivery_v7.py', 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']
EPS = 0.25


class ZPol:
    def __init__(self, ck, topos, interval):
        if not ck['config'].get('set_actor') or ck['config'].get('adapter', 'default') != 'default':
            raise SystemExit('Z checkpoint is not a default-adapter set actor')
        self.adapter = CommAdapter(topos, N_DEC, interval)
        if self.adapter.schema() != ck['schema']:
            raise SystemExit('Z adapter schema differs from the checkpoint')
        self.actor = SetActorNet(self.adapter.dim, ck['config']['hidden']); self.actor.load_state_dict(ck['actor']); self.actor.eval()
        self.mask = torch.as_tensor(self.adapter.valid_mask())

    def act_views(self, views):
        X = np.stack([self.adapter.encode(views[i], 'actual') for i in range(len(views))])
        with torch.no_grad():
            return self.actor(torch.as_tensor(X), self.mask).numpy().argmax(-1)


def empty_view(env, i):
    v0 = env.counterfactual_view(i, [])
    return replace(v0, cache=(), never_heard=tuple(sorted(int(j) for j in env.neighbours[i])))


def z_parity(sc, seed, load, ckz, zpol):
    """Z in its own no-delivery closed loop, acting from the EMPTY counterfactual view; must equal its real-view action."""
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    env, _ = make(sc, seed, load, ckz, 'iid'); DV.DELIVERY['mode'] = 'none'; q = 0.0; m = env.n_agents
    for t in range(N_DEC):
        with no_oracle_access(env):
            DV.deliver(env, seed, load, t)
        ve = [empty_view(env, i) for i in range(m)]                                             # DIAGNOSTIC oracle
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            a_real = zpol.act_views(views); a_e = zpol.act_views(ve)
            if not np.array_equal(a_real, a_e):
                raise AssertionError(f'Z empty-view action differs from its real view at t={t}')
            _, _, rec = env.step({i: int(a) for i, a in enumerate(a_real)})
        q += float(rec['queue'])
    return q


def pre_flags(env, i, teacher, raw, mask, zpol):
    N = sorted(int(j) for j in env.neighbours[i])
    ve = empty_view(env, i); vf = env.counterfactual_view(i, N)
    X = np.stack([raw.encode(ve, 'actual'), raw.encode(vf, 'actual'), raw.encode(replace(vf, cache=()), 'actual')])
    with torch.no_grad():
        L = teacher(torch.as_tensor(X), mask[i:i + 1].expand(X.shape[0], -1)).numpy()
    full = L[1]
    if np.abs(L[2] - full).max() > 1e-5:
        raise AssertionError(f'bases differ with every neighbour fresh at receiver {i}')
    top = full.max()
    need = not (full[int(L[0].argmax())] >= top - EPS - 1e-9)
    xz = zpol.adapter.encode(ve, 'actual')
    with torch.no_grad():
        az = int(zpol.actor(torch.as_tensor(xz[None]), zpol.mask[i:i + 1]).numpy().argmax(-1)[0])
    return need, bool(full[az] >= top - EPS - 1e-9), full, top


def run(sc, seed, load, cks, book, K, zpol):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    if raw.dim != pol.adapter.dim or raw.dim != zpol.adapter.dim:
        raise AssertionError('teacher, relay and Z encodings differ in dimension')
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
            X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                Lr = pol.actor(torch.as_tensor(X), pol.mask).numpy()
            acts = {i: int(a) for i, a in enumerate(Lr.argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
        for i in range(m):
            need, zok, full, top = pre[i]
            ages = [float(e.age) / float(env.action_interval) for e in mv[i].inbox]
            recs.append(dict(t=t, recv=i, need=need, zok=zok, protoS=bool(full[acts[i]] >= top - EPS - 1e-9), n_ent=len(ages),
                             mean_age=float(np.mean(ages)) if ages else -1.0, max_age=float(max(ages)) if ages else -1.0))
    return q, recs


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    paths = (('relay', a.relay), ('teacher', a.teacher), ('z', a.z))
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in paths}
    ck_sha = {k: hashlib.sha256(Path(p).read_bytes()).hexdigest() for k, p in paths}
    sc = Scenarios(out)
    zrows = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.zrows).read_text()) if r['rule'] == 'none'}
    rows = []; allrec = []; t0 = time.perf_counter(); zpol = None
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'
            if zpol is None:
                CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
                _, zp0 = make(sc, seed, load, cks['z'], 'iid'); zpol = ZPol(cks['z'], zp0.adapter.topos, zp0.adapter.interval)
            qz = z_parity(sc, seed, load, cks['z'], zpol)
            if ep not in zrows or abs(zrows[ep] - qz) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: Z {ep} waiting {qz} != e3_dev_Z row {zrows.get(ep)}')
            q, rr = run(sc, seed, load, cks, book, a.K, zpol)
            rows.append(dict(episode=ep, queue_sum=q, z_queue_sum=qz))
            allrec += [dict(seed=seed, load=load, **r) for r in rr]
            print(f'[{time.perf_counter() - t0:.0f}s] {ep} done (Z parity ok)', flush=True)
    keys = ['seed', 'load', 't', 'recv', 'need', 'zok', 'protoS', 'n_ent', 'mean_age', 'max_age']
    np.savez_compressed(out / 'flags.npz', **{k: np.array([r[k] for r in allrec]) for k in keys})
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', eps=EPS, K=a.K, args=vars(a),
        z_parity_episodes=len(rows), checkpoint_sha256=ck_sha, source_hashes=h0, records=len(allrec),
        seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--z', required=True)
    p.add_argument('--zrows', required=True); p.add_argument('--K', type=int, required=True, help='constant K; 0 = iid')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
