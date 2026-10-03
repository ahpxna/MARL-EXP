#!/usr/bin/env python3
"""TEACHER-MARGIN PROBE (01/10/2026 11:2x EDT; PROTOCOL_E3_G4_REPLICATION_ADDENDUM1_20261001.md).  DIAGNOSTIC: records the
teacher's top-2 logit gap on each receiver's full fresh counterfactual view along the executed relay closed loop (the V-D v1
system: relay student, age-first, the given capacity, relay v2 merge — or the slot merge under the grid relay wrapper).
No oracle quantity chooses an executed action.  SELF-CHECK: the executed waiting equals the evaluator's rows (--parity).
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
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

SOURCES = ['scripts/MARL_e3_teacher_margin_probe.py', 'scripts/MARL_e3_theory_probe.py', 'models/marl_relay_v2.py',
           'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py',
           'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py']


def run(sc, seed, load, cks, book, capacity):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], capacity)
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; margins = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        X = np.stack([raw.encode(env.counterfactual_view(i, list(env.neighbours[i])), 'actual') for i in range(m)])   # DIAGNOSTIC
        with torch.no_grad():
            L = teacher(torch.as_tensor(X), mask).numpy()
        Ls = np.sort(np.where(np.isfinite(L) & (L > -1e8), L, -np.inf), axis=-1)
        margins += list(Ls[:, -1] - Ls[:, -2])
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            Xr = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                Lr = pol.actor(torch.as_tensor(Xr), pol.mask).numpy()
            _, _, rec = env.step({i: int(a) for i, a in enumerate(Lr.argmax(-1))})
        q += float(rec['queue'])
    return q, margins


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in (('relay', a.relay), ('teacher', a.teacher))}
    sc = Scenarios(out)
    parity = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text()) if r['rule'] == 'prefix'}
    allm = []; npar = 0; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'; q, mg = run(sc, seed, load, cks, book, a.capacity)
            if ep in parity:
                if abs(parity[ep] - q) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != evaluator row {parity[ep]}')
                npar += 1
            allm += mg
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
    np.save(out / 'margins.npy', np.asarray(allm, np.float32))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), parity_episodes=npar,
        mean_margin=float(np.mean(allm)), records=len(allm), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, float(np.mean(allm)), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--parity', required=True)
    p.add_argument('--capacity', default='low'); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 933))); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
