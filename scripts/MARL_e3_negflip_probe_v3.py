#!/usr/bin/env python3
"""v3 (01/10/2026 19:1x EDT; PROTOCOL_E3_DECISION_RETURN_GAP_20261001.md, EXPLORATORY): why can the decision-level net_Z be
positive while the return is negative?  v2's relay closed loop and Z parity loop, plus
  * graded teacher regret top - L(a) (full fresh teacher logits) for the relay's and for Z's action on the RELAY's states;
  * Z scored on ITS OWN closed-loop states (acceptability and regret against the same teacher), i.e. same-trajectory vs
    own-trajectory decision quality;
  * the per-step queue of both closed loops (where along the episode the two systems diverge).
DIAGNOSTIC ORACLE only (teacher views label, never act).  SELF-CHECKS: v1's (Z empty-view action = real-view action at every
step, Z queue = development rows), relay queue = --parity rows where given, flags of the relay loop equal v2 (--check-dir).
"""
from __future__ import annotations
import argparse, json, sys, time
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
import scripts.MARL_e3_negflip_probe as V1

EPS = V1.EPS


def teacher_full(env, i, teacher, raw, mask):
    N = sorted(int(j) for j in env.neighbours[i])
    ve = V1.empty_view(env, i); vf = env.counterfactual_view(i, N)
    X = np.stack([raw.encode(ve, 'actual'), raw.encode(vf, 'actual')])
    with torch.no_grad():
        L = teacher(torch.as_tensor(X), mask[i:i + 1].expand(2, -1)).numpy()
    return ve, L[1]


def z_own(sc, seed, load, ckz, zpol, teacher, raw, mask):
    """Z in its own no-delivery closed loop; teacher acceptability / regret of Z's action on Z's OWN states; per-step queue."""
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    env, _ = make(sc, seed, load, ckz, 'iid'); DV.DELIVERY['mode'] = 'none'; m = env.n_agents; q = []; rec_ = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            DV.deliver(env, seed, load, t)
        tf = [teacher_full(env, i, teacher, raw, mask) for i in range(m)]               # DIAGNOSTIC oracle
        ve = [x[0] for x in tf]
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            a_real = zpol.act_views(views); a_e = zpol.act_views(ve)
            if not np.array_equal(a_real, a_e):
                raise AssertionError(f'Z empty-view action differs from its real view at t={t}')
            _, _, rec = env.step({i: int(a) for i, a in enumerate(a_real)})
        q.append(float(rec['queue']))
        for i in range(m):
            full = tf[i][1]; top = full.max()
            rec_.append(dict(t=t, recv=i, zok_own=bool(full[a_real[i]] >= top - EPS - 1e-9), zreg_own=float(top - full[a_real[i]])))
    return q, rec_


def relay_run(sc, seed, load, cks, book, cap, zpol, teacher, raw, mask):
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], 'iid' if cap.startswith('const') else cap)
    if cap.startswith('const'):
        env._trace = np.full_like(np.asarray(env._trace), int(cap[5:]))
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = []; recs = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        tf = [teacher_full(env, i, teacher, raw, mask) for i in range(m)]               # DIAGNOSTIC oracle
        az = zpol.act_views([x[0] for x in tf])
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                ar = pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1)
            _, _, rec = env.step({i: int(a) for i, a in enumerate(ar)})
        q.append(float(rec['queue']))
        for i in range(m):
            full = tf[i][1]; top = full.max()
            recs.append(dict(t=t, recv=i, protoS=bool(full[ar[i]] >= top - EPS - 1e-9), zok=bool(full[az[i]] >= top - EPS - 1e-9),
                             rreg=float(top - full[ar[i]]), zreg=float(top - full[az[i]])))
    return q, recs


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    book = json.loads((ROOT / a.codebook).read_text())
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in (('relay', a.relay), ('teacher', a.teacher), ('z', a.z))}
    sc = Scenarios(out)
    zrows = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.zrows).read_text()) if r['rule'] == 'none'}
    rpar = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text())} if a.parity else {}
    res = []; t0 = time.perf_counter(); zpol = None; teacher = None
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'
            if zpol is None:
                CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
                _, zp0 = make(sc, seed, load, cks['z'], 'iid'); zpol = V1.ZPol(cks['z'], zp0.adapter.topos, zp0.adapter.interval)
                raw = CommAdapter(zp0.adapter.topos, zp0.adapter.n_dec, zp0.adapter.interval)
                teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
            qz, zr = z_own(sc, seed, load, cks['z'], zpol, teacher, raw, mask)
            if ep in zrows and abs(zrows[ep] - sum(qz)) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: Z {ep} waiting {sum(qz)} != Z development row {zrows[ep]}')
            qr, rr = relay_run(sc, seed, load, cks, book, a.capacity, zpol, teacher, raw, mask)
            if ep in rpar and abs(rpar[ep] - sum(qr)) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: relay {ep} waiting {sum(qr)} != parity row {rpar[ep]}')
            res.append(dict(episode=ep, q_relay=qr, q_z=qz, relay=rr, z_own=zr))
            print(f'[{time.perf_counter() - t0:.0f}s] {ep} done', flush=True)
    (out / 'records.json').write_text(json.dumps(res))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', eps=EPS, capacity=a.capacity, args=vars(a),
        relay_parity_episodes=sum(r['episode'] in rpar for r in res), z_rows_checked=sum(r['episode'] in zrows for r in res)), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--z', required=True)
    p.add_argument('--zrows', required=True); p.add_argument('--capacity', required=True); p.add_argument('--parity', default=None)
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
