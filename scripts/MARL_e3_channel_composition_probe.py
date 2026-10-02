#!/usr/bin/env python3
"""CHANNEL-COMPOSITION PROBE (01/10/2026 18:4x EDT; PROTOCOL_E3_G4_CONSTK_ADDENDUM1_20261001 prediction, EXPLORATORY).
The closed loop of MARL_e3_ageclip_eval.py (age-first, relay merge, 3 B adapter) with the relay student acting, recording only
the COMPOSITION of every receiver's merged view: entries, ages (decision steps), never-heard, b3 = sum_j (a_j - 3)+.  At constant
K the composition is a function of the channel schedule alone (no oracle, no teacher), so it can be computed for a grid before
any target run.  Runs on any grid through scripts/MARL_grid_relay_wrapper.py.
--relay none: fixed actions (first valid phase); the composition must equal the policy-driven run (checked by the caller).
SELF-CHECK: --parity rows (episode -> queue_sum) reproduced where given (same closed loop as the age-clip evaluator, A = -1).
"""
from __future__ import annotations
import argparse, json, sys
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


def run(sc, seed, load, ck, book, K):
    if ck is None:                                     # --no-policy: fixed actions (the composition does not depend on them)
        env, topo, _, _ = sc.env(seed, load); pol = None
    else:
        CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = quantized(CommAdapter, book, 4)
        env, pol = make(sc, seed, load, ck, 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; recs = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            if pol is None:
                acts = {i: int(topo[i].valid_phases[0]) for i in range(m)}
            else:
                X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
                with torch.no_grad():
                    acts = {i: int(a) for i, a in enumerate(pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
        for i in range(m):
            ages = [int(round(float(e.age) / float(env.action_interval))) for e in mv[i].inbox]
            recs.append(dict(t=t, n_ent=len(ages), never=len(mv[i].neighbours) - len(ages), max_age=max(ages) if ages else -1,
                             b3=sum(max(a - 3, 0) for a in ages), n_stale=sum(a > 2 for a in ages), ages=ages))
    return q, recs


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    book = json.loads((ROOT / a.codebook).read_text()); ck = None if a.relay == 'none' else torch.load(Path(a.relay), weights_only=False)
    par = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text())} if a.parity else {}
    sc = Scenarios(out); res = {}
    for K in a.K:
        allr = []
        for seed in a.traffic_seeds:
            for load in a.headways:
                ep = f'seed{seed}_load{load:g}'; q, rr = run(sc, seed, load, ck, book, K)
                if K == a.parity_K and ep in par and abs(par[ep] - q) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != parity row {par[ep]}')
                allr += rr
        f = lambda k: np.array([r[k] for r in allr], float)
        ma = f('max_age'); ma = ma[ma >= 0]
        res[K] = dict(entries=float(f('n_ent').mean()), never=float(f('never').mean()), stale=float(f('n_stale').mean()),
                      B3=float(f('b3').mean()), max_age_p50=float(np.percentile(ma, 50)), max_age_p95=float(np.percentile(ma, 95)),
                      max_age_p99=float(np.percentile(ma, 99)), steps=len(allr),
                      age_hist=np.bincount([x for r in allr for x in r['ages']], minlength=16).tolist(),
                      B_tau={tau: float(np.mean([sum(max(x - tau, 0) for x in r['ages']) for r in allr])) for tau in range(0, 15)})
        print(f'K={K if K else "iid"}: ' + ' '.join(f'{k} {v:.2f}' for k, v in res[K].items() if not isinstance(v, (list, dict))), flush=True)
    (out / 'composition.json').write_text(json.dumps(res, indent=1))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a)), indent=1, default=str))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True, help="relay checkpoint, or 'none' for fixed actions"); p.add_argument('--K', type=int, nargs='+', default=[1, 2, 3, 4, 0])
    p.add_argument('--parity', default=None); p.add_argument('--parity-K', type=int, default=1)
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
