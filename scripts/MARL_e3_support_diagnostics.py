#!/usr/bin/env python3
"""SUPPORT DIAGNOSTICS (02/10/2026 12:5x; descriptive, channel-side; ledger L-266 / L-267 follow-up).  For the 3×3 relay channel
under age-first, relay v2 merge, at const K = 1, 2, 3 and iid, record per receiver-step the view statistics a learned receiver
can be sensitive to: fresh count (entries delivered directly this step), present count, maximum age, number of entries older
than 2 steps.  At constant K / iid under age-first these do not depend on the policy (the order uses the scheduler's
mirror only; capacities are exogenous) — the closed loop of relay6Cage_st_s0 is used only to drive the simulator.
For each (training channel, deployment channel) pair: the fraction of deployment receiver-steps whose statistic takes a
value NEVER seen under the training channel (out-of-support mass), per statistic and for the joint (fresh, max age).
Development episodes 901–904 × 8/16.  Usage: MARL_e3_support_diagnostics.py --out file.json"""
from __future__ import annotations
import argparse, json, sys
from collections import Counter
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
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


def stats(K, sc, ck, book, seeds, loads):
    out = []
    for seed in seeds:
        for load in loads:
            CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = quantized(CommAdapter, book, 4)
            env, pol = make(sc, seed, load, ck, 'iid')
            if K > 0:
                env._trace = np.full_like(np.asarray(env._trace), int(K))
            mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None
            for t in range(N_DEC):
                with no_oracle_access(env):
                    mus(env, seed, load, t); views = env.transmit()
                    mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
                    for i in range(m):
                        ages = [int(round(float(e.age) / float(env.action_interval))) for e in mv[i].inbox]
                        out.append((len(views[i].inbox), len(ages), max(ages) if ages else -1, sum(a > 2 for a in ages), t))
                    X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
                    with torch.no_grad():
                        acts = {i: int(x) for i, x in enumerate(pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1))}
                    env.step(acts)
            del env
    return out


def main(a):
    book = json.loads((ROOT / 'research/marl_budget/e3_payload_codebook_20260929.json').read_text())
    ck = torch.load(ROOT / a.ckpt, weights_only=False)
    names = {1: 'K1', 2: 'K2', 3: 'K3', 0: 'iid'}; S = {}
    for K in (1, 2, 3, 0):
        S[names[K]] = stats(K, Scenarios(Path(a.out).with_suffix('') / names[K]), ck, book, [901, 902, 903, 904], [8.0, 16.0])
        print(K, 'done', len(S[names[K]]), flush=True)
    feats = {'fresh': lambda r: r[0], 'present': lambda r: r[1], 'max_age': lambda r: r[2], 'n_older2': lambda r: r[3], 'fresh_x_maxage': lambda r: (r[0], r[2]),
             'present_x_step4': lambda r: (r[1], r[4] * 4 // N_DEC), 'present_x_late': lambda r: (r[1], r[4] >= N_DEC // 2)}
    res = dict(histograms={n: {f: dict(Counter(str(fn(r)) for r in S[n])) for f, fn in feats.items() if f in ('fresh', 'present', 'max_age', 'n_older2')} for n in S}, oos={})
    for tr in S:
        for dp in S:
            if tr == dp:
                continue
            res['oos'][f'{tr}->{dp}'] = {f: float(np.mean([fn(r) not in {fn(x) for x in S[tr]} for r in S[dp]])) for f, fn in feats.items()}
    Path(a.out).write_text(json.dumps(res, indent=1))
    for k, v in res['oos'].items():
        print(k, {f: round(x, 3) for f, x in v.items()}, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--out', required=True)
    p.add_argument('--ckpt', default='research/marl_budget/e3_delivery_actors_20260929/relay6Cage_st_s0/ckpt_best.pt'); main(p.parse_args())
