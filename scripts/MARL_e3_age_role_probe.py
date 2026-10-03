#!/usr/bin/env python3
"""AGE-ROLE PROBE on the CityFlow relay students (02/10/2026 12:2x; PROTOCOL_AGE_ROLE_PROBE_20261002.md).  Closed loop of
scripts/MARL_e3_ageremap_eval.py with --remap none (plain student acts), on development episodes; at every step and receiver:
f = log-softmax of the student's action logits on its merged view, f1 = the same with every present entry's age + 1 step
(saturated at 14), f0 = the same student on its local-only view (inbox and cache removed).  d = f − f0, Δ = f1 − f (invalid
actions zeroed); ρ = Σ <Δ, d>² / |d|² / Σ |Δ|².  Diagnostic only: nothing changes the executed actions.
Usage: MARL_e3_age_role_probe.py --relay ckpt --tag name --K k --traffic-seeds ... --out file.json"""
from __future__ import annotations
import argparse, json, sys
from dataclasses import replace
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


def aged(v, interval):
    return replace(v, inbox=tuple(replace(e, age=min(14, int(round(float(e.age) / float(interval))) + 1) * float(interval)) for e in v.inbox))


def local_only(v):
    return replace(v, inbox=(), cache=(), never_heard=tuple(sorted(int(j) for j in v.neighbours)))


def logp(pol, views, mask):
    X = np.stack([pol.adapter.encode(v, 'actual') for v in views])
    with torch.no_grad():
        z = pol.actor(torch.as_tensor(X), mask)
        lp = torch.log_softmax(z, -1)
    return torch.where(torch.isfinite(lp), lp, torch.zeros_like(lp)).numpy(), z.numpy()


def main(a):
    book = json.loads((ROOT / a.codebook).read_text()); ck = torch.load(Path(a.relay), weights_only=False)
    out = Path(a.out); sc = Scenarios(out.with_suffix('')); num = 0.0; den = 0.0; n = 0
    for seed in a.traffic_seeds:
        for load in a.headways:
            CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = quantized(CommAdapter, book, 4)
            env, pol = make(sc, seed, load, ck, 'iid')
            if a.K > 0:
                env._trace = np.full_like(np.asarray(env._trace), int(a.K))
            mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None
            for t in range(N_DEC):
                with no_oracle_access(env):
                    mus(env, seed, load, t)
                    views = env.transmit(); env.verify_mirror()
                    mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
                    V = [mv[i] for i in range(m)]
                    f, z = logp(pol, V, pol.mask); f1, _ = logp(pol, [aged(v, env.action_interval) for v in V], pol.mask)
                    f0, _ = logp(pol, [local_only(v) for v in V], pol.mask)
                    D = f - f0; Dl = f1 - f; nd = (D ** 2).sum(1); ok = nd > 1e-6
                    num += float(((Dl[ok] * D[ok]).sum(1) ** 2 / nd[ok]).sum()); den += float((Dl[ok] ** 2).sum()); n += int(ok.sum())
                    acts = {i: int(x) for i, x in enumerate(z.argmax(-1))}
                    env.step(acts)
            del env
    res = dict(tag=a.tag, K=a.K, rho=num / den if den > 0 else None, n=n, traffic_seeds=a.traffic_seeds, headways=a.headways)
    out.write_text(json.dumps(res, indent=1)); print(json.dumps(res), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--relay', required=True); p.add_argument('--tag', required=True); p.add_argument('--K', type=int, required=True)
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json'); p.add_argument('--out', required=True)
    main(p.parse_args())
