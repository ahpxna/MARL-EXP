#!/usr/bin/env python3
"""Coverage × time SUPPORT TABLE of a training channel (02/10/2026 13:0x; PROTOCOL_E3_G4_TIME_PROJECTION_20261002.md).
Channel-side: for the training channel (iid by default) on development episodes 901–904 × 8/16, the set of decision steps at
which a receiver's merged view has each present count c (under age-first the views' composition does not depend on the
policy; relayCage_st_s0 of the given network only drives the simulator).  Written to JSON {c: sorted steps}.  Run under the
grid wrapper for 4×4.  Usage: MARL_e3_coverage_time_table.py --ckpt <ckpt> --K 0 --out table.json"""
import argparse, json, sys
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


def main(a):
    book = json.loads((ROOT / 'research/marl_budget/e3_payload_codebook_20260929.json').read_text())
    ck = torch.load(ROOT / a.ckpt, weights_only=False); sc = Scenarios(Path(a.out).with_suffix('')); S = {}
    for seed in (901, 902, 903, 904):
        for load in (8.0, 16.0):
            CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = quantized(CommAdapter, book, 4)
            env, pol = make(sc, seed, load, ck, 'iid')
            if a.K > 0:
                env._trace = np.full_like(np.asarray(env._trace), int(a.K))
            mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None
            for t in range(N_DEC):
                with no_oracle_access(env):
                    mus(env, seed, load, t); views = env.transmit()
                    mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
                    for i in range(m):
                        S.setdefault(len(mv[i].inbox), set()).add(t)
                    X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
                    with torch.no_grad():
                        acts = {i: int(x) for i, x in enumerate(pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1))}
                    env.step(acts)
            del env
    Path(a.out).write_text(json.dumps({str(c): sorted(v) for c, v in sorted(S.items())}, indent=1))
    print({c: (min(v), max(v), len(v)) for c, v in sorted(S.items())}, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--ckpt', required=True); p.add_argument('--K', type=int, default=0); p.add_argument('--out', required=True)
    main(p.parse_args())
