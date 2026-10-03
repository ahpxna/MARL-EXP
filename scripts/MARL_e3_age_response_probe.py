#!/usr/bin/env python3
"""AGE-RESPONSE probe (01/10/2026 20:1x EDT; EXPLORATORY): on the relay student's own closed-loop states (const K or iid), set the
age label of EVERY relayed entry (age > 0) to a common value a (content unchanged) and record whether the student's argmax is in
the teacher's A_0.25, for a = 0..10.  Executed actions are the student's on the actual view (closed loop of the age-clip probe).
DIAGNOSTIC ORACLE (teacher labels only)."""
from __future__ import annotations
import argparse, json, sys
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
from scripts.MARL_e3_negflip_probe import ZPol, pre_flags, EPS
AGES = list(range(11))


def run(sc, seed, load, cks, book, K, zpol):
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; ok = np.zeros(len(AGES)); n = 0; base = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        pre = [pre_flags(env, i, teacher, raw, mask, zpol) for i in range(m)]
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            X = [pol.adapter.encode(mv[i], 'actual') for i in range(m)]
            for a in AGES:
                X += [pol.adapter.encode(replace(mv[i], inbox=tuple(replace(e, age=a * float(env.action_interval)) if float(e.age) > 0 else e
                                                                      for e in mv[i].inbox)), 'actual') for i in range(m)]
            with torch.no_grad():
                Lr = pol.actor(torch.as_tensor(np.stack(X)), pol.mask.repeat(len(AGES) + 1, 1)).numpy()
            acts = {i: int(a) for i, a in enumerate(Lr[:m].argmax(-1))}
            _, _, rec = env.step(acts)
        for i in range(m):
            full, top = pre[i][2], pre[i][3]
            base += full[acts[i]] >= top - EPS - 1e-9; n += 1
            for k in range(len(AGES)):
                ok[k] += full[int(Lr[(k + 1) * m + i].argmax())] >= top - EPS - 1e-9
    return ok, base, n


def main(a):
    D = Path('research/marl_budget/e3_delivery_actors_20260929'); book = json.loads((ROOT / 'research/marl_budget/e3_payload_codebook_20260929.json').read_text())
    res = {}
    for s in a.seeds:
        cks = {'relay': torch.load(D / f'relay6Cage_st_s{s}/ckpt_best.pt', weights_only=False), 'teacher': torch.load(D / f'set_full_s{s}/ckpt_best.pt', weights_only=False)}
        ckz = torch.load(D / f'distill_none_s{s}/ckpt_best.pt', weights_only=False)
        sc = Scenarios(Path(a.out) / f's{s}_K{a.K}'); CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
        _, zp0 = make(sc, 901, 8.0, ckz, 'iid'); zpol = ZPol(ckz, zp0.adapter.topos, zp0.adapter.interval)
        tot = np.zeros(len(AGES)); b = 0; n = 0
        for seed in (901, 902, 903, 904):
            for load in (8.0, 16.0):
                o, bb, nn = run(sc, seed, load, cks, book, a.K, zpol); tot += o; b += bb; n += nn
        res[s] = dict(acc_by_age=(tot / n).tolist(), acc_actual=b / n)
        print(f's{s} K={a.K}: actual {b / n:.3f} | ' + ' '.join(f'a{x}:{v:.3f}' for x, v in zip(AGES, tot / n)), flush=True)
    Path(a.out, f'age_response_K{a.K}.json').write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--K', type=int, required=True); p.add_argument('--seeds', type=int, nargs='+', default=list(range(10)))
    p.add_argument('--out', required=True); main(p.parse_args())
