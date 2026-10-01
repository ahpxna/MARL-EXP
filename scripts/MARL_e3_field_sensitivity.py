#!/usr/bin/env python3
"""Paper-B experiment, preparation (30/09 12:5x; ledger L-164): a DECISION-FOCUSED codebook.  Bits go to the payload fields
whose distinctions change the action.

Paper B: the query class, not the query count, sets the rate; obstructions are the pairs a decision must separate.  The v1
codebook gives every field the same number of equal-mass levels.  Here:
  1. A relay-trained checkpoint acts on its own deployment pipeline (prefix, relay merge, 3 B v1 codebook) on TRAIN traffic.
     Every actor input is recorded, and so is every raw packet field on the air.
  2. The decision margin (top-1 minus top-2 logit) is differentiated with respect to the input.  Per payload field group
     (elapsed 1 dim, vehicles 4, waiting 4) of every HEARD sender block, sensitivity s_f = mean |d margin / d x| x the
     field's std in input units: the margin change per one-std change of the field.
  3. For every allocation of equal-mass levels L_f ∈ {1, 2, 4, 8, 16} per field, the quantisation MSE D_f(L_f) of the
     field is computed on the recorded raw samples, using the v1 fitting rule; L = 1 is a single bin at the mean.  The
     predicted margin distortion is sum_f s_f^2 D_f / var_f.  The dynamic bits are b_e + 4 b_v + 4 b_w, with sender id and
     phase fixed at 8 bits.  For each budget of dynamic bits, the best allocation is written as a codebook key
     "<9000 + budget>" in the v1 JSON layout, so the existing --quant/--codebook consumers read it unchanged.
Output: a JSON with sensitivities, the full allocation table, and the codebooks.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, sys
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_zero_loss_truncation import make
import scripts.MARL_e3_actor_train_delivery_v7 as DV
import scripts.MARL_e3_continuation_labels as CLAB
from models.marl_comm_actor import CommAdapter, N_PH, SCALE_P, SCALE_T
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized, _q
from models.marl_relay import merge_views
from scripts.MARL_e3_payload_codebook import fit

FIELDS = {'elapsed': (slice(3 + N_PH, 4 + N_PH), SCALE_T), 'vehicles': (slice(4 + N_PH, 8 + N_PH), SCALE_P), 'waiting': (slice(8 + N_PH, 12 + N_PH), SCALE_P)}
MULT = {'elapsed': 1, 'vehicles': 4, 'waiting': 4}


def one_level(v):
    return dict(edges=[float(np.floor(v.min()))], reps=[float(v.mean())], levels=1)


def main(a):
    out = Path(a.out)
    if out.exists():
        raise SystemExit(f'{out} exists')
    book1 = json.loads((ROOT / a.codebook).read_text()); ck = torch.load(ROOT / a.actor, weights_only=False)
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = quantized(CommAdapter, book1, a.quant); DV.DELIVERY['mode'] = 'prefix'
    sc = Scenarios(Path(a.scratch)); X = []; raw = {f: [] for f in FIELDS}; pol = None
    for seed in a.seeds:
        for load in (8.0, 16.0):
            env, pol = make(sc, seed, load, ck, 'iid'); prev = None
            for t in range(N_DEC):
                with no_oracle_access(env):
                    DV.deliver(env, seed, load, t); views = env.transmit()
                    for v in views.values():
                        for e in v.inbox:
                            raw['elapsed'].append(e.payload.phase_elapsed); raw['vehicles'] += list(e.payload.vehicles); raw['waiting'] += list(e.payload.waiting)
                    mv = merge_views(views, prev, t, 'age'); prev = mv
                    X.append(np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(env.n_agents)]))
                    env.step(pol.act(mv))
    X = torch.as_tensor(np.concatenate(X)).requires_grad_(True); ad = pol.adapter; base = ad.own_dim + ad.m
    M = pol.mask.repeat(X.shape[0] // pol.mask.shape[0], 1)
    lg = pol.actor(X, M); top2 = lg.topk(2, -1).values; (top2[:, 0] - top2[:, 1]).sum().backward()
    G = X.grad.detach().numpy(); Xn = X.detach().numpy()
    blocks = [(base + k * ad.blk_dim) for k in range(ad.m - 1)]
    sens = {}
    for f, (sl, scale) in FIELDS.items():
        g, x = [], []
        for b0 in blocks:
            heard = Xn[:, b0 + 1] > 0.5
            g.append(np.abs(G[heard][:, b0 + sl.start: b0 + sl.stop]).ravel()); x.append(Xn[heard][:, b0 + sl.start: b0 + sl.stop].ravel())
        g, x = np.concatenate(g), np.concatenate(x)
        sens[f] = float(g.mean() * x.std())                          # margin change per one-std change of the field
    raw = {f: np.asarray(v, float) for f, v in raw.items()}; var = {f: float(raw[f].var()) for f in raw}
    books_f = {f: {1: one_level(raw[f]), **{L: fit(raw[f], L) for L in (2, 4, 8, 16)}} for f in raw}
    D = {f: {L: float(np.mean((_q(raw[f], books_f[f][L]) - raw[f]) ** 2)) for L in books_f[f]} for f in raw}
    table = []
    for Le, Lv, Lw in itertools.product((1, 2, 4, 8, 16), repeat=3):
        bits = {f: int(np.ceil(np.log2(books_f[f][L]['levels']))) if books_f[f][L]['levels'] > 1 else 0 for f, L in zip(('elapsed', 'vehicles', 'waiting'), (Le, Lv, Lw))}
        dyn = bits['elapsed'] + 4 * bits['vehicles'] + 4 * bits['waiting']
        dist = sum(sens[f] ** 2 * D[f][L] / max(var[f], 1e-9) for f, L in zip(('elapsed', 'vehicles', 'waiting'), (Le, Lv, Lw)))
        table.append(dict(L=dict(elapsed=Le, vehicles=Lv, waiting=Lw), dyn_bits=dyn, bits_per_packet=8 + dyn, predicted_margin_distortion=dist))
    codebooks = {}
    for budget in a.budgets:
        ok = [r for r in table if r['dyn_bits'] <= budget]
        best = min(ok, key=lambda r: r['predicted_margin_distortion'])
        cb = {f: books_f[f][best['L'][f]] for f in raw}
        cb['bits_per_packet'] = best['bits_per_packet']; cb['bytes_per_packet'] = int(np.ceil(best['bits_per_packet'] / 8)); cb['allocation'] = best['L']
        codebooks[str(9000 + budget)] = cb
    uni = [r for r in table if r['L']['elapsed'] == r['L']['vehicles'] == r['L']['waiting']]
    res = dict(producer='scripts/MARL_e3_field_sensitivity.py', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), actor=a.actor,
               seeds=a.seeds, headways=[8, 16], n_inputs=int(X.shape[0]), sensitivity=sens, field_var=var, quant_mse=D,
               key_meaning='"<9000 + dynamic-bit budget>": the allocation with the least predicted margin distortion under that budget',
               uniform_rows=uni, codebooks=codebooks, table=table)
    out.write_text(json.dumps(res, indent=1))
    print('sensitivity', sens)
    for k, cb in codebooks.items():
        print(k, cb['allocation'], cb['bits_per_packet'], 'bits')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor', required=True); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--quant', type=int, default=4); p.add_argument('--seeds', type=int, nargs='+', default=[313, 314, 315, 316])
    p.add_argument('--budgets', type=int, nargs='+', default=[8, 12, 16]); p.add_argument('--scratch', required=True); p.add_argument('--out', required=True)
    main(p.parse_args())
