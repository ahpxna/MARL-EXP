#!/usr/bin/env python3
"""v9 (29/09 23:4x; ledger L-136): v8 plus --audit-every N: the per-step access audit keeps checks 1-6 at every step and
walks the view leaves (check 7) only at decision steps t % N == 0 (envs/external/cityflow_audit_sampled.py), TRAINING only,
approved by the user 23:4x.  --audit-every 1 is exactly v8.  Evaluation never uses this.
v8 docstring follows.
v8 (29/09 23:0x; ledger L-133): trainer v7 (imported unchanged) plus --quant L --codebook JSON.  The actor is TRAINED on
sender-side compressed payloads (models/marl_comm_actor_quant.py; codebook fitted on TRAIN traffic by
scripts/MARL_e3_payload_codebook.py), so that the byte-budget variant of PROTOCOL_E3_BYTEBUDGET_20260929 is trained
end to end, not only compressed at evaluation.  Evaluate with scripts/MARL_e3_delivery_eval_v7.py --quant L (the same
codebook).  Without --quant this is exactly v7.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_e3_actor_train_delivery_v7 as V7
from models.marl_comm_actor_quant import quantized
import envs.external.cityflow_audit_sampled as AUD

R = V7.R


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', required=True); p.add_argument('--seed', type=int, default=0)
    p.add_argument('--iters', type=int, default=200); p.add_argument('--eps-per-iter', type=int, default=8)
    p.add_argument('--epochs', type=int, default=4); p.add_argument('--minibatch', type=int, default=64)
    p.add_argument('--lr', type=float, default=3e-4); p.add_argument('--ent', type=float, default=0.01)
    p.add_argument('--hidden', type=int, default=128); p.add_argument('--eval-every', type=int, default=10)
    p.add_argument('--threads', type=int, default=2); p.add_argument('--p-mix', type=float, default=0.0)
    p.add_argument('--init-from'); p.add_argument('--stop-after', type=int, default=0)
    p.add_argument('--capacity', choices=['iid', 'fixed', 'high', 'low', 'bursty'], default='iid'); p.add_argument('--mask-nonneighbors', action='store_true'); p.add_argument('--set-actor', action='store_true'); p.add_argument('--arch', choices=['flat', 'set', 'sharedconcat', 'attn'], default='flat'); p.add_argument('--adapter', choices=['default', 'noise', 'freshonly'], default='default')
    p.add_argument('--delivery', choices=['prefix', 'full', 'none', 'random', 'nbr', 'rxq', 'rxold', 'mixrand0.25', 'mixrand0.5'] + [f'cap{c}' for c in range(1, 9)], required=True)
    p.add_argument('--quant', type=int, default=0); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--audit-every', type=int, default=1)
    a = p.parse_args()
    V7.DELIVERY['mode'] = a.delivery; V7.DELIVERY['capacity'] = a.capacity
    if a.set_actor:
        a.arch = 'set'
    import models.marl_comm_actor_variants as VAR
    from models.marl_comm_actor_set import SetActorNet
    R.ActorNet = {'flat': R.ActorNet, 'set': SetActorNet, 'sharedconcat': VAR.SharedConcatActorNet, 'attn': VAR.AttnActorNet}[a.arch]
    if a.adapter != 'default':
        R.CommAdapter = {'noise': VAR.NoiseCommAdapter, 'freshonly': VAR.FreshOnlyCommAdapter}[a.adapter]
    if a.mask_nonneighbors:
        from models.marl_comm_actor_masked import MaskedCommAdapter
        R.CommAdapter = MaskedCommAdapter
    if a.quant:
        R.CommAdapter = quantized(R.CommAdapter, json.loads((ROOT / a.codebook).read_text()), a.quant)
    AUD.install(a.audit_every)
    R.episode = V7.episode
    R.SOURCES = R.SOURCES + ['scripts/MARL_e3_actor_train_delivery_v9.py', 'envs/external/cityflow_audit_sampled.py', 'scripts/MARL_e3_actor_train_delivery_v8.py', 'models/marl_comm_actor_quant.py', a.codebook,
                             'scripts/MARL_e3_actor_train_delivery_v7.py', 'models/marl_comm_actor_variants.py', 'scripts/MARL_e3_actor_train_delivery_v6.py',
                             'scripts/MARL_hetero_panel_collect.py', 'scripts/MARL_e3_actor_train_delivery_v5.py', 'models/marl_comm_actor_set.py',
                             'scripts/MARL_e3_actor_train_delivery_v4.py', 'models/marl_comm_actor_masked.py', 'models/marl_hetero_selector.py', 'scripts/MARL_hetero_target_diag.py']
    R.main(a)
