#!/usr/bin/env python3
"""Codebook v2 for the Paper-A experiment (30/09 12:5x; ledger L-164): REFIT the 3 B codebook on the deployed policy's OWN
state distribution, and mix it with the original behaviour at weight beta.

Paper A: a frozen surrogate starves the decision cells it never visits, and the repair spends a beta fraction on the old
support.  The v1 codebook (`e3_payload_codebook_20260929.json`) was fitted once, on TRAIN traffic, under FULL delivery, with
the raw teacher set_full_s0 as behaviour.  The relay student visits other states (it acts on relay-merged, compressed
inputs under the prefix).
This script collects the RAW packet payloads that senders put on the air (phase_elapsed, vehicles and waiting per slot) on
TRAIN traffic under:
  * behaviour 'relay': a relay-trained checkpoint, acting on its own pipeline (prefix delivery, relay merge, --quant L of the
    v1 codebook), and
  * behaviour 'full': set_full_s0 under full delivery (the v1 behaviour, for the mixture).
It then fits equal-mass codebooks exactly as v1 (same `fit`) on
  key "<L>"      the relay behaviour only, and
  key "<1000*round(100*beta)+L>" (e.g. 50004 for beta = 0.5, L = 4)  a mixture: each field's samples = relay samples plus
                 a random beta-share of full-behaviour samples, sized so the full samples are a beta fraction of the pool.
The output has the v1 JSON layout (codebooks → key → {elapsed, vehicles, waiting, bits_per_packet}), so every existing
consumer (`models/marl_comm_actor_quant.py` via --quant <key> --codebook <file>) reads it unchanged.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
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
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized
from models.marl_relay import merge_views
from scripts.MARL_e3_payload_codebook import fit


def collect(sc, ck, seeds, mode, book, L):
    """Raw packet payload fields decoded by receivers on TRAIN traffic, under the behaviour's own pipeline."""
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, L) if mode == 'relay' else CommAdapter
    DV.DELIVERY['mode'] = 'prefix' if mode == 'relay' else 'full'
    el, veh, wai = [], [], []
    for seed in seeds:
        for load in (8.0, 16.0):
            env, pol = make(sc, seed, load, ck, 'iid'); prev = None
            for t in range(N_DEC):
                with no_oracle_access(env):
                    DV.deliver(env, seed, load, t); views = env.transmit()
                    for v in views.values():
                        for e in v.inbox:
                            el.append(e.payload.phase_elapsed); veh += list(e.payload.vehicles); wai += list(e.payload.waiting)
                    if mode == 'relay':
                        mv = merge_views(views, prev, t, 'age'); prev = mv; acts = pol.act(mv)
                    else:
                        acts = pol.act(views)
                    env.step(acts)
    return dict(elapsed=np.array(el, float), vehicles=np.array(veh, float), waiting=np.array(wai, float))


def book_of(samples, L):
    b = {f: fit(samples[f], L) for f in ('elapsed', 'vehicles', 'waiting')}
    bits = 4 + 4 + int(np.ceil(np.log2(b['elapsed']['levels']))) + 4 * int(np.ceil(np.log2(b['vehicles']['levels']))) \
        + 4 * int(np.ceil(np.log2(b['waiting']['levels'])))
    b['bits_per_packet'] = bits; b['bytes_per_packet'] = int(np.ceil(bits / 8))
    return b


def main(a):
    out = Path(a.out)
    if out.exists():
        raise SystemExit(f'{out} exists')
    book1 = json.loads((ROOT / a.codebook).read_text()); sc = Scenarios(Path(a.scratch))
    rel = collect(sc, torch.load(ROOT / a.relay_actor, weights_only=False), a.seeds, 'relay', book1, a.quant)
    full = collect(sc, torch.load(ROOT / a.full_actor, weights_only=False), a.seeds, 'full', book1, a.quant)
    rng = np.random.default_rng(0); books = {}
    for L in a.levels:
        books[str(L)] = book_of(rel, L)
        for beta in a.betas:
            mix = {}
            for f in rel:
                n_full = int(round(beta / (1 - beta) * len(rel[f]))) if beta < 1 else len(full[f])
                mix[f] = np.concatenate([rel[f], rng.choice(full[f], size=min(n_full, len(full[f])), replace=False)])
            books[str(1000 * int(round(100 * beta)) + L)] = book_of(mix, L)
    stat = lambda x: [float(np.percentile(x, q)) for q in (0, 25, 50, 75, 95, 100)]
    res = dict(producer='scripts/MARL_e3_payload_codebook_v2.py', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               relay_actor=a.relay_actor, full_actor=a.full_actor, seeds=a.seeds, headways=[8, 16], v1_codebook=a.codebook, v1_quant_for_relay_behaviour=a.quant,
               key_meaning='"<L>" = relay behaviour only; "<1000*round(100*beta)+L>" = relay samples plus a beta share of full-behaviour samples',
               n_samples=dict(relay={f: int(len(v)) for f, v in rel.items()}, full={f: int(len(v)) for f, v in full.items()}),
               raw_stats=dict(relay={f: stat(v) for f, v in rel.items()}, full={f: stat(v) for f, v in full.items()}), codebooks=books)
    out.write_text(json.dumps(res, indent=1))
    print(json.dumps({k: (b['bits_per_packet'], b['elapsed']['levels'], b['vehicles']['levels'], b['waiting']['levels']) for k, b in books.items()}))
    print('relay raw', res['raw_stats']['relay']); print('full raw', res['raw_stats']['full'])


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay-actor', required=True); p.add_argument('--full-actor', default='research/marl_budget/e3_delivery_actors_20260929/set_full_s0/ckpt_best.pt')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json'); p.add_argument('--quant', type=int, default=4)
    p.add_argument('--seeds', type=int, nargs='+', default=[309, 310, 311, 312]); p.add_argument('--levels', type=int, nargs='+', default=[4])
    p.add_argument('--betas', type=float, nargs='+', default=[0.5]); p.add_argument('--scratch', required=True); p.add_argument('--out', required=True)
    main(p.parse_args())
