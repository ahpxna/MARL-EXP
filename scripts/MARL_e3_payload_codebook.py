#!/usr/bin/env python3
"""Sender-side payload codebook for the direction-2 diagnostic (29/09 22:4x; ledger L-128).

Direction 2 (L-123): compress each packet to a decision-relevant summary, so that all senders fit a BYTE budget.  This
script fits the codebook on TRAINING traffic only (seeds 301-304 x headways 8/16, never an evaluation panel).  The
behaviour policy is the set_full_s0 actor under FULL delivery.  Every payload a receiver decodes is pooled:
  * phase_elapsed (seconds);
  * vehicles per approach slot;
  * waiting per approach slot.
For L in {2, 4, 8, 16}, each field gets equal-mass bins, with edges at empirical quantiles (duplicate edges merged; the
data are integers).  The representative of a bin is its conditional mean on the training payloads.
Output: JSON with edges and representatives per field and L, plus the bit cost per packet (sender id 4 bits, phase
4 bits, elapsed log2 L, 8 counts x log2 L; measured_at is implicit, since a fresh packet is this step's).
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


def fit(values, L):
    v = np.asarray(values, float); qs = np.quantile(v, np.linspace(0, 1, L + 1)[1:-1])
    edges = sorted(set([float(np.floor(v.min()))] + [float(np.ceil(q)) for q in qs]))   # integer edges, bin k = [e_k, e_{k+1})
    reps = []
    for k, lo in enumerate(edges):
        hi = edges[k + 1] if k + 1 < len(edges) else np.inf
        sel = v[(v >= lo) & (v < hi)]
        reps.append(float(sel.mean()) if sel.size else float(lo))
    return dict(edges=edges, reps=reps, levels=len(edges))


def main(a):
    out = Path(a.out)
    if out.exists():
        raise SystemExit(f'{out} exists')
    ck = torch.load(ROOT / a.actor, weights_only=False)
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    sc = Scenarios(Path(a.scratch)); DV.DELIVERY['mode'] = 'full'
    el, veh, wai = [], [], []
    for seed in a.seeds:
        for load in (8.0, 16.0):
            env, pol = make(sc, seed, load, ck, 'iid')
            for t in range(N_DEC):
                with no_oracle_access(env):
                    DV.deliver(env, seed, load, t); views = env.transmit()
                    for v in views.values():
                        for e in v.inbox:
                            el.append(e.payload.phase_elapsed); veh += list(e.payload.vehicles); wai += list(e.payload.waiting)
                    _, _, rec = env.step(pol.act(views))
    books = {str(L): dict(elapsed=fit(el, L), vehicles=fit(veh, L), waiting=fit(wai, L)) for L in a.levels}
    for L, b in books.items():
        bits = 4 + 4 + int(np.ceil(np.log2(b['elapsed']['levels']))) + 4 * int(np.ceil(np.log2(b['vehicles']['levels']))) \
            + 4 * int(np.ceil(np.log2(b['waiting']['levels'])))
        b['bits_per_packet'] = bits; b['bytes_per_packet'] = int(np.ceil(bits / 8))
    res = dict(producer='scripts/MARL_e3_payload_codebook.py', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               actor=a.actor, seeds=a.seeds, headways=[8, 16], n_packets=len(el), raw_bytes_per_packet=25,
               raw_stats=dict(elapsed=[float(np.percentile(el, q)) for q in (0, 25, 50, 75, 95, 100)],
                              vehicles=[float(np.percentile(veh, q)) for q in (0, 25, 50, 75, 95, 100)],
                              waiting=[float(np.percentile(wai, q)) for q in (0, 25, 50, 75, 95, 100)]),
               codebooks=books)
    out.write_text(json.dumps(res, indent=1))
    print(json.dumps({L: (b['bits_per_packet'], b['bytes_per_packet'], b['elapsed']['levels'], b['vehicles']['levels'], b['waiting']['levels']) for L, b in books.items()}))
    print('raw', res['raw_stats'], 'packets', len(el))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor', default='research/marl_budget/e3_delivery_actors_20260929/set_full_s0/ckpt_best.pt')
    p.add_argument('--seeds', type=int, nargs='+', default=[301, 302, 303, 304]); p.add_argument('--levels', type=int, nargs='+', default=[2, 4, 8, 16])
    p.add_argument('--scratch', required=True); p.add_argument('--out', required=True)
    main(p.parse_args())
