#!/usr/bin/env python3
"""Paper-C experiment, preparation (30/09 12:5x; ledger L-164): COVERAGE and AGE of relay-merged views, the empirical basis of
a coverage lemma to state and prove in Lean ("one exchange suffices"; a d-step bound on the graph).

A checkpoint acts on its relay pipeline (relay merge, 3 B v1 codebook) under a delivery rule and capacity process.  At every
step and for every receiver it records:
  * coverage: the number of the m-1 other agents present in its merged view;
  * the age of every present summary, in DECISION STEPS (age seconds / action interval, rounded);
  * how many packets it decoded (K_i).
Reported per condition:
  * the coverage distribution;
  * the share of summaries at age 0 / 1 / 2 / 3 / >= 4 steps;
  * the maximum age seen after a burn-in of 2 steps;
  * coverage and age by K.
Development diagnostic; no claim.  --order agefirst uses models/marl_delivery_agefirst.py for the broadcast order.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, collections
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


def main(a):
    out = Path(a.out)
    if out.exists():
        raise SystemExit(f'{out} exists')
    book = json.loads((ROOT / a.codebook).read_text()); ck = torch.load(ROOT / a.actor, weights_only=False)
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = quantized(CommAdapter, book, a.quant)
    sc = Scenarios(Path(a.scratch)); res = {}
    for cond in a.conditions:                                   # "<delivery>:<capacity>", e.g. prefix:iid, cap4:iid, prefix:low
        rule, cap = cond.split(':'); DV.DELIVERY['mode'] = rule
        cov = []; ages = []; byK = collections.defaultdict(list); maxage_after = 0
        for seed in a.seeds:
            for load in (8.0, 16.0):
                env, pol = make(sc, seed, load, ck, cap); prev = None; dt = float(env.action_interval)
                for t in range(N_DEC):
                    with no_oracle_access(env):
                        DV.deliver(env, seed, load, t); views = env.transmit()
                        mv = merge_views(views, prev, t, 'age'); prev = mv
                        for i, v in mv.items():
                            k = len(views[i].inbox); c = len(v.inbox); cov.append(c); byK[k].append(c)
                            for e in v.inbox:
                                s = int(round(float(e.age) / dt)); ages.append(s)
                                if t >= 2:
                                    maxage_after = max(maxage_after, s)
                        env.step(pol.act(mv))
        ages = np.array(ages); cov = np.array(cov)
        res[cond] = dict(receiver_steps=int(len(cov)), coverage_mean=float(cov.mean()), coverage_hist={int(c): int((cov == c).sum()) for c in np.unique(cov)},
                         full_coverage_share=float((cov == 8).mean()),
                         age_share={str(s): float((ages == s).mean()) for s in range(4)} | {'>=4': float((ages >= 4).mean())},
                         max_age_steps_after_t2=int(maxage_after),
                         coverage_by_decoded_K={int(k): float(np.mean(v)) for k, v in sorted(byK.items())})
        print(cond, json.dumps(res[cond]))
    out.write_text(json.dumps(dict(producer='scripts/MARL_e3_relay_age_diag.py', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                                   actor=a.actor, seeds=a.seeds, headways=[8, 16], order=a.order, results=res), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor', required=True); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--quant', type=int, default=4); p.add_argument('--seeds', type=int, nargs='+', default=list(range(901, 917)))
    p.add_argument('--conditions', nargs='+', default=['prefix:iid', 'cap4:iid', 'cap2:iid', 'prefix:low'])
    p.add_argument('--order', choices=['prefix', 'agefirst'], default='prefix')
    p.add_argument('--scratch', required=True); p.add_argument('--out', required=True)
    a = p.parse_args()
    if a.order == 'agefirst':
        from models.marl_delivery_agefirst import deliver_agefirst
        DV.deliver = deliver_agefirst
    main(a)
