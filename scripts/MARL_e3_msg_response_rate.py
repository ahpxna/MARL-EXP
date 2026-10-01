#!/usr/bin/env python3
"""Direction 3 check (29/09 22:5x; ledger L-128): how SPARSE is the decision value of messages, and can a receiver
predict it from its OWN information?  QUERY's natural RWARE panel found other agents' actions changed agent 0's outcome in
5 / 9.5 / 28 % of states at horizons 1 / 2 / 6.

Positive control: set_full_s0 acting under FULL delivery (the configuration where messages are worth -5.8 %).  Along its own
closed-loop trajectories, every receiver-step is scored twice from the SAME view:
  * a_msg  = argmax of the actor on the delivered input (what it does);
  * a_none = argmax on the same view with every message removed (CommAdapter variant 'none').
The receiver-step NEEDS messages this step iff a_msg != a_none.  If all receivers' actions are unchanged, the joint action
and hence the next state are identical (LeanMarlDecisionCertificateV1.states_agree), so the step's messages were
decision-irrelevant.
Local predictors, legal at deployment (the receiver's own view only):
  * margin_none: top-1 minus top-2 logit of the no-message decision;
  * own waiting and own vehicles (sums over lanes);
  * headway.
Reported:
  * the change rate (overall, by headway);
  * the AUC of each predictor for "needs messages";
  * a REQUEST GATE: receiver i requests messages iff margin_none < tau.  Per tau it gives the share of receiver-steps that
    request, the share of changes captured, the share of steps with no request at all (a silent stream), and the share of
    SENDERS needed if each sender transmits only when one of its physical neighbours requests.
Offline scoring, no counterfactual rollouts: the closed loop is the actor's own full-delivery trajectory.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
from pathlib import Path
import numpy as np
import torch
from scipy.stats import rankdata

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


def auc(score, y):
    y = np.asarray(y, bool); s = np.asarray(score, float)
    if y.all() or (~y).all():
        return float('nan')
    r = rankdata(s); return float((r[y].sum() - y.sum() * (y.sum() + 1) / 2) / (y.sum() * (~y).sum()))


def main(a):
    out = Path(a.out)
    if out.exists():
        raise SystemExit(f'{out} exists')
    ck = torch.load(ROOT / a.actor, weights_only=False)
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    sc = Scenarios(Path(a.scratch)); DV.DELIVERY['mode'] = a.delivery
    R = []
    for seed in a.seeds:
        for load in (8.0, 16.0):
            env, pol = make(sc, seed, load, ck, 'iid'); nb = [set(env.physical_neighbours[i]) for i in range(env.n_agents)]
            for t in range(N_DEC):
                with no_oracle_access(env):
                    DV.deliver(env, seed, load, t); views = env.transmit()
                    m = env.n_agents
                    Xa = np.stack([pol.adapter.encode(views[i], 'actual') for i in range(m)])
                    Xn = np.stack([pol.adapter.encode(views[i], 'none') for i in range(m)])
                    with torch.no_grad():
                        La = pol.actor(torch.as_tensor(Xa), pol.mask).numpy(); Ln = pol.actor(torch.as_tensor(Xn), pol.mask).numpy()
                    acts = {i: int(La[i].argmax()) for i in range(m)}
                    for i in range(m):
                        srt = np.sort(Ln[i])[::-1]
                        R.append(dict(seed=seed, load=load, t=t, i=i, change=int(La[i].argmax() != Ln[i].argmax()),
                                      margin_none=float(srt[0] - srt[1]), own_wait=float(np.sum(views[i].lane_waiting)),
                                      own_veh=float(np.sum(views[i].lane_vehicles)), nb=sorted(nb[i])))
                    _, _, rec = env.step(acts)
    y = np.array([r['change'] for r in R]); mg = np.array([r['margin_none'] for r in R])
    res = dict(producer='scripts/MARL_e3_msg_response_rate.py', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               actor=a.actor, delivery=a.delivery, seeds=a.seeds, headways=[8, 16], receiver_steps=len(R),
               change_rate=float(y.mean()),
               change_rate_by_headway={str(h): float(np.mean([r['change'] for r in R if r['load'] == h])) for h in (8.0, 16.0)},
               auc=dict(neg_margin_none=auc(-mg, y), neg_own_wait=auc([-r['own_wait'] for r in R], y),
                        neg_own_veh=auc([-r['own_veh'] for r in R], y), light_headway=auc([r['load'] for r in R], y)))
    key = {}
    for k, r in enumerate(R):
        key.setdefault((r['seed'], r['load'], r['t']), []).append(k)
    gate = []
    for q in (0.05, 0.1, 0.2, 0.3, 0.5, 0.7, 0.9, 1.0):
        tau = float(np.quantile(mg, q)) if q < 1 else np.inf
        req = mg < tau if q < 1 else np.ones_like(mg, bool)
        silent = np.mean([not req[ks].any() for ks in key.values()])
        senders = []
        for ks in key.values():
            asked = set()
            for k in ks:
                if req[k]:
                    asked |= set(R[k]['nb'])
            senders.append(len(asked) / 9)
        gate.append(dict(q=q, tau=tau, request_share=float(req.mean()), changes_captured=float(y[req].sum() / max(1, y.sum())),
                         silent_step_share=float(silent), sender_share_nbr_gate=float(np.mean(senders))))
    res['request_gate'] = gate
    out.write_text(json.dumps(res, indent=1))
    print(json.dumps({k: v for k, v in res.items() if k not in ('request_gate',)}, indent=1))
    for g in gate:
        print(g)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor', default='research/marl_budget/e3_delivery_actors_20260929/set_full_s0/ckpt_best.pt')
    p.add_argument('--delivery', default='full'); p.add_argument('--seeds', type=int, nargs='+', default=list(range(901, 933)))
    p.add_argument('--scratch', required=True); p.add_argument('--out', required=True)
    main(p.parse_args())
