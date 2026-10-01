#!/usr/bin/env python3
"""THEORY PROBE for the relay method (30/09 15:4x EDT; ledger L-176).  DIAGNOSTIC: it uses the simulator's counterfactual
view (an oracle) to RECORD what other policies would do on the same state; the oracle never chooses an executed action.

Executed system = the saturated-age relay evaluator (`MARL_e3_delivery_eval_relay_satrot.py`): relay student, relay v2
merge (185-bit layout), cap-correct order (models/marl_delivery_music.py), 3 B v1 codebook.  SELF-CHECK: the executed
waiting must equal that evaluator's rows on the same episodes (--parity rows.json), and the AgeMirror must equal the
merged views at every step.

Recorded at every (step, receiver), from the SAME state:
  L_relay   relay student logits on its merged relay view (the executed input)
  L_fresh   relay student logits on the counterfactual FULL FRESH view (every other sender's current packet, age 0, 3 B)
  L_T       teacher logits on the full fresh RAW view (its training input)
  L_Tq      teacher logits on the full fresh 3 B view
  L_0       0-byte student logits on a view with no messages (its deployment input; construction checked at t = 0 against a
            real 'none' delivery)
  ages      relayed age in decision steps of every other agent in the merged view (-1 = absent), K_i, decoded count
Predictions tested offline (scripts/MARL_e3_theory_probe_report.py):
  V-F  FUNCTIONAL lifetime / D6 margin / MARL argmax_stable: argmax(L_relay) = argmax(L_fresh) whenever
       osc(L_relay - L_fresh) < top-1 gap of L_fresh (an identity; a pipeline check), and a PREDICTIVE certificate
       delta + nu * age < gap fitted on half of the traffic seeds and tested on the other half (soundness, coverage).
  V-U  UNIFIED / Paper B floor: the relay student's agreement with the teacher rises most where the 0-byte student
       disagrees with the teacher (where an obstruction hides in the local fibre).
  V-B  Paper B safe order / SUPPORT fibre: teacher(raw) vs teacher(3 B) disagreement is low and concentrated at small
       margins (the 3 B code resolves the teacher's obstructions).
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
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
import scripts.MARL_e3_actor_train_delivery_v7 as DV
import scripts.MARL_e3_continuation_labels as CLAB
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery, NEVER

SOURCES = ['scripts/MARL_e3_theory_probe.py', 'models/marl_relay_v2.py', 'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py',
           'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py',
           'scripts/MARL_e3_actor_train_delivery_v7.py', 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']


def net_of(ck, dim):
    n = SetActorNet(dim, ck['config']['hidden']); n.load_state_dict(ck['actor']); n.eval(); return n


def empty_view(v):
    return replace(v, inbox=(), cache=(), never_heard=tuple(v.neighbours))


def run(sc, seed, load, cks, rule, order, capacity, book):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], capacity)            # pol = the executed relay student, 3 B adapter
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    q4 = quantized(CommAdapter, book, 4)(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    teacher = net_of(cks['teacher'], raw.dim); zero = net_of(cks['zero'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    mus = MusicDelivery(order); mus.mode = rule; m = env.n_agents; prev = None; q = 0.0; rec_rows = []; mirror_steps = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        cf = [env.counterfactual_view(i, [j for j in range(m) if j != i]) for i in range(m)]      # DIAGNOSTIC oracle
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            for i in range(m):
                got = {e.sender: float(e.measured_at) for e in mv[i].inbox}
                for j in range(m):
                    tm = float(mus.mirror.table[i, j])
                    if (j in got) != (tm > NEVER / 2) or (j in got and abs(got[j] - tm) > 1e-6):
                        raise AssertionError(f'AgeMirror != merged view: t {t} receiver {i} agent {j}')
            mirror_steps += 1
            X_relay = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                L_relay = pol.actor(torch.as_tensor(X_relay), pol.mask).numpy()
            acts = {i: int(a) for i, a in enumerate(L_relay.argmax(-1))}
            ages = np.full((m, m), -1.0)
            for i in range(m):
                for e in mv[i].inbox:
                    ages[i, e.sender] = round(float(e.age) / float(env.action_interval))
            X0 = np.stack([raw.encode(empty_view(views[i]), 'actual') for i in range(m)])
            Kt = [int(env._k[i]) for i in range(m)]; dec = [len(views[i].inbox) for i in range(m)]
            _, _, rec = env.step(acts)
        Xf = np.stack([pol.adapter.encode(cf[i], 'actual') for i in range(m)])
        XT = np.stack([raw.encode(cf[i], 'actual') for i in range(m)]); XTq = np.stack([q4.encode(cf[i], 'actual') for i in range(m)])
        with torch.no_grad():
            L_fresh = pol.actor(torch.as_tensor(Xf), pol.mask).numpy()
            L_T = teacher(torch.as_tensor(XT), mask).numpy(); L_Tq = teacher(torch.as_tensor(XTq), mask).numpy()
            L_0 = zero(torch.as_tensor(X0), mask).numpy()
        q += float(rec['queue'])
        for i in range(m):
            rec_rows.append((t, i, Kt[i], dec[i], ages[i], L_relay[i], L_fresh[i], L_T[i], L_Tq[i], L_0[i], acts[i]))
    return q, rec_rows, mirror_steps


def check_zero_view(sc, cks, book):
    """At t = 0 the empty-view construction must encode exactly like a real 'none' delivery (same state, same step)."""
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    env, pol = make(sc, 901, 8.0, cks['zero'], 'iid'); raw = pol.adapter
    DV.DELIVERY['mode'] = 'none'
    with no_oracle_access(env):
        DV.deliver(env, 901, 8.0, 0); views = env.transmit()
    env2, _ = make(sc, 901, 8.0, cks['zero'], 'iid'); mus = MusicDelivery('prefix'); mus.mode = 'prefix'
    with no_oracle_access(env2):
        mus(env2, 901, 8.0, 0); views2 = env2.transmit()
    a = np.stack([raw.encode(views[i], 'actual') for i in range(env.n_agents)])
    b = np.stack([raw.encode(empty_view(views2[i]), 'actual') for i in range(env.n_agents)])
    return float(np.abs(a - b).max())


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in (('relay', a.relay), ('teacher', a.teacher), ('zero', a.zero))}
    sc = Scenarios(out); zdiff = check_zero_view(sc, cks, book)
    if zdiff > 1e-6:
        raise SystemExit(f'SELF-CHECK FAIL: empty-view construction differs from a real none delivery by {zdiff}')
    parity = {}
    if a.parity:
        parity = {r['episode']: r for r in json.loads(Path(a.parity).read_text()) if r['rule'] == a.rule}
    rows = []; recs = []; t0 = time.perf_counter(); msteps = 0
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'; q, rr, ms = run(sc, seed, load, cks, a.rule, a.order, a.capacity, book); msteps += ms
            if ep in parity and abs(parity[ep]['queue_sum'] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != evaluator row {parity[ep]["queue_sum"]}')
            rows.append(dict(episode=ep, queue_sum=q, parity_checked=ep in parity))
            for r in rr:
                recs.append((seed, load) + r)
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
    m = recs[0][6].shape[0]
    arr = {k: np.array([r[i] for r in recs]) for i, k in enumerate(['seed', 'load', 't', 'recv', 'K', 'decoded'])}
    arr.update({k: np.stack([r[i] for r in recs]) for i, k in [(6, 'ages'), (7, 'L_relay'), (8, 'L_fresh'), (9, 'L_T'), (10, 'L_Tq'), (11, 'L_0')]})
    arr['act'] = np.array([r[12] for r in recs])
    np.savez_compressed(out / 'probe.npz', **arr); (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', zero_view_max_diff=zdiff, mirror_checked_steps=msteps,
                                                       parity_episodes=sum(r['parity_checked'] for r in rows), args=vars(a), source_hashes=h0,
                                                       records=len(recs), seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    D = 'research/marl_budget/e3_delivery_actors_20260929'
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--zero', required=True)
    p.add_argument('--order', choices=['prefix', 'agefirst', 'bass'], default='agefirst'); p.add_argument('--rule', default='prefix')
    p.add_argument('--capacity', default='iid'); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 965))); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--parity', default=None, help='the satrot evaluator rows.json of the same actor/order/capacity'); p.add_argument('--out', required=True)
    main(p.parse_args())
