#!/usr/bin/env python3
"""DECISION-DEPTH PROBE v3 (01/10 08:2x EDT; directions A and D, ledger L-199): v2 plus, for the EMPTY base only, the
acceptability bit of EVERY sender subset of size <= 2 at eps = 0.25, stored with the receiver's neighbour list, so that
(D) the best common order, per-sender relevance and pairwise interactions (approximate modularity) can be computed
offline.  Fields added: `sub_ok` (records x 37 bool, subsets in the order (), singletons, pairs of the sorted
neighbours; padded with False when |N| < 8) and `nbrs` (records x 8, -1 padded).
v2 description follows.
DECISION-DEPTH PROBE v2 (01/10 01:1x EDT): v1 built every prefix view on top of the receiver's DIRECT CACHE (stale copies
of earlier receptions; `env._build_view` keeps non-heard senders as cache entries), so its "depth 0" meant "the cached,
stale view already suffices", not "no message".  v2 records BOTH bases, labelled:
  base 'cache' — v1's quantity (fresh first-k senders on top of the direct cache);
  base 'empty' — fresh first-k senders and NOTHING else (cache stripped, every other sender never heard): the pure
                 decision depth of LeanMarlDecisionDepthV1 (no prior information beyond the local observation).
v1 description follows.
DECISION-DEPTH PROBE (01/10 01:0x EDT; theory: work/p13_conjectures/LeanMarlDecisionDepthV1.lean).  DIAGNOSTIC: it uses
the simulator's counterfactual view (an oracle) to RECORD how many decoded senders the TEACHER needs before its action is
acceptable; the oracle never chooses an executed action.

Executed system = the theory probe's (`scripts/MARL_e3_theory_probe.py`): relay student, relay v2 merge, the chosen stream
order, 3 B v1 codebook.  SELF-CHECK: the executed waiting must equal the satrot evaluator's rows on the same episodes
(--parity), exactly as in the theory probe; the full counterfactual view of each receiver must reproduce the teacher
logits of the all-senders view built independently.

ACCEPTABLE SET (a labelled, TEACHER-DEFINED proxy, NOT ground truth): with L_full the teacher's logits on the full fresh
raw view, A_eps = {a : L_full(a) >= max L_full - eps} for eps in EPS (logit units).  Lean's `safe` is a model input; this
probe instantiates it with the teacher, which the paper must say.

Recorded at every (step, receiver i), from the SAME state, with N_i = i's neighbours:
  depth[o, e]  the least k such that argmax L(view of the first k senders of order o, restricted to N_i) lies in A_eps
               (orders o: 'stream' = the executed stream order; 'reverse'; 'random' = a seeded permutation per step);
               the prefix decision depth of LeanMarlDecisionDepthV1 for this receiver and state, with safe := A_eps.
  minset[e]    the least size of ANY sender subset S of N_i (searched up to size 2; 3 means "more than 2") whose view's
               argmax lies in A_eps: the per-receiver hitting size, without the common-order constraint.
  K, nN        the receiver's revealed capacity and |N_i|.
Predictions written BEFORE the run (ledger L-192): (P1) minset << nN at eps > 0 (decide << identify);
(P2) depth(stream) >= minset, and the gap is positive on a non-trivial share of receiver-steps (the price of a common
order); (P3) depth decreases with eps; (P4) the share of receiver-steps with depth(stream) <= K is higher under the
age-first order than under the congestion order at low capacity -- OR it is not, in which case the age-first gain is
freshness, not decision depth.  Which holds is the result.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, sys, time
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
from dataclasses import replace

SOURCES = ['scripts/MARL_e3_decision_depth_probe_v3.py', 'scripts/MARL_e3_decision_depth_probe_v2.py', 'scripts/MARL_e3_theory_probe.py', 'models/marl_relay_v2.py',
           'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py',
           'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py']
EPS = (0.0, 0.25, 1.0)
ORDERS = ('stream', 'reverse', 'random')


def strip(view, heard):
    return replace(view, cache=(), never_heard=tuple(j for j in view.neighbours if j not in set(heard)))


def depths_for_receiver(env, i, teacher, raw, mask, orders, rng_perm, base):
    N = list(env.neighbours[i])
    seqs = {}
    for o in orders:
        seqs[o] = [j for j in orders[o] if j in N]
    subsets = [()] + [(j,) for j in N] + list(itertools.combinations(N, 2))
    heard_lists = []
    for o in ORDERS:
        for k in range(len(N) + 1):
            heard_lists.append(tuple(seqs[o][:k]))
    heard_lists += subsets
    uniq = list(dict.fromkeys(heard_lists))
    idx = {h: n for n, h in enumerate(uniq)}
    if base == 'empty':
        X = np.stack([raw.encode(strip(env.counterfactual_view(i, list(h)), h), 'actual') for h in uniq])
    else:
        X = np.stack([raw.encode(env.counterfactual_view(i, list(h)), 'actual') for h in uniq])
    with torch.no_grad():
        L = teacher(torch.as_tensor(X), mask[i:i + 1].expand(X.shape[0], -1)).numpy()   # the mask row of receiver i
    full = L[idx[tuple(seqs['stream'])]]
    for o in ORDERS:                                   # the full view is order-independent: a self-check
        if np.abs(L[idx[tuple(seqs[o])]] - full).max() > 1e-5:
            raise AssertionError(f'full view depends on the order at receiver {i}')
    top = full.max()
    depth = np.zeros((len(ORDERS), len(EPS)), dtype=np.int16)
    minset = np.zeros(len(EPS), dtype=np.int16)
    for e, eps in enumerate(EPS):
        ok = lambda h: full[int(L[idx[h]].argmax())] >= top - eps - 1e-9
        for oi, o in enumerate(ORDERS):
            depth[oi, e] = next(k for k in range(len(N) + 1) if ok(tuple(seqs[o][:k])))
        best = 3
        for s in subsets:
            if ok(s):
                best = min(best, len(s))
        minset[e] = best
    eps_sub = 1
    okk = lambda h: full[int(L[idx[h]].argmax())] >= top - EPS[eps_sub] - 1e-9
    Ns = sorted(N)
    canon = [()] + [(j,) for j in Ns] + list(itertools.combinations(Ns, 2))
    sub_ok = np.zeros(37, dtype=bool)
    for n_, h in enumerate(canon[:37]):
        key = h if h in idx else tuple(sorted(h))
        if key not in idx:
            key = next(k for k in idx if tuple(sorted(k)) == tuple(sorted(h)))
        sub_ok[n_] = okk(key)
    nb = np.full(8, -1, dtype=np.int16); nb[:len(Ns)] = Ns[:8]
    return depth, minset, len(N), sub_ok, nb


def run(sc, seed, load, cks, rule, order, capacity, book):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], capacity)
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    mus = MusicDelivery(order); mus.mode = rule; m = env.n_agents; prev = None; q = 0.0; recs = []
    rng = np.random.default_rng(10_000 + 10 * seed + int(load))
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        stream = tuple(mus.last_order)
        orders = {'stream': stream, 'reverse': tuple(reversed(stream)), 'random': tuple(int(x) for x in rng.permutation(m))}
        per = [depths_for_receiver(env, i, teacher, raw, mask, orders, rng, 'cache') for i in range(m)]      # DIAGNOSTIC oracle
        per_e = [depths_for_receiver(env, i, teacher, raw, mask, orders, rng, 'empty') for i in range(m)]
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            X_relay = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                L_relay = pol.actor(torch.as_tensor(X_relay), pol.mask).numpy()
            acts = {i: int(a) for i, a in enumerate(L_relay.argmax(-1))}
            Kt = [int(env._k[i]) for i in range(m)]
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
        for i in range(m):
            recs.append((t, i, Kt[i], per[i][2], per[i][0], per[i][1], per_e[i][0], per_e[i][1], per_e[i][3], per_e[i][4]))
    return q, recs


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in (('relay', a.relay), ('teacher', a.teacher))}
    sc = Scenarios(out)
    parity = {r['episode']: r for r in json.loads(Path(a.parity).read_text()) if r['rule'] == a.rule} if a.parity else {}
    rows = []; allrec = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'; q, rr = run(sc, seed, load, cks, a.rule, a.order, a.capacity, book)
            if ep in parity and abs(parity[ep]['queue_sum'] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != evaluator row {parity[ep]["queue_sum"]}')
            rows.append(dict(episode=ep, queue_sum=q, parity_checked=ep in parity))
            allrec += [(seed, load) + r for r in rr]
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
    arr = {k: np.array([r[i] for r in allrec]) for i, k in enumerate(['seed', 'load', 't', 'recv', 'K', 'nN'])}
    arr['depth'] = np.stack([r[6] for r in allrec]); arr['minset'] = np.stack([r[7] for r in allrec])
    arr['depth_empty'] = np.stack([r[8] for r in allrec]); arr['minset_empty'] = np.stack([r[9] for r in allrec])
    arr['sub_ok'] = np.stack([r[10] for r in allrec]); arr['nbrs'] = np.stack([r[11] for r in allrec])
    np.savez_compressed(out / 'depth.npz', **arr); (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', eps=EPS, orders=ORDERS, bases=('cache', 'empty'),
                                                       parity_episodes=sum(r['parity_checked'] for r in rows), args=vars(a),
                                                       source_hashes=h0, records=len(allrec), seconds=time.perf_counter() - t0),
                                                  indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True)
    p.add_argument('--order', choices=['prefix', 'agefirst', 'bass'], default='agefirst'); p.add_argument('--rule', default='prefix')
    p.add_argument('--capacity', default='iid'); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 933))); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--parity', default=None); p.add_argument('--out', required=True)
    main(p.parse_args())
