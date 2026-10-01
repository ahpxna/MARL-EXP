#!/usr/bin/env python3
"""E3 closed loop v3: v2 plus selectors with a RESPONSE HEAD (MARL_e3_selector_train_v2.py).  The head is
evaluated at runtime on the same LEGAL inputs as in training (bid if any, mirror, z, public grid topology) and its
change probabilities are appended to the candidate features exactly as in training.  v2 is unchanged.

v2 description follows.
E3 closed loop v2: MARL_e3_closed_loop.py plus --cap (total byte cap over the prefix bytes, for a multi-budget
frontier), --headways and --capacity (a declared distribution shift: iid | fixed | bursty | low | high, the traces of
MARL_hetero_panel_collect.capacity_trace).  The selectors are the SAME frozen models (trained with feasibility at
+84 B); only the cap applied at deployment changes, which is declared.  v1 is unchanged.

Original v1 description follows.
E3 closed loop: FROZEN learned actor + frozen selectors (MARL_e3_selector_train.py), fresh traffic seeds.

Methods on the same episodes (paired):
  prefix          the frozen actor with the committed cached-queue prefix (R = 0);
  mp2             reference: the frozen MP2 actor with the same prefix (a different actor; label only);
  <name>/s<k>     the frozen actor with selector <name> (init seed k), policy direct or R1, total cap
                  +84 B over the prefix bytes; a bid selector pays 10 B at EVERY step inside the cap.
Per step: context, committed order, capacity reveal; receivers compute the bid from their OWN
pre-transmission view (the actor's top-2 phases and logit gap); candidates (B1 family, seeded);
scheduler features from LEGAL data only (z, K, mirror, bid) through the trainer's features(); anchored
score, tau, cap; submit, transmit, the actor acts.  Every call except the receiver-side bid runs inside
no_oracle_access, and every step passes the access invariants.  Rows follow the closed-loop format,
so MARL_hetero_closed_loop_report.py and MARL_make_fig3_v4.py read them unchanged.
"""
from __future__ import annotations
import argparse, glob, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets, profile_cost
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC, candidates
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_continuation_labels import Policy
from scripts.MARL_e3_selector_train import Net, features, choose, BID_BYTES
from scripts.MARL_hetero_panel_collect import capacity_trace
from models.marl_e3_response import resp_features, RespNet

SOURCES = ['scripts/MARL_e3_closed_loop_v3.py', 'scripts/MARL_e3_closed_loop_v2.py', 'scripts/MARL_e3_selector_train_v2.py', 'models/marl_e3_response.py', 'scripts/MARL_hetero_panel_collect.py', 'scripts/MARL_e3_selector_train.py', 'scripts/MARL_e3_continuation_labels.py',
           'scripts/MARL_e3_actor_train.py', 'models/marl_comm_actor.py', 'envs/external/cityflow_hetero.py',
           'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py']


def episode(sc, seed, load, method, pol_ck, sel, policy, CAP=84, capacity='iid'):
    env, topo, down, onward = sc.env(seed, load); m = env.n_agents
    tr = capacity_trace(capacity, N_DEC, m, 5000 + 10 * seed + int(load))
    if tr is not None:
        env._trace = tr
    pol = Policy(pol_ck, topo, env.action_interval) if method != 'mp2' else None
    rngc = np.random.default_rng(80000 + 10 * seed + int(load)); total = 0; edits = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            ctx = env.scheduler_context(); z = ctx.features(); mir = env.mirror_features()
            order, K = grant(env); P = prefix_sets(order, K); sets = [set(s) for s in P]
            b0 = profile_cost(order, K, sets)[0]; cap = None; bid_b = 0
        if sel is not None:
            net, meta = sel; bid = None
            if meta['bid']:
                pre = {i: env._build_view(i) for i in range(m)}                   # receiver side, own view
                lg = pol.logits(pre); bid = []
                for i in range(m):
                    o = np.argsort(-lg[i]); bid.append(dict(p1=int(o[0]), p2=int(o[1]), gap=float(lg[i][o[0]] - lg[i][o[1]])))
                bid_b = BID_BYTES
            with no_oracle_access(env):
                Pt = tuple(frozenset(s) for s in P)
                cands = [Pt] + [tuple(frozenset(s) for s in c) for c in candidates(order, K, m, rngc) if tuple(frozenset(s) for s in c) != Pt]
                st = dict(m=m, z=[float(x) for x in z], K=K, mirror=[float(x) for x in mir], bid=bid, b0=int(b0),
                          cands=[dict(sets=[sorted(s) for s in c], bytes=int(profile_cost(order, K, [set(s) for s in c])[0])) for c in cands])
                c, D, feas, r1 = features(st, meta['bid'], meta['gap_thr'])
                feas = np.array([cc['bytes'] <= b0 + CAP - bid_b for cc in st['cands']])     # the RUN's cap, not the training +84
                if meta.get('resp'):
                    hn = meta['_head']; X = resp_features(st, meta['bid'], meta['gap_thr'])
                    with torch.no_grad():
                        pr = torch.sigmoid(hn(torch.as_tensor((X - meta['head']['mu']) / meta['head']['sd']))).numpy()
                    D = np.concatenate([D, pr, pr.sum(1, keepdims=True)], 1).astype(np.float32)
                with torch.no_grad():
                    p = net(torch.as_tensor((c - meta['cm']) / meta['cs'])[None], torch.as_tensor(D)).numpy() * meta['ys']
                an = p - p[0]; tau = meta['tau'][policy]; tau = -np.inf if tau is None else tau
                j = choose(an, feas, r1 if policy == 'R1' else np.ones_like(r1), tau)
                sets = [set(s) for s in cands[j]]; edits += int(j != 0); cap = b0 + CAP - bid_b
        with no_oracle_access(env):
            env.submit_profile(sets, R=(1 if policy == 'R1' and sel is not None else (0 if sel is None else None)), cap=cap)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            acts = {i: mp2_action(v, topo[i], down, onward) for i, v in views.items()} if method == 'mp2' else pol.act(views)
            _, _, rec = env.step(acts)
        total += rec['accounted_bytes'] + bid_b
    return dict(episode=f'seed{seed}_load{load:g}', method=method, cap=CAP, capacity=capacity, queue_sum=float(sum(r['queue'] for r in env.step_records)),
                finished=int(env.step_records[-1]['finished']), bytes=int(total), edits=edits, summary=env.episode_summary())


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    pol_ck = torch.load(Path(a.actor), weights_only=False); sc = Scenarios(out)
    sels = {}
    for name in a.names:
        for f in sorted(glob.glob(str(Path(a.selectors) / f'model_{name}_s*.pt'))):
            meta = torch.load(f, weights_only=False); job = json.loads(Path(f.replace('model_', 'job_').replace('.pt', '.json')).read_text())
            if Path(job['actor_ckpt']).resolve() != Path(a.actor).resolve():
                raise SystemExit(f'{f}: selector trained on labels of a different actor ({job["actor_ckpt"]})')
            net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval()
            if meta.get('resp'):
                hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval(); meta['_head'] = hn
            sels[f'{name}/s{job["seed"]}'] = (net, meta)
    methods = ['prefix'] + (['mp2'] if a.mp2 else []) + list(sels)
    rows = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.headways:
            for meth in methods:
                r = episode(sc, seed, load, meth, pol_ck, sels.get(meth), a.policy, a.cap, a.capacity); rows.append(r)
                print(f'[{time.perf_counter() - t0:.0f}s] {r["episode"]} {meth}: queue_sum {r["queue_sum"]:.0f} finished {r["finished"]} '
                      f'bytes {r["bytes"]} edits {r["edits"]}', flush=True)
                tmp = out / '.rows.json'; tmp.write_text(json.dumps(rows, default=float)); os.replace(tmp, out / 'rows.json')
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor', required=True); p.add_argument('--selectors', required=True); p.add_argument('--names', nargs='+', required=True)
    p.add_argument('--out', required=True); p.add_argument('--traffic-seeds', type=int, nargs='+', required=True)
    p.add_argument('--policy', choices=['direct', 'R1'], default='direct'); p.add_argument('--mp2', action='store_true')
    p.add_argument('--cap', type=int, default=84); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--capacity', choices=['iid', 'fixed', 'bursty', 'low', 'high'], default='iid')
    main(p.parse_args())
