#!/usr/bin/env python3
"""E3 closed loop v6 (28/09 23:35, PROTOCOL_E3_CLOSED_LOOP_GUARD_20260928.md; ledger L-65): v5 plus ONE declared
deployment rule, the SUPPORT GUARD, and a per-step decision log.

Why: every E3 selector normalises its context by the TRAIN mean and std + 1e-6; several binary 'packet present' flags
are constant on train states (t >= 7), so at t = 0..3 (empty caches) the normalised input reaches 1e6 and a selector with
a small tau edits on scores computed far outside its training support.  v5 is unchanged; old checkpoints are unchanged
(their normalisers are NOT patched): the guard is a different deployment rule, reported as such.

--guard support: at a step, keep the committed prefix instead of the selector's choice if
  (a) t < --t-min (the earliest labelled snapshot of the selector's training labels; 7 for the original rounds), or
  (b) the largest |normalised input| of the critic context, or of the response / multi-class head input, exceeds
      --z-max (50; the largest value on the saved DEV states of the audited checkpoints is 27.7).
Bids are still sent and charged at a guarded step.  --guard none reproduces v5 (checked by --parity-smoke).
Each selector row adds 'steps': [t, guarded, reason, max |z|, edited] per decision, and 'guard' settings.
Everything else (tau parsing, selftest, train/runtime score and choice parity, per-step byte parity, no oracle access)
is v5's code path, imported unchanged.
"""
from __future__ import annotations
import argparse, glob, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_e3_closed_loop_v5 as v5
from scripts.MARL_e3_closed_loop_v5 import (no_oracle_access, prefix_sets, profile_cost, mp2_action, N_DEC, candidates, grant,
                                            Scenarios, Policy, features, choose, capacity_trace, resp_features,
                                            parse_tau, selftest, bid_bytes, runtime_scores, load_selector, self_check)

SOURCES = ['scripts/MARL_e3_closed_loop_v6.py'] + v5.SOURCES


def support_z(meta, st):
    """Largest |normalised input| of the critic context and of the head input(s), in the trainer's feature order."""
    c, _, _, _ = features(st, meta['bid'], meta['gap_thr'])
    if meta.get('qbid'):
        c = np.concatenate([c, np.asarray(st['qbid'], np.float32) / 50.0]).astype(np.float32)
    zs = []
    if meta.get('resp'):
        X = resp_features(st, meta['bid'], meta['gap_thr']); zs.append(float(np.abs((X - meta['head']['mu']) / meta['head']['sd']).max()))
    if meta.get('resp_multi'):
        hm = meta['head_multi']; X = resp_features(st, meta['bid'], meta['gap_thr']); zs.append(float(np.abs((X - hm['mu']) / hm['sd']).max()))
        from scripts.MARL_e3_selector_train_v5 import multi_features
        pm, _ = multi_features(meta['_multi'], hm['mu'], hm['sd'], X); c = np.concatenate([c, pm[0].ravel()]).astype(np.float32)
    zc = float(np.abs((c - meta['cm']) / meta['cs']).max())
    return max([zc] + zs)


def episode(sc, seed, load, method, pol_ck, sel, policy, CAP, capacity, guard, t_min, z_max):
    env, topo, down, onward = sc.env(seed, load); m = env.n_agents
    tr = capacity_trace(capacity, N_DEC, m, 5000 + 10 * seed + int(load))
    if tr is not None:
        env._trace = tr
    pol = Policy(pol_ck, topo, env.action_interval) if method != 'mp2' else None
    rngc = np.random.default_rng(80000 + 10 * seed + int(load)); total = 0; edits = 0; steps = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            ctx = env.scheduler_context(); z = ctx.features(); mir = env.mirror_features()
            order, K = grant(env); P = prefix_sets(order, K); sets = [set(s) for s in P]
            b0 = profile_cost(order, K, sets)[0]; cap = None; bid_b = 0
            qb = None
            if sel is not None and sel.get('qbid'):
                qb = [int(min(255, round(float(np.asarray(env._build_view(i).lane_waiting).sum())))) for i in range(m)]
        if sel is not None:
            meta = sel; bid = None
            if meta['bid']:
                pre = {i: env._build_view(i) for i in range(m)}
                lg = pol.logits(pre); bid = []
                for i in range(m):
                    o = np.argsort(-lg[i]); bid.append(dict(p1=int(o[0]), p2=int(o[1]), gap=float(lg[i][o[0]] - lg[i][o[1]])))
            bid_b = bid_bytes(meta)
            with no_oracle_access(env):
                Pt = tuple(frozenset(s) for s in P)
                cands = [Pt] + [tuple(frozenset(s) for s in c) for c in candidates(order, K, m, rngc) if tuple(frozenset(s) for s in c) != Pt]
                st = dict(m=m, z=[float(x) for x in z], K=K, mirror=[float(x) for x in mir], bid=bid, b0=int(b0), qbid=qb,
                          cands=[dict(sets=[sorted(s) for s in c], bytes=int(profile_cost(order, K, [set(s) for s in c])[0])) for c in cands])
                an, r1 = runtime_scores(meta, st)
                feas = np.array([cc['bytes'] <= b0 + CAP - bid_b for cc in st['cands']])
                j = choose(an, feas, r1 if policy == 'R1' else np.ones_like(r1), parse_tau(meta['tau'][policy], meta.get('tau_format')))
                zmax = support_z(meta, st); reason = ''
                if guard == 'support':
                    if t < t_min:
                        reason = 't<t_min'
                    elif zmax > z_max:
                        reason = 'z>z_max'
                guarded = bool(reason)
                steps.append([t, guarded, reason, round(zmax, 3), int(j != 0 and not guarded), int(j != 0)])
                if guarded:
                    j = 0
                sets = [set(s) for s in cands[j]]; edits += int(j != 0); cap = b0 + CAP - bid_b; scored_bytes = st['cands'][j]['bytes']
        with no_oracle_access(env):
            env.submit_profile(sets, R=(1 if policy == 'R1' and sel is not None else (0 if sel is None else None)), cap=cap)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            acts = {i: mp2_action(v, topo[i], down, onward) for i, v in views.items()} if method == 'mp2' else pol.act(views)
            _, _, rec = env.step(acts)
        want = scored_bytes if sel is not None else b0
        if rec['accounted_bytes'] != want:
            raise AssertionError(f'BYTE PARITY FAIL at t{t}: env accounted {rec["accounted_bytes"]}, scheduler scored {want}')
        total += rec['accounted_bytes'] + bid_b
    row = dict(episode=f'seed{seed}_load{load:g}', method=method, cap=CAP, capacity=capacity, queue_sum=float(sum(r['queue'] for r in env.step_records)),
               finished=int(env.step_records[-1]['finished']), bytes=int(total), edits=edits, summary=env.episode_summary())
    if sel is not None:
        row.update(steps=steps, steps_fields=['t', 'guarded', 'reason', 'max_abs_z', 'edited', 'selector_wanted_edit'],
                   guard=dict(mode=guard, t_min=t_min, z_max=z_max))
    return row


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    pol_ck = torch.load(Path(a.actor), weights_only=False); sc = Scenarios(out)
    sels = {}
    for name in a.names:
        files = [f for d in a.selectors for f in sorted(glob.glob(str(Path(d) / f'model_{name}_s*.pt')))]
        if not files:
            raise SystemExit(f'no selector {name} in {a.selectors}')
        for f in files:
            meta, job = load_selector(f, a.actor); key = f'{name}/s{job["seed"]}'
            if key in sels:
                raise SystemExit(f'{key}: found in more than one selector directory')
            sels[key] = (meta, job)
    selftest(); chk = self_check(sels, a.actor)
    methods = ['prefix'] + (['mp2'] if a.mp2 else []) + list(sels)
    rows = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.headways:
            for meth in methods:
                r = episode(sc, seed, load, meth, pol_ck, sels[meth][0] if meth in sels else None, a.policy, a.cap, a.capacity, a.guard, a.t_min, a.z_max)
                rows.append(r)
                g = sum(s[1] for s in r.get('steps', []))
                print(f'[{time.perf_counter() - t0:.0f}s] {r["episode"]} {meth}: queue_sum {r["queue_sum"]:.0f} finished {r["finished"]} '
                      f'bytes {r["bytes"]} edits {r["edits"]} guarded {g}', flush=True)
                tmp = out / '.rows.json'; tmp.write_text(json.dumps(rows, default=float)); os.replace(tmp, out / 'rows.json')
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', self_check_detail=chk, args=vars(a), source_hashes=h0,
                                                       seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor', required=True); p.add_argument('--selectors', nargs='+', required=True); p.add_argument('--names', nargs='+', required=True)
    p.add_argument('--out', required=True); p.add_argument('--traffic-seeds', type=int, nargs='+', required=True)
    p.add_argument('--policy', choices=['direct', 'R1'], default='direct'); p.add_argument('--mp2', action='store_true')
    p.add_argument('--cap', type=int, default=84); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--capacity', choices=['iid', 'fixed', 'bursty', 'low', 'high'], default='iid')
    p.add_argument('--guard', choices=['none', 'support'], required=True); p.add_argument('--t-min', type=int, default=7)
    p.add_argument('--z-max', type=float, default=50.0)
    main(p.parse_args())
