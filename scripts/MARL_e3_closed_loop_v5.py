#!/usr/bin/env python3
"""E3 closed loop v5 (28/09 independent recheck P0): v4 plus
  * STRICT tau parsing: finite float, the exact strings '+inf' / '-inf', or legacy None (v1/v2 only, = -inf); NaN,
    bare 'inf', other strings and a None in a v3+ checkpoint (tau_format 'v3 strings') are REJECTED;
  * --selftest: unit tests of the decision rule (exact tie at tau, +inf with huge scores, no feasible edit, -inf with
    all-negative scores, argmax ties) before any episode;
  * per-step BYTE PARITY: the env's accounted bytes of the submitted profile must equal the bytes the scheduler scored
    (profile_cost of the chosen candidate), and the charged total adds exactly the bid bytes.
v4 is unchanged (its smoke run is an artifact).

v4 description follows.
E3 closed loop v4 (28/09 self-audit L-15): v3 plus every DEPLOYABLE selector version.

Why: v1-v3 parse tau as `-inf if tau is None else tau`; selectors v3+ store tau as the strings '+inf' / '-inf' or a
float, so a v3+ checkpoint could not be deployed (crash, or a float compared with a string).  v4 adds:
  * tau parsing: None (v1/v2) -> -inf, '-inf' -> -inf, '+inf' -> +inf (always keep the prefix), float as is;
  * --qbid selectors (v4, same-byte queue bid): each receiver's own total waiting from its OWN pre-transmission view,
    min(255, round(sum lane_waiting)), exactly as MARL_e3_queue_side.py; 10 B charged every step inside the cap;
  * --resp-multi selectors (v5): the multi-class head on the same legal inputs, features appended as in training;
  * selectors from several directories (--selectors DIR ...; method names must be unique);
  * priv_joint selectors are REFUSED (privileged diagnostic, never deployable).
Features are built in the trainer's order (base -> qbid -> binary head -> multi-class head) by runtime_scores().
Self-checks before any episode (abort on failure), on the actor's stored development labels (<actor dir>/labels_dev):
  (1) runtime_scores() equals MARL_e3_selector_diag_v2.predictions() (the trainer-verified path) to 1e-5;
  (2) with the training cap (+84) the chosen index equals the trainer's saved dev_chosen (v3+ jobs).
Everything else as v3: legal inputs only, no_oracle_access around every scheduler call, access invariants every step.
"""
from __future__ import annotations
import argparse, glob, gzip, hashlib, json, os, sys, time
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
from scripts.MARL_e3_selector_train import Net, features, choose, load, BID_BYTES
from scripts.MARL_e3_selector_diag_v2 import predictions
from scripts.MARL_hetero_panel_collect import capacity_trace
from models.marl_e3_response import resp_features, RespNet

SOURCES = ['scripts/MARL_e3_closed_loop_v5.py', 'scripts/MARL_e3_closed_loop_v4.py', 'scripts/MARL_e3_selector_diag_v2.py', 'scripts/MARL_e3_selector_train_v5.py',
           'models/marl_e3_response.py', 'scripts/MARL_hetero_panel_collect.py', 'scripts/MARL_e3_selector_train.py',
           'scripts/MARL_e3_continuation_labels.py', 'scripts/MARL_e3_actor_train.py', 'models/marl_comm_actor.py',
           'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py']


def parse_tau(t, fmt=None):
    if t is None:
        if fmt == 'v3 strings':
            raise ValueError('tau None in a v3+ checkpoint: ambiguous (v3+ writes explicit strings)')
        return -np.inf                                    # legacy v1/v2 meaning
    if isinstance(t, str):
        if t == '+inf':
            return np.inf
        if t == '-inf':
            return -np.inf
        raise ValueError(f'unknown tau string {t!r}')
    t = float(t)
    if not np.isfinite(t):
        raise ValueError(f'non-finite numeric tau {t!r} (infinities must be the explicit strings)')
    return t


def selftest():
    """Decision-rule unit tests (no simulator)."""
    f = np.array([True, True, True]); al = np.ones(3, bool)
    assert choose(np.array([0.0, 2.0, 1.0]), f, al, 2.0) == 0, 'exact tie at tau must keep the prefix (strict >)'
    assert choose(np.array([0.0, 2.0, 1.0]), f, al, 1.999) == 1
    assert choose(np.array([0.0, 1e9, 5.0]), f, al, parse_tau('+inf')) == 0, '+inf must always keep the prefix'
    assert choose(np.array([0.0, 9.0, 5.0]), np.array([True, False, False]), al, parse_tau('-inf')) == 0, 'no feasible edit -> prefix'
    assert choose(np.array([0.0, -3.0, -1.0]), f, al, parse_tau('-inf')) == 0, '-inf with negative anchored scores keeps the argmax = prefix'
    assert choose(np.array([0.0, 4.0, 4.0]), f, al, 0.0) == 1, 'argmax ties resolve to the lowest index'
    assert choose(np.array([0.0, 4.0, 3.0]), f, np.array([True, False, True]), 0.0) == 2, 'R1 mask respected'
    for bad in (float('nan'), 'inf', 'Infinity', 'nan', float('inf')):
        try:
            parse_tau(bad); raise AssertionError(f'parse_tau accepted {bad!r}')
        except ValueError:
            pass
    try:
        parse_tau(None, 'v3 strings'); raise AssertionError('parse_tau accepted None in a v3+ checkpoint')
    except ValueError:
        pass
    assert parse_tau(None) == -np.inf, 'legacy None must mean -inf'
    assert parse_tau(1.25) == 1.25
    print('selftest PASS (7 decision cases, 6 rejected tau forms)', flush=True)


def bid_bytes(meta):
    return BID_BYTES if (meta['bid'] or meta.get('qbid')) else 0


def runtime_scores(meta, st):
    """Anchored scores from LEGAL runtime data only (no 'cont'/'joint' read), in the trainer's feature order."""
    c, D, _, r1 = features(st, meta['bid'], meta['gap_thr'])
    if meta.get('qbid'):
        c = np.concatenate([c, np.asarray(st['qbid'], np.float32) / 50.0]).astype(np.float32)
    if meta.get('resp'):
        X = resp_features(st, meta['bid'], meta['gap_thr'])
        with torch.no_grad():
            pr = torch.sigmoid(meta['_head'](torch.as_tensor((X - meta['head']['mu']) / meta['head']['sd']))).numpy()
        D = np.concatenate([D, pr, pr.sum(1, keepdims=True)], 1).astype(np.float32)
    if meta.get('resp_multi'):
        from scripts.MARL_e3_selector_train_v5 import multi_features
        hm = meta['head_multi']; pm, tv = multi_features(meta['_multi'], hm['mu'], hm['sd'], resp_features(st, meta['bid'], meta['gap_thr'])); C_ = pm.shape[0]
        c = np.concatenate([c, pm[0].ravel()]).astype(np.float32)
        D = np.concatenate([D, pm.reshape(C_, -1), tv, tv.sum(1, keepdims=True)], 1).astype(np.float32)
    with torch.no_grad():
        p = meta['_net'](torch.as_tensor((c - meta['cm']) / meta['cs'])[None], torch.as_tensor(D)).numpy() * meta['ys']
    return p - p[0], r1


def load_selector(f, actor):
    meta = torch.load(f, weights_only=False); job = json.loads(Path(f.replace('model_', 'job_').replace('.pt', '.json')).read_text())
    if Path(job['actor_ckpt']).resolve() != Path(actor).resolve():
        raise SystemExit(f'{f}: selector trained on labels of a different actor ({job["actor_ckpt"]})')
    if meta.get('priv_joint'):
        raise SystemExit(f'{f}: privileged diagnostic evaluator, never deployable')
    net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); meta['_net'] = net
    if meta.get('resp'):
        hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval(); meta['_head'] = hn
    if meta.get('resp_multi'):
        from scripts.MARL_e3_selector_train_v5 import RespMulti
        nm = RespMulti(); nm.load_state_dict(meta['head_multi']['state']); nm.eval(); meta['_multi'] = nm
    return meta, job


def self_check(sels, actor):
    D = Path(actor).parent / 'labels_dev'; S, _ = load([D]); qd = D.parent / f'qbid_{D.name}'
    if (qd / 'manifest.json').exists():
        Q = {(r['episode_id'], r['t']): r['qbid'] for r in map(json.loads, gzip.open(qd / 'qbid.jsonl.gz', 'rt'))}
        for st in S:
            st['qbid'] = Q.get((st['episode_id'], st['t']))
    rep = {}
    for name, (meta, job) in sels.items():
        if meta.get('qbid') and S[0].get('qbid') is None:
            raise SystemExit(f'SELF-CHECK FAIL: {name} needs queue side data for {D}')
        worst = 0.0; ch = []
        for st in S:
            an, r1 = runtime_scores(meta, st)
            ref, _, feas_ref, _ = predictions(meta, meta['_net'], meta.get('_head'), st)
            worst = max(worst, float(np.max(np.abs(an - ref))))
            feas = np.array([cc['bytes'] <= st['b0'] + 84 - bid_bytes(meta) for cc in st['cands']])
            if not np.array_equal(feas, feas_ref):
                raise SystemExit(f'SELF-CHECK FAIL: {name}: feasibility differs from the trainer path')
            ch.append(choose(an, feas, np.ones_like(r1), parse_tau(meta['tau']['direct'], meta.get('tau_format'))))
        if worst > 1e-5:
            raise SystemExit(f'SELF-CHECK FAIL: {name}: runtime scores differ from the trainer path by {worst}')
        saved = job['results']['direct'].get('dev_chosen')
        if saved is not None and saved != ch:
            raise SystemExit(f'SELF-CHECK FAIL: {name}: chosen indices differ from the trainer\'s dev_chosen')
        rep[name] = dict(max_score_diff=worst, chosen_checked=saved is not None, states=len(S))
        print(f'self-check {name}: max |runtime - trainer path| {worst:.2e}; chosen indices ' + ('== trainer' if saved is not None else 'not saved (v1/v2 job)'), flush=True)
    return rep


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
            qb = None
            if sel is not None and sel.get('qbid'):
                qb = [int(min(255, round(float(np.asarray(env._build_view(i).lane_waiting).sum())))) for i in range(m)]   # own view, as queue_side
        if sel is not None:
            meta = sel; bid = None
            if meta['bid']:
                pre = {i: env._build_view(i) for i in range(m)}                   # receiver side, own view
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
                feas = np.array([cc['bytes'] <= b0 + CAP - bid_b for cc in st['cands']])     # the RUN's cap
                j = choose(an, feas, r1 if policy == 'R1' else np.ones_like(r1), parse_tau(meta['tau'][policy], meta.get('tau_format')))
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
    return dict(episode=f'seed{seed}_load{load:g}', method=method, cap=CAP, capacity=capacity, queue_sum=float(sum(r['queue'] for r in env.step_records)),
                finished=int(env.step_records[-1]['finished']), bytes=int(total), edits=edits, summary=env.episode_summary())


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
                r = episode(sc, seed, load, meth, pol_ck, sels[meth][0] if meth in sels else None, a.policy, a.cap, a.capacity); rows.append(r)
                print(f'[{time.perf_counter() - t0:.0f}s] {r["episode"]} {meth}: queue_sum {r["queue_sum"]:.0f} finished {r["finished"]} '
                      f'bytes {r["bytes"]} edits {r["edits"]}', flush=True)
                tmp = out / '.rows.json'; tmp.write_text(json.dumps(rows, default=float)); os.replace(tmp, out / 'rows.json')
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', self_check_detail=chk, args=vars(a), source_hashes=h0,
                                                       seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor', required=True); p.add_argument('--selectors', nargs='+', required=True); p.add_argument('--names', nargs='+', required=True)
    p.add_argument('--out', required=True); p.add_argument('--traffic-seeds', type=int, nargs='+', required=True)
    p.add_argument('--policy', choices=['direct', 'R1'], default='direct'); p.add_argument('--mp2', action='store_true')
    p.add_argument('--cap', type=int, default=84); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--capacity', choices=['iid', 'fixed', 'bursty', 'low', 'high'], default='iid')
    p.add_argument('--selftest-only', action='store_true')
    a_ = p.parse_args()
    selftest() if a_.selftest_only else main(a_)
