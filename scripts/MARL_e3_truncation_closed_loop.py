#!/usr/bin/env python3
"""Direction (b), LEGAL closed loop (29/09): send less than the prefix, and compare decision-aware truncation with blind
truncation at the same bytes.  Same panel, scenario factory, capacity trace and actor as MARL_e3_closed_loop_v5.

Every rule keeps the committed cached-queue order and sends a PREFIX of the prefix stream (the first L of its L0
packets); receiver i decodes P_i restricted to that stream (a voluntary smaller capacity).  Bytes: the shared
models.marl_hetero_selector.profile_cost, plus the declared bid bytes of rules that use a bid.
  prefix        L = L0 (the reference; parity against the saved closed-loop prefix row);
  blind_<f>     L = round((1 - f) L0): the lowest-priority packets dropped, no information used (the same-byte baseline
                curve; f in --fracs);
  proxy         RECEIVER-SIDE, legal: after the reveal (order and K are public), receiver i evaluates its own actor on its
                OWN pre-transmission view with, for every candidate L, the senders it would decode marked fresh (age 0)
                and carrying their CACHED content (the fresh content is unknown to it; a never-heard sender gets a zero
                payload), the others as in its cache.  It reports L_i = the smallest L such that its proxy action is
                the same for every L' in [L, L0] (one byte; the declared bid charge, BID_BYTES = 10 per step, is added).
                The scheduler sends L = max_i L_i.  It checks the CURRENT decision only (with a proxy); it ignores the
                future cache (see LeanMarlDecisionCertificateV1.current_step_invariance_insufficient);
  tmc_<d>       SENDER-SIDE, TMC-style (Zhang, Lin, Zhang, NeurIPS 2020): sender j of the prefix stream omits its packet
                when its phase is unchanged and every per-approach vehicle and waiting count differs by at most d from
                its LAST BROADCAST packet (the public scheduler cache); the stream is described by the shared cost
                function (patched or explicit), receivers decode P_i minus the omitted senders (d in --tmc).
With --oracle-check, at every proxy step a clone of the simulator (diagnostic only, restored before acting) records
whether the TRUE actions under the proxy's L equal the true actions under L0, and the smallest exactly-safe L.
Recorded per episode: waiting (sum of queues), bytes, first step whose joint action differs from the prefix run's.
"""
from __future__ import annotations
import argparse, dataclasses, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import CacheEntry, MessagePayload
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets, stream_length
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_selector_train import BID_BYTES
from scripts.MARL_e3_zero_loss_truncation import make, play

SOURCES = ['scripts/MARL_e3_truncation_closed_loop.py', 'scripts/MARL_e3_zero_loss_truncation.py', 'scripts/MARL_e3_continuation_labels.py',
           'scripts/MARL_hetero_target_diag.py', 'scripts/MARL_e3_actor_train.py', 'models/marl_hetero_selector.py', 'models/marl_comm_actor.py',
           'envs/external/cityflow_hetero_mirror.py', 'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py']


def proxy_view(v, S, t):
    """Receiver's OWN pre-transmission view with the senders in S marked delivered now, carrying their cached content."""
    cached = {e.sender: e for e in v.cache}; inbox = []
    for j in sorted(S):
        if j in cached:
            e = cached[j]; inbox.append(CacheEntry(j, e.payload, e.measured_at, 0.0, t))
        else:
            p = MessagePayload(int(j), int(round(v.sim_time)), 0, 0, (0, 0, 0, 0), (0, 0, 0, 0)); inbox.append(CacheEntry(j, p, p.measured_at, 0.0, t))
    return dataclasses.replace(v, inbox=tuple(inbox), cache=tuple(e for e in v.cache if e.sender not in S),
                               never_heard=tuple(j for j in v.never_heard if j not in S))


def proxy_L(env, pol, order, P, L0, t):
    """Each receiver's reported L_i from its own view; the scheduler's L = max_i L_i."""
    m = env.n_agents; Ls = []
    for i in range(m):
        v = env._build_view(i)
        Xs = [pol.adapter.encode(proxy_view(v, {j for j in P[i] if j in set(order[:L])}, t), 'actual') for L in range(L0 + 1)]
        with torch.no_grad():
            a = pol.actor(torch.as_tensor(np.stack(Xs)), pol.mask[i].expand(len(Xs), -1)).argmax(-1).numpy()
        Li = L0
        while Li > 0 and a[Li - 1] == a[L0]:
            Li -= 1
        Ls.append(int(Li))
    return max(Ls), Ls


def episode(sc, seed, load, ck, capacity, rule, A_ref, oracle_check):
    env, pol = make(sc, seed, load, ck, capacity); m = env.n_agents; total = 0; qs = []; first_div = None; checks = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            order, K = grant(env)
            P = prefix_sets(order, K); L0 = stream_length(order, P); extra = 0; Lrep = None
            if rule == 'prefix':
                L = L0
            elif rule.startswith('blind_'):
                L = int(np.floor((1.0 - float(rule.split('_')[1])) * L0 + 0.5))
            elif rule == 'proxy':
                L, Lrep = proxy_L(env, pol, order, P, L0, t); extra = BID_BYTES
            elif rule.startswith('tmc_'):
                L = None; d = float(rule.split('_')[1]); omit = set()
                for j in order[:L0]:
                    last = env._scheduler_cache.get(j); cur = env._summary(j)        # sender j's own summary (local to j)
                    if last is not None and cur.phase == last.phase and max(abs(x - y) for x, y in zip(cur.vehicles + cur.waiting, last.vehicles + last.waiting)) <= d:
                        omit.add(j)
            else:
                raise ValueError(rule)
        if rule.startswith('tmc_'):
            sets = [frozenset(j for j in P[i] if j not in omit) for i in range(m)]
        else:
            sets = [frozenset(j for j in P[i] if j in set(order[:L])) for i in range(m)]
        if oracle_check and rule == 'proxy':
            snap = env.clone_state()
            full = play(env, pol, P)[1]; env.restore_state(snap)
            mine = play(env, pol, sets)[1]; env.restore_state(snap)
            Lx = L0
            for L_ in range(L0):
                a_ = play(env, pol, [frozenset(j for j in P[i] if j in set(order[:L_])) for i in range(m)])[1]; env.restore_state(snap)
                if a_ == full:
                    Lx = L_; break
            checks.append(dict(t=t, L0=L0, L=L, L_exact=Lx, safe=(mine == full), L_reports=Lrep))
        _, acts = play(env, pol, sets); _, _, rec = env.step(acts)
        if first_div is None and [acts[i] for i in range(m)] != A_ref[t]:
            first_div = t
        total += rec['accounted_bytes'] + extra; qs.append(float(rec['queue']))
    return dict(queue_sum=float(sum(qs)), bytes=int(total), first_divergence=first_div, checks=checks, summary=env.episode_summary())


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    ck = torch.load(Path(a.actor), weights_only=False); sc = Scenarios(out)
    parity = {r['episode']: r for r in json.loads(Path(a.parity_rows).read_text()) if r['method'] == 'prefix'} if a.parity_rows else {}
    rules = ['prefix'] + [f'blind_{f}' for f in a.fracs] + (['proxy'] if a.proxy else []) + [f'tmc_{d:g}' for d in a.tmc]
    rows = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'
            env, pol = make(sc, seed, load, ck, a.capacity); A_ref = []
            for t in range(N_DEC):
                with no_oracle_access(env):
                    order, K = grant(env)
                _, acts = play(env, pol, prefix_sets(order, K)); env.step(acts); A_ref.append([acts[i] for i in range(env.n_agents)])
            for rule in rules:
                r = episode(sc, seed, load, ck, a.capacity, rule, A_ref, a.oracle_check)
                if rule == 'prefix':
                    if r['first_divergence'] is not None:
                        raise SystemExit(f'SELF-CHECK FAIL: {ep}: the prefix rule does not reproduce the reference actions')
                    if ep in parity and (abs(parity[ep]['queue_sum'] - r['queue_sum']) > 1e-6 or parity[ep]['bytes'] != r['bytes']):
                        raise SystemExit(f'SELF-CHECK FAIL: {ep}: prefix {r["queue_sum"]}/{r["bytes"]} != saved row {parity[ep]["queue_sum"]}/{parity[ep]["bytes"]}')
                rows.append(dict(episode=ep, traffic_seed=seed, headway=load, rule=rule, **r))
                extra = ''
                if r['checks']:
                    extra = f" | proxy safe {np.mean([c['safe'] for c in r['checks']]):.2f}, L {np.mean([c['L'] for c in r['checks']]):.2f} vs exact {np.mean([c['L_exact'] for c in r['checks']]):.2f} of L0 {np.mean([c['L0'] for c in r['checks']]):.2f}"
                print(f'[{time.perf_counter() - t0:.0f}s] {ep} {rule}: waiting {r["queue_sum"]:.0f} bytes {r["bytes"]} first divergence {r["first_divergence"]}{extra}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), rules=rules, episodes=len(rows), source_hashes=h0,
                                                       evidence_class='closed loop, legal rules (oracle-check columns are diagnostics)',
                                                       seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor', required=True); p.add_argument('--out', required=True)
    p.add_argument('--traffic-seeds', type=int, nargs='+', required=True); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--capacity', default='iid'); p.add_argument('--fracs', type=float, nargs='+', default=[0.1, 0.2, 0.3, 0.4, 0.5])
    p.add_argument('--tmc', type=float, nargs='*', default=[]); p.add_argument('--proxy', action='store_true'); p.add_argument('--oracle-check', action='store_true'); p.add_argument('--parity-rows', default='')
    main(p.parse_args())
