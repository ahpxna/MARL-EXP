#!/usr/bin/env python3
"""Direction (b), oracle diagnostic (29/09): how many bytes can the E3 prefix protocol drop while EVERY receiver's action
stays identical to the prefix trajectory, and how much does the FUTURE-cache check matter?  (oracle diagnostic: the
simulator is cloned to test candidate truncations; an upper bound for a certificate, not a deployable rule)

Reference R: the prefix run of MARL_e3_closed_loop_v5 (same scenario factory, capacity trace, actor), recording the joint
action a*_t, the queue and the accounted bytes of every step.
Diagnostic run D(H): at every step, after the capacity reveal, the scheduler may send LESS than the prefix:
  family 'tail'  : the stream truncated to its first L packets (L = 0 .. L0); receiver i decodes P_i restricted to that
                   stream (a voluntary smaller capacity K'_i = |P_i & order[:L]|); the committed order is unchanged;
  family 'greedy': whole packets removed from the stream one at a time (tail first, repeated while one passes);
                   receivers decode P_i minus the removed packets;
  '<family>_local': H = 0 only, and the target at t is the action the UNTRUNCATED prefix would give now in THIS run
                   (a current-decision-invariance rule that ignores the future cache; it may drift from R).
  Bytes of every profile are the shared models.marl_hetero_selector.profile_cost (min of patched / explicit).
A candidate is ACCEPTED iff, from a clone of the simulator at that step: the receivers' actions under it equal a*_t,
AND for the next H steps (H = 'end': the rest of the episode) the plain prefix rule, run from the resulting caches,
reproduces a*_{t+1..t+H}.  'tail' takes the smallest accepted L; 'greedy' removes packets while a removal is accepted.
H = 'end' makes D's trajectory identical to R by construction; H < end can diverge (the current-step-only check is H = 0).
Self-checks (abort): R reproduces the saved closed-loop prefix row (queue_sum and bytes) of --parity-rows if given;
the untruncated candidate is accepted at t = 0 of every D run; every D(end) run has R's queues at every step exactly.
Per step recorded (for a later legal learner): K, order, L0, the scheduler features z and mirror, the receivers' bids
(p1, p2, logit gap on the pre-transmission view), the current-step pass vector over all L, and the choices.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets, profile_cost, stream_length
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_continuation_labels import Policy
from scripts.MARL_hetero_panel_collect import capacity_trace

SOURCES = ['scripts/MARL_e3_zero_loss_truncation.py', 'scripts/MARL_e3_closed_loop_v5.py', 'scripts/MARL_e3_continuation_labels.py',
           'scripts/MARL_hetero_target_diag.py', 'scripts/MARL_e3_actor_train.py', 'models/marl_hetero_selector.py', 'models/marl_comm_actor.py',
           'envs/external/cityflow_hetero_mirror.py', 'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py']


def make(sc, seed, load, ck, capacity):
    env, topo, _, _ = sc.env(seed, load)
    tr = capacity_trace(capacity, N_DEC, env.n_agents, 5000 + 10 * seed + int(load))
    if tr is not None:
        env._trace = tr
    return env, Policy(ck, topo, env.action_interval)


def play(env, pol, sets):
    """Submit `sets` (|S_i| may be below the revealed K_i: a voluntary smaller capacity), transmit, act."""
    with no_oracle_access(env):
        env._k = {i: len(sets[i]) for i in range(env.n_agents)}
        env.submit_profile([set(s) for s in sets], R=None)
        views = env.transmit(); env.verify_mirror()
        bad = env.check_access_invariants(views)
        if bad:
            raise AssertionError(f'access invariant: {bad[:3]}')
        return views, pol.act(views)


def reference(sc, seed, load, ck, capacity):
    env, pol = make(sc, seed, load, ck, capacity); A, Q, B = [], [], []
    for t in range(N_DEC):
        with no_oracle_access(env):
            order, K = grant(env)
        _, acts = play(env, pol, prefix_sets(order, K)); _, _, rec = env.step(acts)
        A.append([acts[i] for i in range(env.n_agents)]); Q.append(float(rec['queue'])); B.append(int(rec['accounted_bytes']))
    return A, Q, B


def accepted(env, pol, sets, t, H, A):
    """From the current (cloned) state at step t, stage 'revise': does `sets` keep a*_t and, with the prefix rule
    afterwards, a*_{t+1..t+H}?  Returns (ok, steps simulated)."""
    m = env.n_agents
    _, acts = play(env, pol, sets)
    if [acts[i] for i in range(m)] != A[t]:
        return False, 0
    env.step(acts); n = 1
    last = N_DEC - 1 if H == 'end' else min(N_DEC - 1, t + H)
    for u in range(t + 1, last + 1):
        with no_oracle_access(env):
            o, k = grant(env)
        _, acts = play(env, pol, prefix_sets(o, k))
        if [acts[i] for i in range(m)] != A[u]:
            return False, n
        env.step(acts); n += 1
    return True, n


def run_D(sc, seed, load, ck, capacity, family, H, A, Q):
    env, pol = make(sc, seed, load, ck, capacity); m = env.n_agents; steps = []; sim = 0; diverged = None; Aref = A
    for t in range(N_DEC):
        with no_oracle_access(env):
            z = [round(float(x), 5) for x in env.scheduler_context().features()]; mir = [round(float(x), 5) for x in env.mirror_features()]
            order, K = grant(env)
        pre = {i: env._build_view(i) for i in range(m)}; lg = pol.logits(pre); bid = []
        for i in range(m):
            o_ = np.argsort(-lg[i]); bid.append(dict(p1=int(o_[0]), p2=int(o_[1]), gap=round(float(lg[i][o_[0]] - lg[i][o_[1]]), 4)))
        P = prefix_sets(order, K); L0 = stream_length(order, P); b0 = profile_cost(order, K, [set(s) for s in P])[0]
        snap = env.clone_state()
        tail = lambda L: [frozenset(j for j in P[i] if j in set(order[:L])) for i in range(m)]
        if family.endswith('_local'):                            # target = the untruncated prefix's actions NOW, in this run
            env.restore_state(snap); _, acts = play(env, pol, P); A = list(A); A[t] = [acts[i] for i in range(m)]
        pass0 = []
        for L in range(L0 + 1):                                  # current-step check for every L (cheap, for learners)
            env.restore_state(snap); pass0.append(bool(accepted(env, pol, tail(L), t, 0, A)[0]))
        if family.startswith('tail'):
            chosen = None
            for L in range(L0 + 1):
                env.restore_state(snap); ok, n = accepted(env, pol, tail(L), t, H, A); sim += n
                if ok:
                    chosen = tail(L); break
        else:
            chosen = [frozenset(s) for s in P]; removed = []
            env.restore_state(snap); ok, n = accepted(env, pol, chosen, t, H, A); sim += n
            if not ok:
                chosen = None
            progress = chosen is not None
            while progress:
                progress = False
                for j in reversed(order[:L0]):
                    if j in removed:
                        continue
                    trial = [s - {j} for s in chosen]
                    env.restore_state(snap); ok, n = accepted(env, pol, trial, t, H, A); sim += n
                    if ok:
                        chosen = trial; removed.append(j); progress = True; break
        if chosen is None:                                       # even the untruncated prefix fails: diverged caches
            if t == 0:
                raise SystemExit(f'SELF-CHECK FAIL: {seed}/{load}: the untruncated prefix is not accepted at t = 0')
            diverged = t if diverged is None else diverged; chosen = [frozenset(s) for s in P]
        env.restore_state(snap)
        _, acts = play(env, pol, chosen); _, _, rec = env.step(acts)
        steps.append(dict(t=t, K=K, order=list(order), L0=L0, b0=int(b0), bytes=int(rec['accounted_bytes']),
                          sent=sorted(set().union(*chosen)), pass0=pass0, same_action=[acts[i] for i in range(m)] == Aref[t],
                          queue=float(rec['queue']), z=z, mirror=mir, bid=bid))
    q = [s['queue'] for s in steps]
    if H == 'end' and q != Q:
        raise SystemExit(f'SELF-CHECK FAIL: {seed}/{load} {family} end: queues differ from the reference')
    return steps, sim, diverged


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    ck = torch.load(Path(a.actor), weights_only=False); sc = Scenarios(out)
    parity = {}
    if a.parity_rows:
        parity = {r['episode']: r for r in json.loads(Path(a.parity_rows).read_text()) if r['method'] == 'prefix'}
    rows = []; t0 = time.perf_counter(); arms = [(f, h) for f in a.families for h in a.horizons]
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'
            A, Q, B = reference(sc, seed, load, ck, a.capacity)
            if ep in parity:
                pr = parity[ep]
                if abs(pr['queue_sum'] - sum(Q)) > 1e-6 or pr['bytes'] != sum(B):
                    raise SystemExit(f'SELF-CHECK FAIL: {ep}: reference {sum(Q)}/{sum(B)} != closed-loop prefix row {pr["queue_sum"]}/{pr["bytes"]}')
            row = dict(episode=ep, traffic_seed=seed, headway=load, ref=dict(actions=A, queue=Q, bytes=B, queue_sum=sum(Q), bytes_sum=sum(B),
                                                                            parity=('checked' if ep in parity else 'no row')), arms={})
            for fam, H in arms:
                if fam.endswith('_local') and H != '0':
                    continue
                h = H if H == 'end' else int(H)
                steps, sim, div = run_D(sc, seed, load, ck, a.capacity, fam, h, A, Q)
                qs = sum(s['queue'] for s in steps); bs = sum(s['bytes'] for s in steps)
                row['arms'][f'{fam}_H{H}'] = dict(queue_sum=qs, bytes_sum=bs, saved_frac=1 - bs / sum(B), steps=steps, simulated_steps=sim,
                                                  first_divergence=div, action_match_rate=float(np.mean([s['same_action'] for s in steps])))
                print(f'[{time.perf_counter() - t0:.0f}s] {ep} {fam} H={H}: bytes {bs} vs {sum(B)} (saved {1 - bs / sum(B):.3f}) | '
                      f'queue {qs:.0f} vs {sum(Q):.0f} ({qs / sum(Q) - 1:+.4f}) | action match {row["arms"][f"{fam}_H{H}"]["action_match_rate"]:.3f} | sim steps {sim}', flush=True)
            rows.append(row); (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), episodes=len(rows), source_hashes=h0,
                                                       evidence_class='oracle diagnostic (upper bound; simulator cloned)', seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor', required=True); p.add_argument('--out', required=True)
    p.add_argument('--traffic-seeds', type=int, nargs='+', required=True); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--capacity', default='iid'); p.add_argument('--families', nargs='+', default=['tail'])
    p.add_argument('--horizons', nargs='+', default=['0', '1', '3', 'end']); p.add_argument('--parity-rows', default='')
    main(p.parse_args())
