#!/usr/bin/env python3
"""v2 (28/09, handoff F4): adds a CAUSALITY assertion for d > 0 -- every payload an agent uses at step t was measured no
later than the simulator time of step t - d.  Scope stays (i): a DELAYED RECEIVER-OBSERVATION stress test with an idealised
(zero-delay) scheduler and mirror; not a network-delay test of the bid -> selector -> transmission method.

v1 description follows.
Communication DELAY acting on traffic (research/marl_budget/PROTOCOL_E3_DELAY_ACQ_20260928.md, part A).

Payloads broadcast at decision step t reach their receivers at step t + d.  At step t a receiver acts on the
message cache it had at step t - d, with every age increased by d * action_interval; its own sensor is fresh.
The scheduler (committed cached-queue prefix, R = 0), capacities and bytes are unchanged, so the delay acts
on traffic only through the actions it changes.
Methods: frozen learned actors (CommAdapter encoding rebuilt from the delayed cache) and frozen MP2 (computed
from the delayed payloads through LegalView).
Self-checks (abort): at d = 0 the rebuilt encoding equals CommAdapter.encode(view, 'actual') and the LegalView
MP2 action equals mp2_action(view), at every step; access invariants and mirror checks every step.
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from models.marl_comm_actor import CommAdapter, ActorNet, N_PH, SCALE_Q, SCALE_P, SCALE_T
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_response_replay import LegalView
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios

SOURCES = ['scripts/MARL_e3_delay_v2.py', 'scripts/MARL_e3_delay.py', 'models/marl_comm_actor.py', 'scripts/MARL_hetero_response_replay.py',
           'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py']


def view_msgs(view):
    out = {e.sender: (0, float(e.age), e.payload) for e in view.cache}
    out.update({e.sender: (1, float(e.age), e.payload) for e in view.inbox})
    return out


def encode_msgs(ad, view, msgs):
    """CommAdapter.encode with the message dict given (same layout, same scaling)."""
    i = view.agent
    own = np.concatenate([np.asarray(view.lane_vehicles, np.float32).ravel() / SCALE_Q, np.asarray(view.lane_waiting, np.float32).ravel() / SCALE_Q,
                          np.eye(N_PH, dtype=np.float32)[int(view.own_phase)], [float(view.own_phase_elapsed) / SCALE_T, float(view.decision_step) / ad.n_dec]])
    blocks = []
    for j in range(ad.m):
        if j == i:
            continue
        b = np.zeros(ad.blk_dim, np.float32); b[-8:] = ad.static[(i, j)]
        if j in msgs:
            fr, age, p = msgs[j]
            b[0] = fr; b[1] = 1.0; b[2] = age / SCALE_T; b[3 + int(p.phase)] = 1.0; b[3 + N_PH] = float(p.phase_elapsed) / SCALE_T
            b[4 + N_PH:8 + N_PH] = np.asarray(p.vehicles, np.float32) / SCALE_P; b[8 + N_PH:12 + N_PH] = np.asarray(p.waiting, np.float32) / SCALE_P
        blocks.append(b)
    return np.concatenate([own, np.eye(ad.m, dtype=np.float32)[i]] + blocks).astype(np.float32)


def episode(sc, seed, load, d, actor, ad, mask):
    env, topo, down, onward = sc.env(seed, load); m = env.n_agents; hist = []; checks = 0; times = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            order, K = grant(env); env.submit_profile(prefix_sets(order, K), R=0)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            now_t = env._now(); times.append(now_t); hist.append({i: view_msgs(views[i]) for i in range(m)})
            src = hist[t - d] if t >= d else {i: {} for i in range(m)}
            delayed = {i: {j: (fr, age + d * env.action_interval, p) for j, (fr, age, p) in src[i].items()} for i in range(m)}
            if d > 0 and t >= d:
                for i in range(m):
                    for j, (_, _, p) in delayed[i].items():
                        if p.measured_at > times[t - d] + 1e-9:
                            raise AssertionError(f'CAUSALITY FAIL: payload of {j} measured at {p.measured_at} used at step {t} with delay {d}')
            if actor is None:
                acts = {}
                for i in range(m):
                    own = np.asarray(views[i].lane_waiting).sum(axis=1)
                    acts[i] = mp2_action(LegalView(own, {j: p for j, (_, _, p) in delayed[i].items()}), topo[i], down, onward)
                    if d == 0 and acts[i] != mp2_action(views[i], topo[i], down, onward):
                        raise AssertionError('SELF-CHECK FAIL: LegalView MP2 differs from mp2_action at d = 0')
            else:
                X = np.stack([encode_msgs(ad, views[i], delayed[i]) for i in range(m)])
                if d == 0:
                    ref = np.stack([ad.encode(views[i], 'actual') for i in range(m)])
                    if not np.array_equal(X, ref):
                        raise AssertionError('SELF-CHECK FAIL: rebuilt encoding differs from CommAdapter.encode at d = 0')
                with torch.no_grad():
                    A = actor(torch.as_tensor(X), mask).argmax(-1).numpy()
                acts = {i: int(A[i]) for i in range(m)}
            checks += 1
            _, _, rec = env.step(acts)
    s = env.episode_summary()
    return dict(episode=f'seed{seed}_load{load:g}', queue_sum=float(sum(r['queue'] for r in env.step_records)),
                finished=int(env.step_records[-1]['finished']), bytes=int(s['payload_bytes']), edits=0, summary=s, checks=checks)


def boot(v, B=10000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v, float)
    return [float(x) for x in np.quantile([v[rng.integers(0, len(v), len(v))].mean() for _ in range(B)], [0.025, 0.975])]


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    sc = Scenarios(out); env0, topo0, _, _ = sc.env(a.traffic_seeds[0], 8.0)
    ad = CommAdapter(topo0, N_DEC, env0.action_interval); mask = torch.as_tensor(ad.valid_mask())
    actors = {}
    for spec in a.actors:
        name, _, path = spec.partition('=')
        ck = torch.load(path, weights_only=False)
        if ck['schema'] != ad.schema():
            raise SystemExit(f'{path}: adapter schema differs')
        net = ActorNet(ad.dim, ck['config']['hidden']); net.load_state_dict(ck['actor']); net.eval(); actors[name] = net
    methods = [('mp2', None)] + list(actors.items()); rows = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in a.headways:
            for d in a.delays:
                for name, net in methods:
                    r = episode(sc, seed, load, d, net, ad, mask); r['method'] = f'{name}/d{d}'; r['delay'] = d; r['actor'] = name; rows.append(r)
            print(f'[{time.perf_counter() - t0:.0f}s] seed{seed}_load{load:g}: ' + ' '.join(f'{x["method"]} {x["queue_sum"]:.0f}' for x in rows[-len(a.delays) * len(methods):]), flush=True)
            tmp = out / '.rows.json'; tmp.write_text(json.dumps(rows, default=float)); os.replace(tmp, out / 'rows.json')
    rep = {}; eps = sorted({r['episode'] for r in rows}); Q = {(r['actor'], r['delay'], r['episode']): r['queue_sum'] for r in rows}
    for name, _ in methods:
        for d in a.delays:
            rel = [100 * (Q[(name, d, e)] - Q[(name, 0, e)]) / Q[(name, 0, e)] for e in eps]
            rep[f'{name}/d{d}_vs_d0'] = dict(mean=float(np.mean(rel)), ci95=boot(rel))
            if name != 'mp2':
                rel2 = [100 * (Q[('mp2', d, e)] - Q[(name, d, e)]) / Q[(name, d, e)] for e in eps]
                rep[f'mp2_vs_{name}/d{d}'] = dict(mean=float(np.mean(rel2)), ci95=boot(rel2))
    rep['mean_queue_sum'] = {f'{n}/d{d}': float(np.mean([Q[(n, d, e)] for e in eps])) for n, _ in methods for d in a.delays}
    rep['self_check'] = 'PASS (d = 0 encoding and MP2 identities; d > 0 causality: every used payload measured by t - d)'
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'report.json').write_text(json.dumps(rep, indent=1))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1))
    for k, v in rep.items():
        if isinstance(v, dict) and 'mean' in v:
            print(f'{k:28s} {v["mean"]:+6.2f}% [{v["ci95"][0]:+.2f}, {v["ci95"][1]:+.2f}]')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actors', nargs='+', required=True, help='NAME=ckpt path'); p.add_argument('--out', required=True)
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 917))); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--delays', type=int, nargs='+', default=[0, 1, 2, 3])
    main(p.parse_args())
