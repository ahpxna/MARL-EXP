#!/usr/bin/env python3
"""TARGET DIAGNOSTIC: held-phase labels against closed-loop CONTINUATION labels on the same states.

Question (independent readiness audit §4.6; B4 result).  The selectors are trained on the
held-phase label
    held_H(S) = - sum_{h=1..H} waiting_h   after the joint action of profile S, phases HELD H steps
(Labeler / oracle_rollout_value, H = 3).  The deployed loop instead re-senses, re-selects and re-acts
every step, and profile S also changes what each receiver has cached for later steps.  The
continuation label with a DECLARED common continuation c = (prefix scheduler, frozen MP2) is
    cont_H(S) = - sum_{h=1..H} waiting_h   when S is transmitted at step t and steps t+1..t+H-1
                                           run the live loop with c.
Both use the same state, the same capacity trace (the env's seeded trace) and the same H.

Design.  Development seeds only (default 501-504 x headways 8, 16; opened), snapshots t in {10, 16}
on the PREFIX trajectory, live K, the B1 candidate family (fresh seeded rng).  cont is computed by
re-running the episode from reset to t with the prefix policy (the env is deterministic), then
applying S; a fresh engine is built from the same scenario files for every candidate.
Outputs: rows.json (per state: candidates, bytes, joints, held_1, held_3, cont_1, cont_3) and
report.json: top-choice disagreement, realised continuation gain of the held-phase argmax, rank
correlation, sign agreement, over all candidates and over the +84 B feasible ones, also restricted
to candidates whose first joint action differs from the prefix's.
Self-checks, which can fail and are reported as SELF-CHECK FAIL:
  (1) the replayed prefix trajectory reproduces the base run's order, K and queues at t;
  (2) cont_1(S) == held_1(S) for every candidate (same joint action, same one-interval value);
  (3) cont_3(P) equals the base run's -(q_t + q_t+1 + q_t+2).
Evidence class: ORACLE-LABEL DIAGNOSTIC (not a learner, not a test).
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import BudgetTraceSpec, make_grid_scenario
from envs.external.cityflow_hetero_mirror import make_hetero_mirror_env
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets, profile_cost
from scripts.DIAG_cityflow_set_objective_hops import build_static, mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC, H, ROWS, COLS, candidates, Labeler

SOURCES = ['scripts/MARL_hetero_target_diag.py', 'scripts/MARL_hetero_pilot_collect.py',
           'envs/external/cityflow_hetero_mirror.py', 'envs/external/cityflow_hetero.py',
           'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py',
           'scripts/DIAG_cityflow_set_objective_hops.py']
CAP = 84


def scenario(out, seed, load):
    return make_grid_scenario(out / 'scenarios' / f'seed{seed}_load{load:g}', rows=ROWS, cols=COLS, traffic_seed=seed,
                              horizon_s=10 * (N_DEC + H + 5), mean_headway_s=load)


def new_env(scen, seed, load):                       # identical to MARL_hetero_closed_loop.make_env
    env = make_hetero_mirror_env(scen, budget_spec=BudgetTraceSpec(kind='bursty', k=4, k_low=1),
                                 n_decisions=N_DEC, capacity_seed=5000 + 10 * seed + int(load), mode='oracle')
    env.reset(budget_seed=1000 + seed)
    topo = {i: env.public_topology(i) for i in range(env.n_agents)}
    down, onward = build_static(topo)
    return env, topo, down, onward


def grant(env):
    with no_oracle_access(env):
        ctx = env.scheduler_context(); order = tuple(ctx.cached_queue_ranking())
        env.commit_global_ranking(order); Kd = env.reveal_budget()
    return order, [int(Kd[i]) for i in range(env.n_agents)]


def act(env, topo, down, onward, sets, cap=None):
    with no_oracle_access(env):
        env.submit_profile([set(s) for s in sets], R=None, cap=cap)
        views = env.transmit(); env.verify_mirror()
        joint = {i: mp2_action(v, topo[i], down, onward) for i, v in views.items()}
        _, _, rec = env.step(joint)
    return rec['queue'], tuple(joint[i] for i in range(env.n_agents))


def replay(scen, seed, load, t, S):
    env, topo, down, onward = new_env(scen, seed, load)
    for _ in range(t):
        order, K = grant(env); act(env, topo, down, onward, prefix_sets(order, K))
    order, K = grant(env)
    q = []; q0, j0 = act(env, topo, down, onward, S); q.append(q0)
    for _ in range(H - 1):
        o, k = grant(env); q.append(act(env, topo, down, onward, prefix_sets(o, k))[0])
    return order, K, q, j0


def spearman(a, b):
    ra = np.argsort(np.argsort(a)); rb = np.argsort(np.argsort(b))
    if np.std(ra) == 0 or np.std(rb) == 0:
        return None
    return float(np.corrcoef(ra, rb)[0, 1])


def summarise(st, feasible_only, changing_only):
    C = [c for c in st['cands'] if (not feasible_only or c['feasible']) and (not changing_only or c['changes'])]
    P = st['cands'][0]
    if len(C) < 2:
        return None
    gh = np.array([c['held_3'] - P['held_3'] for c in C]); gc = np.array([c['cont_3'] - P['cont_3'] for c in C])
    ih, ic = int(np.argmax(gh)), int(np.argmax(gc))
    pos = gh > 1e-9
    return dict(n=len(C), held_best_gain=float(gh[ih]), cont_best_gain=float(gc[ic]), cont_gain_of_held_best=float(gc[ih]),
                top_agree=bool(abs(gc[ih] - gc[ic]) < 1e-9), spearman=spearman(gh, gc),
                n_held_pos=int(pos.sum()), frac_cont_pos_given_held_pos=float((gc[pos] > 1e-9).mean()) if pos.any() else None,
                mean_cont_gain_given_held_pos=float(gc[pos].mean()) if pos.any() else None)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    states = []; fails = []; t0 = time.perf_counter()
    for seed in a.seeds:
        for load in a.headways:
            scen = scenario(out, seed, load)
            env, topo, down, onward = new_env(scen, seed, load); m = env.n_agents
            rngc = np.random.default_rng(40000 + 10 * seed + int(load)); base_q = []; snap = {}
            for t in range(max(a.snaps) + H):
                order, K = grant(env)
                if t in a.snaps:
                    lab = Labeler(env, lambda i, v: mp2_action(v, topo[i], down, onward))
                    cands = [tuple(frozenset(s) for s in c) for c in candidates(order, K, m, rngc)]
                    P = tuple(frozenset(s) for s in prefix_sets(order, K))
                    cands = [P] + [c for c in cands if c != P]
                    b0 = profile_cost(order, K, [set(s) for s in P])[0]
                    rows = []
                    for c in cands:
                        j = lab.joint(c)
                        rows.append(dict(sets=[sorted(s) for s in c], joint=list(j), held_3=float(lab.value(c)),
                                         held_1=float(env.oracle_rollout_value(dict(enumerate(j)), 1)),
                                         bytes=int(profile_cost(order, K, [set(s) for s in c])[0]),
                                         feasible=bool(profile_cost(order, K, [set(s) for s in c])[0] <= b0 + CAP),
                                         changes=bool(tuple(j) != tuple(lab.joint(P)))))
                    snap[t] = dict(order=list(order), K=K, cands=rows)
                base_q.append(act(env, topo, down, onward, prefix_sets(order, K))[0])
            for t, st in snap.items():
                for ci, c in enumerate(st['cands']):
                    order, K, q, j0 = replay(scen, seed, load, t, [set(s) for s in c['sets']])
                    if list(order) != st['order'] or K != st['K']:
                        fails.append(f'seed{seed} load{load} t{t} cand{ci}: replay order/K differs')
                    c['cont_1'] = -float(q[0]); c['cont_3'] = -float(sum(q)); c['live_joint'] = list(j0)
                    if abs(c['cont_1'] - c['held_1']) > 1e-9 or list(j0) != c['joint']:
                        fails.append(f'seed{seed} load{load} t{t} cand{ci}: cont_1 {c["cont_1"]} != held_1 {c["held_1"]} '
                                     f'or live joint != counterfactual joint')
                ref = -float(sum(base_q[t:t + H]))
                if abs(st['cands'][0]['cont_3'] - ref) > 1e-9:
                    fails.append(f'seed{seed} load{load} t{t}: cont_3(P) {st["cands"][0]["cont_3"]} != base {ref}')
                st.update(episode=f'seed{seed}_load{load:g}', t=t)
                st['summary'] = {f'{"feas" if f else "all"}_{"chg" if g else "any"}': summarise(st, f, g)
                                 for f in (False, True) for g in (False, True)}
                states.append(st)
                s = st['summary']['feas_any']
                print(f'[{time.perf_counter() - t0:.0f}s] {st["episode"]} t{t}: {len(st["cands"])} cands | +84: held-best '
                      f'{s["held_best_gain"]:+.1f} realised {s["cont_gain_of_held_best"]:+.1f} cont-best {s["cont_best_gain"]:+.1f} '
                      f'agree {s["top_agree"]} rho {s["spearman"]} | fails so far {len(fails)}', flush=True)
                tmp = out / '.rows.json'; tmp.write_text(json.dumps(states)); os.replace(tmp, out / 'rows.json')
    rep = dict(self_check='PASS' if not fails else 'SELF-CHECK FAIL', failures=fails[:50], n_failures=len(fails),
               states=len(states), H=H, cap=CAP, continuation='prefix scheduler + frozen MP2 from step t+1',
               seeds=a.seeds, headways=a.headways, snaps=a.snaps)
    for key in ('all_any', 'feas_any', 'all_chg', 'feas_chg'):
        L = [s['summary'][key] for s in states if s['summary'][key]]
        if not L:
            continue
        def mean(f):
            v = [x[f] for x in L if x[f] is not None]
            return float(np.mean(v)) if v else None
        rep[key] = dict(states=len(L), top_agree_rate=float(np.mean([x['top_agree'] for x in L])),
                        held_best_gain=mean('held_best_gain'), cont_gain_of_held_best=mean('cont_gain_of_held_best'),
                        cont_best_gain=mean('cont_best_gain'), spearman=mean('spearman'),
                        frac_cont_pos_given_held_pos=mean('frac_cont_pos_given_held_pos'),
                        mean_cont_gain_given_held_pos=mean('mean_cont_gain_given_held_pos'))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'report.json').write_text(json.dumps(rep, indent=1))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0,
        seconds=time.perf_counter() - t0), indent=1, default=str))
    print(json.dumps(rep, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True)
    p.add_argument('--seeds', type=int, nargs='+', default=[501, 502, 503, 504])
    p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--snaps', type=int, nargs='+', default=[10, 16])
    main(p.parse_args())
