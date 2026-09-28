#!/usr/bin/env python3
"""F5 bridge panel (handoff): T1 on a REDUCED, fully enumerable receiver-sender subproblem of a frozen learned actor.

Subproblem at a development state (prefix trajectory, live K): one receiver i (the legal choice: the smallest
top-2 logit gap in the receivers' own bids); every other receiver keeps its prefix set; receiver i decodes a set
A of the other senders, for EVERY A with 1 <= |A| <= 7 (254 sets; its capacity at that step is set to |A| for this
reduced object only).  f(A) = cont_3 (the declared continuation of MARL_e3_continuation_labels.py, same actor).
On this whole space:
  eta*      exact minimal ScoreLocal constant: min_w max_{A, j not in A} |f(A + j) - f(A) - w_j|  (Chebyshev LP)
            -- over ALL contexts of the small space, not one-swaps;
  hTop      whether the deployed prefix P_i (first k_i of the committed order) is top-k_i by the fitted w;
  geometry  V_all = max_{|A| = k_i} f;  V_R = max over |A \\ P_i| <= R (R = 1, 2);  T1 bound 2 eta* (d - R)_+ with
            d = |P_i \\ A*|;  realised geometric loss V_all - V_R against the bound;
  bytes     V_{R,B}: the same maxima within +84 B of the prefix bytes (profile_cost of the full profile);
  coverage  V_C: the maximum over the B1 candidate family's profiles that change only receiver i;
Self-check: f(P_i) equals the base trajectory's continuation (replay determinism).  Development states only.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, sys, time
from pathlib import Path
import numpy as np
import torch
from scipy.optimize import linprog

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets, profile_cost
from scripts.MARL_hetero_pilot_collect import N_DEC, H, candidates
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_continuation_labels import Policy, step_with

SOURCES = ['scripts/MARL_e3_bridge_panel.py', 'scripts/MARL_e3_continuation_labels.py', 'models/marl_comm_actor.py',
           'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py']


def value(sc, seed, load, ck, t, i, A):
    env, topo, _, _ = sc.env(seed, load); pol = Policy(ck, topo, env.action_interval)
    for _ in range(t):
        with no_oracle_access(env):
            o, k = grant(env)
        step_with(env, pol, prefix_sets(o, k))
    env._trace = env._trace.copy(); env._trace[t, i] = len(A)
    with no_oracle_access(env):
        o, k = grant(env)
    sets = prefix_sets(o, k); sets = [set(s) for s in sets]; sets[i] = set(A)
    q = [step_with(env, pol, sets)[0]]
    for _ in range(H - 1):
        with no_oracle_access(env):
            o2, k2 = grant(env)
        q.append(step_with(env, pol, prefix_sets(o2, k2))[0])
    return -float(sum(q)), tuple(o)


def cheb_eta(f, others):
    """min eta s.t. |f(A+j) - f(A) - w_j| <= eta for all A (1 <= |A| <= 6), j not in A.  Variables (w, eta)."""
    idx = {j: n for n, j in enumerate(others)}; rows, rhs = [], []
    for A in f:
        if len(A) > 6:
            continue
        for j in others:
            if j in A:
                continue
            B = tuple(sorted(A + (j,)))
            if B not in f:
                continue
            dlt = f[B] - f[A]; r1 = np.zeros(len(others) + 1); r1[idx[j]] = -1; r1[-1] = -1; rows.append(r1); rhs.append(-dlt)
            r2 = np.zeros(len(others) + 1); r2[idx[j]] = 1; r2[-1] = -1; rows.append(r2); rhs.append(dlt)
    c = np.zeros(len(others) + 1); c[-1] = 1
    res = linprog(c, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=[(None, None)] * len(others) + [(0, None)], method='highs')
    return float(res.x[-1]), {j: float(res.x[idx[j]]) for j in others}, len(rows) // 2


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    ck = torch.load(a.ckpt, weights_only=False); sc = Scenarios(out); rows = []; t0 = time.perf_counter()
    for seed in a.seeds:
        for load in a.headways:
            for t in a.snaps:
                env, topo, _, _ = sc.env(seed, load); pol = Policy(ck, topo, env.action_interval); m = env.n_agents
                rngc = np.random.default_rng(90000 + 10 * seed + int(load)); base = []
                for s in range(t + H):
                    with no_oracle_access(env):
                        o, K = grant(env)
                        if s == t:
                            pre = {r: env._build_view(r) for r in range(m)}; order, Kt = tuple(o), list(K)
                    if s == t:
                        lg = pol.logits(pre); gaps = [float(np.sort(lg[r])[-1] - np.sort(lg[r])[-2]) for r in range(m)]
                        i = int(np.argmin(gaps)); fam = candidates(order, Kt, m, rngc)
                    base.append(step_with(env, pol, prefix_sets(o, K))[0])
                P = prefix_sets(order, Kt); Pi = tuple(sorted(P[i])); k = Kt[i]; others = [j for j in range(m) if j != i]
                f = {}
                for r_ in range(1, 8):
                    for A in itertools.combinations(others, r_):
                        f[A], o_chk = value(sc, seed, load, ck, t, i, A)
                        if o_chk != order:
                            raise AssertionError('SELF-CHECK FAIL: committed order changed')
                ref = -float(sum(base[t:t + H]))
                if abs(f[Pi] - ref) > 1e-9:
                    raise AssertionError(f'SELF-CHECK FAIL: f(P_i) {f[Pi]} != base {ref}')
                eta, w, ncon = cheb_eta(f, others)
                kset = [A for A in f if len(A) == k]
                b0 = profile_cost(order, Kt, [set(s) for s in P])[0]
                def cost(A):
                    S = [set(s) for s in P]; S[i] = set(A); return profile_cost(order, Kt, S)[0]
                Vall = max(f[A] for A in kset); Astar = max(kset, key=lambda A: f[A]); d = len(set(Pi) - set(Astar))
                topw = tuple(sorted(sorted(others, key=lambda j: -w[j])[:k]))
                res = dict(episode=f'seed{seed}_load{load:g}', t=t, receiver=i, k=k, eta=eta, constraints=ncon, f_prefix=f[Pi], V_all=Vall,
                           d=d, hTop=bool(set(topw) == set(Pi)), gain_all=Vall - f[Pi], f_range=float(np.ptp([f[A] for A in kset])))
                for R in (1, 2):
                    reach = [A for A in kset if len(set(A) - set(Pi)) <= R]
                    VR = max(f[A] for A in reach); VRB = max(f[A] for A in reach if cost(A) <= b0 + 84)
                    res[f'V_R{R}'] = VR; res[f'V_R{R}B'] = VRB; res[f'geom_loss_R{R}'] = Vall - VR; res[f'T1_bound_R{R}'] = 2 * eta * max(d - R, 0)
                    res[f'byte_loss_R{R}'] = VR - VRB
                famI = [c for c in fam if all(set(c[r]) == set(P[r]) for r in range(m) if r != i)]
                VC = max(f[tuple(sorted(c[i]))] for c in famI) if famI else f[Pi]
                res['V_C'] = VC; res['coverage_loss_vs_all'] = Vall - VC; res['family_profiles_for_i'] = len(famI)
                rows.append(res)
                print(f'[{time.perf_counter() - t0:.0f}s] {res["episode"]} t{t} i{i} k{k}: eta* {eta:.2f} hTop {res["hTop"]} gain_all {res["gain_all"]:+.0f} '
                      f'geomR1 {res["geom_loss_R1"]:.0f} (T1 bound {res["T1_bound_R1"]:.1f}) byteR1 {res["byte_loss_R1"]:.0f} coverage {res["coverage_loss_vs_all"]:.0f}', flush=True)
                (out / 'rows.json').write_text(json.dumps(rows, indent=1))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ckpt', required=True); p.add_argument('--out', required=True)
    p.add_argument('--seeds', type=int, nargs='+', default=[501, 502, 503, 504]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--snaps', type=int, nargs='+', default=[10, 16])
    main(p.parse_args())
