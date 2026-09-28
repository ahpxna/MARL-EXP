#!/usr/bin/env python3
"""F5 bridge panel v2 (28/09 self-audit of MARL_e3_bridge_panel.py; v1 and its output e3_bridge_20260928 are kept).

Three defects of v1, found against LeanMarlEstimatedRevisionV1:
  1. ScoreLocal quantifies over EVERY context A, including the empty set; v1 evaluated only 1 <= |A| <= 7, so its
     eta* is a lower bound on the Lean constant.  v2 also evaluates A = {} (receiver i decodes nothing, capacity 0
     at that step, reduced object only).
  2. v1 read hTop at ONE minimiser of the Chebyshev LP, which is not unique; 'hTop false' was not certified.
     v2 solves a second LP, eta_top = min eta s.t. ScoreLocal(f, w, eta) AND the deployed prefix P_i is top-k_i by w
     (w_q <= w_p for p in P_i, q not in P_i: the hypothesis hTop of score_frontier).  hTop is satisfiable at the
     optimal constant iff eta_top = eta*.
  3. v1 reported 2 eta* (d - R)_+ as 'the T1 bound'; with hTop failing at that w it is not an instance of
     score_frontier.  The valid instance is 2 eta_top (d - R)_+ (score_frontier needs both hypotheses at one w).
     v2 reports both, and d = min over OPTIMAL k-sets T of |P_i \\ T| (ties), the tightest valid choice.
Every value f(A) is saved (f.json) so these LPs can be re-solved without rollouts.  Everything else as v1:
f(A) = cont_3 of the declared continuation, same actor, other receivers keep the prefix; self-checks: committed order
unchanged, f(P_i) equals the base trajectory's continuation.  Development states only.
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
from scripts.MARL_hetero_pilot_collect import H, candidates
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_continuation_labels import Policy, step_with
from scripts.MARL_e3_bridge_panel import value

SOURCES = ['scripts/MARL_e3_bridge_panel_v2.py', 'scripts/MARL_e3_bridge_panel.py', 'scripts/MARL_e3_continuation_labels.py',
           'models/marl_comm_actor.py', 'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py']


def lp_eta(f, others, top=None):
    """min eta s.t. |f(A+j) - f(A) - w_j| <= eta for EVERY A (incl. {}) and j not in A; if top is given, also
    w_q - w_p <= 0 for p in top, q not in top.  Returns (eta, w, #ScoreLocal constraint pairs)."""
    n = len(others); idx = {j: t for t, j in enumerate(others)}; rows, rhs = [], []
    for A in f:
        for j in others:
            if j in A:
                continue
            B = tuple(sorted(A + (j,)))
            if B not in f:
                raise AssertionError(f'context {A} + {j}: value missing')
            dlt = f[B] - f[A]
            r1 = np.zeros(n + 1); r1[idx[j]] = -1; r1[-1] = -1; rows.append(r1); rhs.append(-dlt)
            r2 = np.zeros(n + 1); r2[idx[j]] = 1; r2[-1] = -1; rows.append(r2); rhs.append(dlt)
    npairs = len(rows) // 2
    if top is not None:
        for p in top:
            for q in others:
                if q not in top:
                    r = np.zeros(n + 1); r[idx[q]] = 1; r[idx[p]] = -1; rows.append(r); rhs.append(0.0)
    c = np.zeros(n + 1); c[-1] = 1
    res = linprog(c, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=[(None, None)] * n + [(0, None)], method='highs')
    if res.status != 0:
        raise RuntimeError(f'LP failed: {res.message}')
    return float(res.x[-1]), {j: float(res.x[idx[j]]) for j in others}, npairs


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    ck = torch.load(a.ckpt, weights_only=False); sc = Scenarios(out); rows, F = [], {}; t0 = time.perf_counter()
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
                for r_ in range(0, len(others) + 1):
                    for A in itertools.combinations(others, r_):
                        f[A], o_chk = value(sc, seed, load, ck, t, i, A)
                        if o_chk != order:
                            raise AssertionError('SELF-CHECK FAIL: committed order changed')
                ref = -float(sum(base[t:t + H]))
                if abs(f[Pi] - ref) > 1e-9:
                    raise AssertionError(f'SELF-CHECK FAIL: f(P_i) {f[Pi]} != base {ref}')
                eta, w, npairs = lp_eta(f, others)
                eta_top, w_top, _ = lp_eta(f, others, top=Pi)
                if eta_top < eta - 1e-7:
                    raise AssertionError('SELF-CHECK FAIL: the constrained LP beat the unconstrained one')
                kset = [A for A in f if len(A) == k]; Vall = max(f[A] for A in kset)
                opt = [A for A in kset if f[A] >= Vall - 1e-9]; d = min(len(set(Pi) - set(A)) for A in opt)
                b0 = profile_cost(order, Kt, [set(s) for s in P])[0]
                def cost(A):
                    S = [set(s) for s in P]; S[i] = set(A); return profile_cost(order, Kt, S)[0]
                ep = f'seed{seed}_load{load:g}'
                res = dict(episode=ep, t=t, receiver=i, k=k, prefix=list(Pi), f_prefix=f[Pi], V_all=Vall, gain_all=Vall - f[Pi],
                           f_range=float(np.ptp([f[A] for A in kset])), n_contexts=len(f), scorelocal_pairs=npairs,
                           eta_star=eta, eta_top=eta_top, hTop_at_optimum=bool(eta_top <= eta + 1e-7), d_min=d, n_optimal_ksets=len(opt))
                for R in (1, 2):
                    reach = [A for A in kset if len(set(A) - set(Pi)) <= R]
                    VR = max(f[A] for A in reach); VRB = max(f[A] for A in reach if cost(A) <= b0 + 84)
                    res.update({f'V_R{R}': VR, f'geom_loss_R{R}': Vall - VR, f'byte_loss_R{R}': VR - VRB,
                                f'T1_valid_R{R}': 2 * eta_top * max(d - R, 0), f'T1_unconstrained_R{R}': 2 * eta * max(d - R, 0)})
                    if Vall - VR > 2 * eta_top * max(d - R, 0) + 1e-7:
                        raise AssertionError(f'SELF-CHECK FAIL: score_frontier violated at R={R} ({Vall - VR} > {2 * eta_top * max(d - R, 0)})')
                famI = [c for c in fam if all(set(c[r]) == set(P[r]) for r in range(m) if r != i)]
                VC = max(f[tuple(sorted(c[i]))] for c in famI) if famI else f[Pi]
                res.update(V_C=VC, coverage_loss_vs_all=Vall - VC, family_profiles_for_i=len(famI))
                rows.append(res); F[f'{ep}_t{t}'] = dict(receiver=i, others=others, f={','.join(map(str, A)): v for A, v in f.items()})
                print(f'[{time.perf_counter() - t0:.0f}s] {ep} t{t} i{i} k{k}: eta* {eta:.2f} eta_top {eta_top:.2f} hTop@opt {res["hTop_at_optimum"]} '
                      f'gain {res["gain_all"]:+.0f} d {d} geomR1 {res["geom_loss_R1"]:.0f} T1(valid) {res["T1_valid_R1"]:.1f} '
                      f'byteR1 {res["byte_loss_R1"]:.0f} coverage {res["coverage_loss_vs_all"]:.0f}', flush=True)
                (out / 'rows.json').write_text(json.dumps(rows, indent=1)); (out / 'f.json').write_text(json.dumps(F))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), source_hashes=h0,
                                                       seconds=time.perf_counter() - t0), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ckpt', required=True); p.add_argument('--out', required=True)
    p.add_argument('--seeds', type=int, nargs='+', default=[501, 502, 503, 504]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--snaps', type=int, nargs='+', default=[10, 16])
    main(p.parse_args())
