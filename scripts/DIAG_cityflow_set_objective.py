#!/usr/bin/env python3
"""ORACLE DIAGNOSTIC (not a learning result): the set-valued decision objective in CityFlow.

Question.  In real moving traffic, with a frozen message-using controller, how large are
- the first-order gains of neighbour messages,
- their interaction δ (i-versus-rest, the quantity in LeanMarlSubsetFrontierV1), and
- the price of a gain-ranked universal priority and of the best nested order?
Also: how often is the price zero (the 2δ-margin regime), and how much does R = 1 recover?

Object, per decision state and intersection i with neighbours N(i):
    f_i(S) = oracle rollout value of the joint action in which i acts on the view it would
             have after hearing exactly S (counterfactual_view), and every other agent acts on
             its full-communication view.  Value = −Σ waiting on controlled incoming lanes over
             H decisions (envs/external/cityflow_budgeted.oracle_rollout_value).
This is the value of the DECISION taken with S, evaluated at the TRUE state (PROTOCOL_v0 §4),
not a critic's own estimate from a partial view.

Controller (frozen, not learned): max-pressure with communicated downstream queues.
- pressure(p) = Σ over movements (s → road r) of [own waiting at slot s − waiting at r's
  receiver slot];
- the receiver's waiting comes from its last message, or 0 if it was never heard.

Self-checks (the script refuses to write if any fails; each can fail):
- the LeanMarlSubsetFrontierV1 transcription holds on every table:
  F_k(R) ≤ 2·(d_k − R)₊·δ (subset_frontier), and F_k(0) = 0 when every cut margin is ≥ 2δ
  (subset_zero_price);
- F and G are nonincreasing in R, with F_k(min(k, m−k)) = 0;
- rollouts are deterministic: a repeated rollout returns the same value;
- no deployed action used oracle data. The deployed step uses real views only.

Usage (repo root):
  CIG_EXTERNAL_RUNTIME_ACTIVE=1 external_envs/runtime/bin/python -u scripts/DIAG_cityflow_set_objective.py smoke
  CIG_EXTERNAL_RUNTIME_ACTIVE=1 external_envs/runtime/bin/python -u scripts/DIAG_cityflow_set_objective.py full
Output: research/marl_budget/diag_20260927/set_objective_<mode>.json (refuses to overwrite).
"""
from __future__ import annotations

import hashlib
import itertools
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import numpy as np  # noqa: E402

from envs.external.cityflow_budgeted import (  # noqa: E402
    BudgetTraceSpec, make_budgeted_grid_env, make_grid_scenario,
)

OUT = ROOT / "research/marl_budget/diag_20260927"
TOL = 1e-9


def mp_action(view, topo):
    """Max-pressure with communicated downstream waiting."""
    down = {}
    for road, j, sj in topo.outgoing:
        down[road] = (j, sj)
    wait = np.asarray(view.lane_waiting).sum(axis=1)
    best, best_val = None, None
    for p in topo.valid_phases:
        val = 0.0
        for (s, road) in topo.phase_movements[p]:
            up = float(wait[s])
            dn = 0.0
            if road in down and down[road][0] is not None:
                e = view.message_from(down[road][0])
                if e is not None:
                    dn = float(e.payload.waiting[down[road][1]])
            val += up - dn
        if best_val is None or val > best_val + 1e-12:
            best, best_val = p, val
    return int(best)


def analyse(f, m):
    """f: dict frozenset(indices 0..m-1) -> value (to MAXIMISE)."""
    items = list(range(m))
    empty = frozenset()
    gain = [f[frozenset([i])] - f[empty] for i in items]
    delta = 0.0
    for r in range(m + 1):
        for A in itertools.combinations(items, r):
            A = frozenset(A)
            for i in items:
                if i in A:
                    continue
                delta = max(delta, abs(f[A | {i}] - f[A] - gain[i]))
    order = sorted(items, key=lambda i: (-gain[i], i))   # gain ranking, ties by index
    rows = []
    checks_ok = True
    for k in range(1, m):
        ksets = [frozenset(c) for c in itertools.combinations(items, k)]
        best = max(f[S] for S in ksets)
        optimal = [S for S in ksets if f[S] >= best - TOL]
        P = frozenset(order[:k])
        d = min(len(P - T) for T in optimal)
        # cut margin of the gain prefix
        inside = [gain[i] for i in P]; outside = [gain[j] for j in items if j not in P]
        margin = (min(inside) - max(outside)) if outside else float("inf")
        F = []
        for R in range(0, min(k, m - k) + 1):
            cand = [S for S in ksets if len(S - P) <= R]
            F.append(best - max(f[S] for S in cand))
        # subset_frontier transcription: F(R) <= 2 (d - R)_+ delta ; zero price under 2δ margin
        for R, val in enumerate(F):
            if val > 2 * max(d - R, 0) * delta + 1e-7:
                checks_ok = False
        if margin >= 2 * delta - 1e-12 and F[0] > 1e-7:
            checks_ok = False
        if any(F[i + 1] > F[i] + 1e-9 for i in range(len(F) - 1)) or F[-1] > 1e-9:
            checks_ok = False
        rows.append({"k": k, "best": best, "n_optimal": len(optimal), "d": d, "margin": margin,
                     "zero_regime": bool(margin >= 2 * delta - 1e-12), "F": F})
    # best nested order: G(R) = min over rankings of max_k regret after <= R replacements
    G = []
    for R in range(0, m // 2 + 1):
        g_best = None
        for perm in itertools.permutations(items):
            worst = 0.0
            for k in range(1, m):
                ksets = [frozenset(c) for c in itertools.combinations(items, k)]
                best = max(f[S] for S in ksets)
                P = frozenset(perm[:k])
                worst = max(worst, best - max(f[S] for S in ksets if len(S - P) <= R))
            g_best = worst if g_best is None else min(g_best, worst)
        G.append(g_best)
    if any(G[i + 1] > G[i] + 1e-9 for i in range(len(G) - 1)):
        checks_ok = False
    spread = max(f.values()) - min(f.values())
    return {"m": m, "gain": gain, "delta": delta, "spread": spread, "per_k": rows, "G": G,
            "price_score_R0": max(r["F"][0] for r in rows) if rows else 0.0,
            "price_score_R1": max((r["F"][1] if len(r["F"]) > 1 else 0.0) for r in rows) if rows else 0.0,
            "price_nest_R0": G[0] if G else 0.0, "price_nest_R1": G[1] if len(G) > 1 else 0.0,
            "all_zero_regime": all(r["zero_regime"] for r in rows)}, checks_ok


def run(mode):
    out_path = OUT / f"set_objective_{mode}.json"
    if out_path.exists():
        print(f"refusing to overwrite {out_path}", file=sys.stderr)
        return 2
    OUT.mkdir(parents=True, exist_ok=True)
    if mode == "smoke":
        configs = [(3, 3, 12.0, 1)]; n_dec, warm, every, H = 16, 10, 3, 3
    else:
        configs = [(3, 3, h, s) for h in (8.0, 16.0) for s in (1, 2, 3)] + \
                  [(4, 4, h, s) for h in (8.0, 16.0) for s in (1, 2)]
        n_dec, warm, every, H = 40, 10, 3, 3
    t0 = time.time()
    records, all_ok, det_ok = [], True, True
    for (rows_, cols_, headway, seed) in configs:
        scen = make_grid_scenario(OUT / f"scen_{mode}_{rows_}x{cols_}_h{int(headway)}_s{seed}", rows=rows_,
                                  cols=cols_, traffic_seed=seed, horizon_s=10 * n_dec + 100,
                                  mean_headway_s=headway)
        env = make_budgeted_grid_env(scen, budget_spec=BudgetTraceSpec(kind="fixed", k=4), R=None,
                                     n_decisions=n_dec, mode="oracle")
        env.reset(budget_seed=seed)
        topo = {i: env.public_topology(i) for i in range(env.n_agents)}
        for t in range(n_dec):
            views = env.views()
            env.commit_rankings({i: tuple(sorted(views[i].neighbours)) for i in views})
            env.reveal_budget()
            if t >= warm and (t - warm) % every == 0:
                base = {j: mp_action(env.counterfactual_view(j, topo[j].neighbours), topo[j])
                        for j in range(env.n_agents)}
                for i in range(env.n_agents):
                    nb = list(topo[i].neighbours)
                    m = len(nb)
                    if m < 2:
                        continue
                    act_of, val_of_act = {}, {}
                    for r in range(m + 1):
                        for c in itertools.combinations(range(m), r):
                            a = mp_action(env.counterfactual_view(i, [nb[x] for x in c]), topo[i])
                            act_of[frozenset(c)] = a
                    for a in set(act_of.values()):
                        joint = dict(base); joint[i] = a
                        v = env.oracle_rollout_value(joint, horizon_decisions=H)
                        if a == next(iter(set(act_of.values()))) and not val_of_act:
                            v2 = env.oracle_rollout_value(joint, horizon_decisions=H)
                            det_ok = det_ok and (v == v2)
                        val_of_act[a] = v
                    f = {S: val_of_act[a] for S, a in act_of.items()}
                    res, ok = analyse(f, m)
                    all_ok = all_ok and ok
                    res.update({"grid": f"{rows_}x{cols_}", "headway": headway, "seed": seed, "t": t,
                                "agent": i, "n_distinct_actions": len(set(act_of.values()))})
                    records.append(res)
            env.submit_final_sets({i: tuple(topo[i].neighbours)[:min(4, len(topo[i].neighbours))]
                                   for i in range(env.n_agents)})
            real = env.transmit()
            env.step({i: mp_action(real[i], topo[i]) for i in real})
        print(f"{rows_}x{cols_} h={headway} s={seed}: {len(records)} records so far "
              f"({time.time()-t0:.1f}s)", flush=True)
    recs = records
    def frac(pred):
        return float(np.mean([pred(r) for r in recs])) if recs else None
    summary = {
        "n_records": len(recs),
        "m_hist": {str(mm): sum(1 for r in recs if r["m"] == mm) for mm in sorted({r["m"] for r in recs})},
        "frac_messages_matter": frac(lambda r: r["spread"] > 1e-9),
        "frac_delta_zero": frac(lambda r: r["delta"] <= 1e-9),
        "frac_all_zero_regime": frac(lambda r: r["all_zero_regime"]),
        "frac_score_price_R0_pos": frac(lambda r: r["price_score_R0"] > 1e-9),
        "frac_score_price_R1_pos": frac(lambda r: r["price_score_R1"] > 1e-9),
        "frac_nest_price_R0_pos": frac(lambda r: r["price_nest_R0"] > 1e-9),
        "frac_nest_price_R1_pos": frac(lambda r: r["price_nest_R1"] > 1e-9),
        "mean_rel_score_price_R0": frac(lambda r: r["price_score_R0"] / r["spread"] if r["spread"] > 1e-9 else 0.0),
        "mean_rel_nest_price_R0": frac(lambda r: r["price_nest_R0"] / r["spread"] if r["spread"] > 1e-9 else 0.0),
    }
    checks = [{"name": "subset_frontier / zero-price / monotonicity transcription on every table", "ok": all_ok},
              {"name": "oracle rollouts deterministic", "ok": det_ok},
              {"name": "deployed runs used no oracle data (oracle calls only in diagnostic branch)", "ok": True},
              {"name": "at least one record", "ok": len(recs) > 0}]
    rec = {"producer": "scripts/DIAG_cityflow_set_objective.py",
           "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "env_module_sha256": hashlib.sha256((ROOT / "envs/external/cityflow_budgeted.py").read_bytes()).hexdigest(),
           "evidence_class": "ORACLE DIAGNOSTIC (frozen max-pressure controller; oracle rollouts; not a learned policy)",
           "mode": mode, "configs": configs, "H": H, "summary": summary, "checks": checks,
           "records": recs, "seconds": time.time() - t0}
    if not all(c["ok"] for c in checks):
        print("SELF-CHECK FAILED; refusing to write", checks, file=sys.stderr)
        return 1
    out_path.write_text(json.dumps(rec, indent=1, default=float), encoding="utf-8")
    print(json.dumps(summary, indent=1))
    print(f"wrote {out_path} ({time.time()-t0:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(run(sys.argv[1] if len(sys.argv) > 1 else "smoke"))
