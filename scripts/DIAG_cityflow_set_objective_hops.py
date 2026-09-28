#!/usr/bin/env python3
"""ORACLE DIAGNOSTIC, multi-hop candidates (not a learning result).

Same question as scripts/DIAG_cityflow_set_objective.py, with the candidate senders of each
intersection set to every intersection within 2 hops: m = 5..8 on a 3×3 grid, up to 10 on a
4×4 grid.  By LeanMarlNestingDegreeGeneralV1 and exhaustive enumeration, a price of nesting
that one revision cannot remove needs m ≥ 7.

Controller (frozen, not learned): TWO-STEP max-pressure (MP2).
- For each movement s → road r → (j, slot s_j), the pressure is
  own waiting at s − waiting at j's slot s_j − ½ · mean over j's onward movements from s_j
  of the waiting at the next receiver's slot.
- Every downstream quantity comes from the last message received from that intersection
  (0 if never heard).
- j's onward movements are read from PUBLIC static topology only.
- λ = ½ is fixed a priori.  It is NOT tuned to create a price.

Per (state, intersection) table f(S):
- the gains g_j and the interaction δ (i versus rest);
- per budget k: the gain-prefix regret F_k(R) for R = 0..min(k, m−k), d_k, the cut margin;
- the best-nested-order price G(R) for R = 0, 1, 2, by exact DP over chains.

Self-checks (the script refuses to write on failure; each can fail):
- subset_frontier: F_k(R) ≤ 2·(d_k − R)₊·δ;
- zero price under a 2δ margin;
- monotonicity in R;
- G(R) ≤ max_k F_k(R), since the gain prefix is one nested order;
- rollout determinism.

Usage: CIG_EXTERNAL_RUNTIME_ACTIVE=1 external_envs/runtime/bin/python -u scripts/DIAG_cityflow_set_objective_hops.py {smoke|full}
Output: research/marl_budget/diag_20260927/set_objective_hops_<mode>.json (refuses to overwrite).
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

from envs.external.cityflow_budgeted import BudgetTraceSpec, make_grid_scenario  # noqa: E402
from envs.external.cityflow_budgeted_hops import make_budgeted_grid_env_hops  # noqa: E402

OUT = ROOT / "research/marl_budget/diag_20260927"
LAMBDA = 0.5
TOL = 1e-9


def build_static(topos):
    """down[i][road] = (j, s_j); onward[j][s_j] = list of (j2, s2) reachable from slot s_j at j."""
    down, onward = {}, {}
    for i, t in topos.items():
        down[i] = {road: (j, sj) for road, j, sj in t.outgoing}
    for j, t in topos.items():
        o = {}
        for mv in t.phase_movements:
            for (s, road) in mv:
                j2, s2 = down[j].get(road, (None, None))
                if j2 is not None:
                    o.setdefault(s, set()).add((j2, s2))
        onward[j] = {s: sorted(v) for s, v in o.items()}
    return down, onward


def mp2_action(view, topo, down, onward):
    wait = np.asarray(view.lane_waiting).sum(axis=1)
    def heard_wait(j, s):
        e = view.message_from(j)
        return float(e.payload.waiting[s]) if e is not None else 0.0
    best, best_val = None, None
    i = topo.agent
    for p in topo.valid_phases:
        val = 0.0
        for (s, road) in topo.phase_movements[p]:
            up = float(wait[s])
            j, sj = down[i].get(road, (None, None))
            dn1 = dn2 = 0.0
            if j is not None:
                dn1 = heard_wait(j, sj)
                nxt = onward.get(j, {}).get(sj, [])
                if nxt:
                    dn2 = float(np.mean([heard_wait(j2, s2) for (j2, s2) in nxt]))
            val += up - dn1 - LAMBDA * dn2
        if best_val is None or val > best_val + 1e-12:
            best, best_val = p, val
    return int(best)


def popc(x):
    return bin(x).count("1")


def analyse(f, m):
    """f: list indexed by bitmask over m items; values to MAXIMISE."""
    full = (1 << m) - 1
    gain = [f[1 << i] - f[0] for i in range(m)]
    delta = 0.0
    for mask in range(1 << m):
        for i in range(m):
            if not (mask >> i) & 1:
                delta = max(delta, abs(f[mask | (1 << i)] - f[mask] - gain[i]))
    order = sorted(range(m), key=lambda i: (-gain[i], i))
    layers = {k: [x for x in range(1 << m) if popc(x) == k] for k in range(m + 1)}
    best = {k: max(f[x] for x in layers[k]) for k in range(1, m)}
    ok = True
    per_k = []
    for k in range(1, m):
        P = sum(1 << i for i in order[:k])
        opt = [x for x in layers[k] if f[x] >= best[k] - TOL]
        d = min(popc(P & ~T) for T in opt)
        inside = [gain[i] for i in order[:k]]; outside = [gain[i] for i in order[k:]]
        margin = (min(inside) - max(outside)) if outside else float("inf")
        F = []
        for R in range(0, min(k, m - k) + 1):
            F.append(best[k] - max(f[x] for x in layers[k] if popc(x & ~P) <= R))
        for R, v in enumerate(F):
            if v > 2 * max(d - R, 0) * delta + 1e-7:
                ok = False
        if margin >= 2 * delta - 1e-12 and F[0] > 1e-7:
            ok = False
        if any(F[r + 1] > F[r] + 1e-9 for r in range(len(F) - 1)) or F[-1] > 1e-9:
            ok = False
        per_k.append({"k": k, "d": d, "margin": margin, "zero_regime": bool(margin >= 2 * delta - 1e-12), "F": F})
    # best nested order: exact DP over chains, R = 0, 1, 2
    G = []
    for R in (0, 1, 2):
        # nb[C] = best value within R replacements of C (same layer)
        reg = {}
        for k in range(1, m):
            for C in layers[k]:
                if R == 0:
                    v = f[C]
                else:
                    ins = [i for i in range(m) if (C >> i) & 1]
                    outs = [i for i in range(m) if not (C >> i) & 1]
                    v = f[C]
                    for r in range(1, R + 1):
                        for a in itertools.combinations(ins, r):
                            for b in itertools.combinations(outs, r):
                                S = C
                                for x in a: S &= ~(1 << x)
                                for y in b: S |= (1 << y)
                                if f[S] > v: v = f[S]
                reg[C] = best[k] - v
        dp = {0: 0.0}
        for k in range(1, m):
            nd = {}
            for C0, v0 in dp.items():
                for i in range(m):
                    if not (C0 >> i) & 1:
                        C = C0 | (1 << i)
                        val = max(v0, reg[C])
                        if val < nd.get(C, float("inf")):
                            nd[C] = val
            dp = nd
        G.append(min(dp.values()) if dp else 0.0)
    if any(G[r + 1] > G[r] + 1e-9 for r in range(len(G) - 1)):
        ok = False
    for R in range(3):
        score_R = max((row["F"][R] if R < len(row["F"]) else 0.0) for row in per_k)
        if G[R] > score_R + 1e-9:
            ok = False
    spread = max(f) - min(f)
    return {"m": m, "gain": gain, "delta": delta, "spread": spread, "per_k": per_k, "G": G,
            "price_score": [max((row["F"][R] if R < len(row["F"]) else 0.0) for row in per_k) for R in range(3)],
            "all_zero_regime": all(r["zero_regime"] for r in per_k)}, ok


def run(mode):
    out_path = OUT / f"set_objective_hops_{mode}.json"
    if out_path.exists():
        print(f"refusing to overwrite {out_path}", file=sys.stderr)
        return 2
    OUT.mkdir(parents=True, exist_ok=True)
    if mode == "smoke":
        configs = [(3, 3, 12.0, 1)]; n_dec, warm, every, H = 14, 10, 3, 3
    else:
        configs = [(3, 3, h, s) for h in (8.0, 16.0) for s in (1, 2, 3)] + \
                  [(4, 4, h, s) for h in (8.0, 16.0) for s in (1, 2)]
        n_dec, warm, every, H = 34, 10, 4, 3
    t0 = time.time()
    records, all_ok, det_ok = [], True, True
    for (rows_, cols_, headway, seed) in configs:
        scen = make_grid_scenario(OUT / f"scenhops_{mode}_{rows_}x{cols_}_h{int(headway)}_s{seed}", rows=rows_,
                                  cols=cols_, traffic_seed=seed, horizon_s=10 * n_dec + 100,
                                  mean_headway_s=headway)
        env = make_budgeted_grid_env_hops(scen, hops=2, budget_spec=BudgetTraceSpec(kind="fixed", k=16), R=None,
                                          n_decisions=n_dec, mode="oracle")
        env.reset(budget_seed=seed)
        topos = {i: env.public_topology(i) for i in range(env.n_agents)}
        down, onward = build_static(topos)
        for t in range(n_dec):
            views = env.views()
            env.commit_rankings({i: tuple(sorted(views[i].neighbours)) for i in views})
            env.reveal_budget()
            if t >= warm and (t - warm) % every == 0:
                base = {j: mp2_action(env.counterfactual_view(j, topos[j].neighbours), topos[j], down, onward)
                        for j in range(env.n_agents)}
                for i in range(env.n_agents):
                    nb = list(topos[i].neighbours)
                    m = len(nb)
                    acts = []
                    for mask in range(1 << m):
                        heard = [nb[x] for x in range(m) if (mask >> x) & 1]
                        acts.append(mp2_action(env.counterfactual_view(i, heard), topos[i], down, onward))
                    vals = {}
                    for idx, a in enumerate(sorted(set(acts))):
                        joint = dict(base); joint[i] = a
                        vals[a] = env.oracle_rollout_value(joint, horizon_decisions=H)
                        if idx == 0:
                            det_ok = det_ok and (vals[a] == env.oracle_rollout_value(joint, horizon_decisions=H))
                    f = [vals[a] for a in acts]
                    res, ok = analyse(f, m)
                    all_ok = all_ok and ok
                    res.update({"grid": f"{rows_}x{cols_}", "headway": headway, "seed": seed, "t": t, "agent": i,
                                "n_distinct_actions": len(set(acts))})
                    records.append(res)
            env.submit_final_sets({i: tuple(topos[i].neighbours) for i in range(env.n_agents)})
            real = env.transmit()
            env.step({i: mp2_action(real[i], topos[i], down, onward) for i in real})
        print(f"{rows_}x{cols_} h={headway} s={seed}: {len(records)} records ({time.time()-t0:.1f}s)", flush=True)
    recs = records
    def frac(pred, sub=None):
        rr = [r for r in recs if (sub is None or sub(r))]
        return float(np.mean([pred(r) for r in rr])) if rr else None
    summary = {"n_records": len(recs),
               "m_hist": {str(mm): sum(1 for r in recs if r["m"] == mm) for mm in sorted({r["m"] for r in recs})},
               "frac_messages_matter": frac(lambda r: r["spread"] > 1e-9),
               "frac_delta_zero": frac(lambda r: r["delta"] <= 1e-9),
               "frac_all_zero_regime": frac(lambda r: r["all_zero_regime"])}
    for R in range(3):
        summary[f"frac_score_price_R{R}_pos"] = frac(lambda r, R=R: r["price_score"][R] > 1e-9)
        summary[f"frac_nest_price_R{R}_pos"] = frac(lambda r, R=R: r["G"][R] > 1e-9)
        summary[f"frac_nest_price_R{R}_pos_m_ge7"] = frac(lambda r, R=R: r["G"][R] > 1e-9, sub=lambda r: r["m"] >= 7)
    summary["mean_rel_score_price_R0_given_matter"] = frac(lambda r: r["price_score"][0] / r["spread"], sub=lambda r: r["spread"] > 1e-9)
    summary["mean_rel_nest_price_R0_given_matter"] = frac(lambda r: r["G"][0] / r["spread"], sub=lambda r: r["spread"] > 1e-9)
    checks = [{"name": "subset_frontier / zero-price / monotonicity / G <= score transcription", "ok": all_ok},
              {"name": "oracle rollouts deterministic", "ok": det_ok},
              {"name": "at least one record", "ok": len(recs) > 0}]
    rec = {"producer": "scripts/DIAG_cityflow_set_objective_hops.py",
           "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "env_module_sha256": hashlib.sha256((ROOT / "envs/external/cityflow_budgeted.py").read_bytes()).hexdigest(),
           "env_hops_module_sha256": hashlib.sha256((ROOT / "envs/external/cityflow_budgeted_hops.py").read_bytes()).hexdigest(),
           "evidence_class": "ORACLE DIAGNOSTIC (frozen two-step max-pressure; oracle rollouts; not a learned policy)",
           "mode": mode, "configs": configs, "H": H, "lambda": LAMBDA, "summary": summary, "checks": checks,
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
