#!/usr/bin/env python3
"""SMOKE (not an experiment): the budgeted CityFlow environment on a real engine.

What this checks, and nothing more:
* a 3x3 CityFlow grid builds from the pinned generator and runs under
  envs/external/cityflow_budgeted.py for a few decisions;
* the protocol stage machine (rank -> reveal -> revise -> transmit -> act) runs end to end
  with R = 0, R = 1 and R = None (budget-aware);
* information-access invariants report no violation;
* in oracle mode one set-valued measurement runs and leaves the state unchanged.

The policy is a fixed heuristic.  It is NOT a learned MARL policy, and nothing here is a
performance result.
- Ranking: neighbours by the queue in their last received message; never-heard first.
- Revision: swap the oldest-heard prefix member for the most stale outsider.
- Action: the valid phase that serves the most waiting vehicles on the own sensor.

Usage, from the repo root:
  CIG_EXTERNAL_RUNTIME_ACTIVE=1 external_envs/runtime/bin/python -u scripts/SMOKE_cityflow_budgeted.py
Output: research/marl_budget/P3_cityflow/smoke_20260927/{scenario_seed*, smoke_result.json}.
The script refuses to overwrite either output.
"""
from __future__ import annotations

import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import numpy as np  # noqa: E402

from envs.external.cityflow_budgeted import (  # noqa: E402
    BudgetTraceSpec, make_budgeted_grid_env, make_grid_scenario, run_protocol_step, view_fingerprint,
)

OUT = ROOT / "research/marl_budget/P3_cityflow/smoke_20260927"
# v2 (2026-09-27): the v1 state-restore check compared clone_state() snapshots with
# json.dumps(default=str), i.e. by object address, so it could never pass.  v2 compares the
# agents' view fingerprints before and after the rollouts instead.  v1's output is kept.
TAG = sys.argv[1] if len(sys.argv) > 1 else "v1"


class HeuristicPolicy:
    """Fixed, non-learned policy for plumbing checks only."""

    def rank(self, view, topo):
        def key(j):
            e = view.message_from(j)
            if e is None:
                return (0, 0.0, j)          # never heard: first
            return (1, -float(sum(e.payload.waiting)), j)
        return sorted(view.neighbours, key=key)

    def revise(self, view, ranking, k, R):
        k = min(int(k), len(ranking))
        prefix = list(ranking[:k])
        if R is None:                        # budget-aware: the k most stale
            def age(j):
                e = view.message_from(j)
                return float("inf") if e is None else e.age
            return sorted(view.neighbours, key=lambda j: (-age(j), j))[:k]
        if R == 0 or k == 0 or k == len(ranking):
            return prefix
        outside = [j for j in ranking if j not in prefix]
        def age(j):
            e = view.message_from(j)
            return float("inf") if e is None else e.age
        stale_out = max(outside, key=lambda j: (age(j), -j))
        drop = min(prefix, key=lambda j: (age(j), j))
        if age(stale_out) > age(drop):
            prefix[prefix.index(drop)] = stale_out
        return prefix

    def act(self, view, topo):
        best, best_val = None, -1.0
        wait = np.asarray(view.lane_waiting).sum(axis=1)
        for p in topo.valid_phases:
            slots = {s for (s, _road) in topo.phase_movements[p]}
            val = float(sum(wait[s] for s in slots))
            if val > best_val:
                best, best_val = p, val
        return int(best)


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    res_path = OUT / ("smoke_result.json" if TAG == "v1" else f"smoke_result_{TAG}.json")
    if res_path.exists():
        print(f"refusing to overwrite {res_path}", file=sys.stderr)
        return 2
    OUT.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    policy = HeuristicPolicy()
    runs = []
    checks = []
    for seed in (1, 2):
        scen = make_grid_scenario(OUT / (f"scenario_seed{seed}" if TAG == "v1" else f"scenario_seed{seed}_{TAG}"), rows=3, cols=3, traffic_seed=seed,
                                  horizon_s=400, mean_headway_s=12.0)
        print(f"seed {seed}: scenario with {scen['n_vehicles']} vehicles ({time.time()-t0:.1f}s)", flush=True)
        for R in (0, 1, None):
            env = make_budgeted_grid_env(scen, budget_spec=BudgetTraceSpec(kind="bursty", k=2, k_low=0),
                                         R=R, n_decisions=30, action_interval=10, mode="deploy")
            env.reset(budget_seed=100 + seed)
            viol = []
            done = False
            while not done:
                _, done, rec = run_protocol_step(env, policy, audit=True)
                viol += rec["violations"]
            summ = env.episode_summary()
            runs.append({"seed": seed, "R": R, "summary": summ, "violations": viol[:5],
                         "n_violations": len(viol)})
            print(f"  R={R}: decisions={summ['decisions']} finished={summ['finished_vehicles']} "
                  f"queue_mean={summ['queue_mean']:.2f} bytes={summ['payload_bytes']} "
                  f"revisions={summ['revisions']} stale_mean={summ['stale_age_mean_over_steps']} "
                  f"violations={len(viol)} oracle_used={summ['oracle_access_used']}", flush=True)
            checks.append({"name": f"seed{seed} R={R}: no access violation", "ok": len(viol) == 0})
            checks.append({"name": f"seed{seed} R={R}: no oracle access in deploy", "ok": not summ["oracle_access_used"]})
            checks.append({"name": f"seed{seed} R={R}: ran all decisions", "ok": summ["decisions"] == 30})
            if R == 0:
                checks.append({"name": f"seed{seed} R=0: zero revisions", "ok": summ["revisions"] == 0})
    # One oracle-mode measurement: the set-valued rollout value at one state, and restore.
    scen = make_grid_scenario(OUT / ("scenario_oracle" if TAG == "v1" else f"scenario_oracle_{TAG}"), rows=3, cols=3, traffic_seed=3, horizon_s=400)
    env = make_budgeted_grid_env(scen, budget_spec=BudgetTraceSpec(kind="fixed", k=2), R=1,
                                 n_decisions=5, mode="oracle")
    env.reset(budget_seed=7)
    for _ in range(2):
        run_protocol_step(env, policy, audit=True)
    before = {i: view_fingerprint(v) for i, v in env.views().items()}
    t_before = env._engine.get_current_time()
    acts = {i: int(env.public_topology(i).valid_phases[0]) for i in range(env.n_agents)}
    v1 = env.oracle_rollout_value(acts, horizon_decisions=3)
    v2 = env.oracle_rollout_value(acts, horizon_decisions=3)
    after = {i: view_fingerprint(v) for i, v in env.views().items()}
    same = (before == after) and (env._engine.get_current_time() == t_before)
    checks.append({"name": "oracle rollout is deterministic", "ok": v1 == v2})
    checks.append({"name": "oracle rollout restores state", "ok": bool(same)})
    checks.append({"name": "oracle access is logged", "ok": env.access_log["oracle_rollout"] == 2})
    # the check can fail: a rollout WITHOUT restore must change the fingerprints
    for _ in range(3 * env.action_interval):
        env._engine.next_step()
    env._read_lanes()
    moved = {i: view_fingerprint(v) for i, v in env.views().items()} != before
    checks.append({"name": "control: advancing the engine changes the fingerprints", "ok": bool(moved)})
    print(f"oracle: rollout value {v1} (repeat {v2}), state restored={same}, access_log={env.access_log}",
          flush=True)
    ok = all(c["ok"] for c in checks)
    rec = {"producer": "scripts/SMOKE_cityflow_budgeted.py", "source_sha256": sha(Path(__file__)),
           "env_module_sha256": sha(ROOT / "envs/external/cityflow_budgeted.py"),
           "evidence_class": "SMOKE (plumbing only; heuristic policy; not a result)",
           "checks": checks, "all_ok": ok, "runs": runs, "seconds": time.time() - t0}
    res_path.write_text(json.dumps(rec, indent=1, default=str), encoding="utf-8")
    print(f"checks {sum(c['ok'] for c in checks)}/{len(checks)} ok; wrote {res_path} ({time.time()-t0:.1f}s)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
