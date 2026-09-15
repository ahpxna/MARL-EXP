"""QUERY step 1+2: natural reachable panel on RWARE with COMPLETE inclusion accounting.

This is a NEW probe written for the QUERY package.  It is a corrected and
extended replacement for scripts/query_natural_panel_collect.py, which crashes
(`TypeError: int() argument ... not 'Direction'`, rware Agent.dir is an Enum) and
therefore has never produced an artifact.

Supervisor ordering implemented here:
  (1) collect trajectories with a FIXED collection policy,
  (2) keep every count: generated / reachable / filtered / constant / evaluable.

Nothing in this file inspects a query outcome before deciding whether to keep a
state.  The collection policy is a declared, deterministic, STATE-ONLY greedy
delivery heuristic; it is frozen before any query is computed and it is also the
frozen continuation policy rho used for the horizon-h targets, so the
continuation and the behaviour that generated the state are the same object.

All environment rewards in this RWARE configuration are integers (RewardType.GLOBAL
adds exactly 1 to every agent per delivered request), so every response/return
written by this script is an exact integer.  Floats appear only inside the
purchasable feature catalog, where they are used as EXACT BIT KEYS for a
partition (equality of identical float64 values is exact); no float comparison
with a tolerance ever decides a reported number.

Two extra things this probe records that the older script did not, both of which
exist to make the later claim FALSIFIABLE:

  * ``physical_key`` -- a canonical key for the full physical warehouse state
    (all agents, all shelves, request queue, step/inactivity counters).  The
    horizon-h return is a deterministic function of (physical_key, rng_key), so
    a bad pair with an identical physical_key is NOT evidence of representation
    loss -- it is environment stochasticity (RWARE draws a replacement request
    from np_random on every delivery).  Without this key that confound cannot
    be excluded.
  * ``rng_key`` -- a hash of the numpy bit generator state at the snapshot.

Usage: see the findings file for the exact re-run command.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import numpy as np  # noqa: E402

from envs.external.runtime import maybe_reexec_in_external_runtime  # noqa: E402

PROTOCOL = "QUERY_natural_panel_v2_fixed_greedy_delivery_collection"
N_ACTIONS = 5
NOOP, FORWARD, LEFT, RIGHT, TOGGLE = 0, 1, 2, 3, 4
# RWARE Direction: UP=0, DOWN=1, LEFT=2, RIGHT=3.  Screen coordinates: y grows down.
DIR_DELTA = {0: (0, -1), 1: (0, 1), 2: (-1, 0), 3: (1, 0)}
DELTA_DIR = {v: k for k, v in DIR_DELTA.items()}
# Clockwise order of directions as RWARE's Action.RIGHT rotates them.
CW = [0, 3, 1, 2]  # UP -> RIGHT -> DOWN -> LEFT


def _dirval(d):
    return int(getattr(d, "value", d))


# --------------------------------------------------------------------------
# FIXED COLLECTION POLICY  (also used as the frozen continuation policy rho)
# --------------------------------------------------------------------------

def _shelf_layer(w):
    from rware.warehouse import _LAYER_SHELFS  # type: ignore
    return w.grid[_LAYER_SHELFS]


def _bfs_step(w, start, targets, blocked):
    """First grid step of a shortest path from ``start`` to the nearest target.

    Deterministic: neighbours are expanded in a fixed order and ties are broken
    by that expansion order.  Returns None when no target is reachable, and
    ``start`` when already on one.
    """
    h, wd = w.grid_size
    if start in targets:
        return start
    seen = {start}
    queue = collections.deque()
    for dx, dy in ((0, -1), (0, 1), (-1, 0), (1, 0)):
        nx_, ny_ = start[0] + dx, start[1] + dy
        if not (0 <= nx_ < wd and 0 <= ny_ < h):
            continue
        if (nx_, ny_) in blocked:
            continue
        seen.add((nx_, ny_))
        queue.append(((nx_, ny_), (nx_, ny_)))
    while queue:
        cell, first = queue.popleft()
        if cell in targets:
            return first
        for dx, dy in ((0, -1), (0, 1), (-1, 0), (1, 0)):
            nb = (cell[0] + dx, cell[1] + dy)
            if not (0 <= nb[0] < wd and 0 <= nb[1] < h):
                continue
            if nb in seen or nb in blocked:
                continue
            seen.add(nb)
            queue.append((nb, first))
    return None


def _turn_action(cur_dir, want_dir):
    if cur_dir == want_dir:
        return FORWARD
    i, j = CW.index(cur_dir), CW.index(want_dir)
    return RIGHT if (j - i) % 4 <= (i - j) % 4 else LEFT


def greedy_delivery_action(env, agent_index):
    """Declared fixed collection policy. Deterministic function of the state only."""
    w = env.raw_env
    shelf_layer = _shelf_layer(w)
    agent = w.agents[int(agent_index)]
    pos = (int(agent.x), int(agent.y))
    carrying = agent.carrying_shelf
    requested = {(int(s.x), int(s.y)) for s in w.request_queue}
    goals = {(int(gx), int(gy)) for gx, gy in w.goals}

    if carrying is not None and any(carrying is s for s in w.request_queue):
        targets, on_target_action = goals, NOOP  # delivery fires on arrival
    elif carrying is not None:
        free = set()
        h, wd = w.grid_size
        for y in range(h):
            for x in range(wd):
                if not w.highways[y, x] and not shelf_layer[y, x]:
                    free.add((x, y))
        if not free:
            return NOOP
        targets, on_target_action = free, TOGGLE
    else:
        if not requested:
            return NOOP
        targets, on_target_action = requested, TOGGLE

    if pos in targets:
        return on_target_action

    blocked = set()
    if carrying is not None:
        h, wd = w.grid_size
        for y in range(h):
            for x in range(wd):
                if shelf_layer[y, x] and (x, y) != pos:
                    blocked.add((x, y))
    step = _bfs_step(w, pos, targets, blocked)
    if step is None or step == pos:
        return NOOP
    delta = (step[0] - pos[0], step[1] - pos[1])
    want = DELTA_DIR.get(delta)
    if want is None:
        return NOOP
    return _turn_action(_dirval(agent.dir), int(want))


def joint_collection_action(env):
    return [int(greedy_delivery_action(env, i)) for i in range(int(env.n_agents))]


# --------------------------------------------------------------------------
# STATE KEYS  (used to separate representation loss from environment noise)
# --------------------------------------------------------------------------

def physical_key(env):
    w = env.raw_env
    agents = tuple(
        (int(a.x), int(a.y), _dirval(a.dir),
         int(a.carrying_shelf.id) if a.carrying_shelf is not None else 0,
         int(bool(a.has_delivered)))
        for a in w.agents
    )
    shelves = tuple(sorted((int(s.id), int(s.x), int(s.y)) for s in w.shelfs))
    requested = tuple(sorted(int(s.id) for s in w.request_queue))
    counters = (int(getattr(w, "_cur_steps", -1)), int(getattr(w, "_cur_inactive_steps", -1)))
    blob = json.dumps([agents, shelves, requested, counters], sort_keys=True)
    return hashlib.sha256(blob.encode()).hexdigest()[:24]


def rng_key(env):
    w = env.raw_env
    try:
        state = w.np_random.bit_generator.state
    except Exception:  # noqa: BLE001
        return "NA"
    blob = json.dumps(state, sort_keys=True, default=str)
    return hashlib.sha256(blob.encode()).hexdigest()[:24]


# --------------------------------------------------------------------------
# EXACT PANEL (integer returns, gamma = 1)
# --------------------------------------------------------------------------

def _rollout_return(env, snapshot, horizon, forced=None):
    """Integer h-step return of the GLOBAL reward under rho = collection policy."""
    env.restore_state(snapshot)
    total = 0
    taken = 0
    done = False
    for t in range(int(horizon)):
        actions = joint_collection_action(env)
        if forced is not None and t == 0:
            actions[int(forced[0])] = int(forced[1])
        _, rewards, done, _ = env.step(actions)
        total += int(round(float(rewards[0])))
        taken += 1
        if done:
            break
    return total, taken, bool(done)


def response_panel(env, snapshot, candidates, horizon):
    rows, steps, dones = [], 0, []
    for j in candidates:
        row, drow = [], []
        for a in range(N_ACTIONS):
            value, taken, done = _rollout_return(env, snapshot, horizon, forced=(j, a))
            row.append(int(value))
            drow.append(int(done))
            steps += taken
        rows.append(tuple(row))
        dones.append(tuple(drow))
    env.restore_state(snapshot)
    return tuple(rows), steps, tuple(dones)


def coalition_table(env, snapshot, candidates, baseline, horizon):
    """Exact 2^|J| noop-coalition table of h-step returns."""
    import itertools
    values, steps = {}, 0
    for bits in itertools.product((0, 1), repeat=len(candidates)):
        active = tuple(i for i, b in enumerate(bits) if b)
        env.restore_state(snapshot)
        total, done = 0, False
        for t in range(int(horizon)):
            actions = joint_collection_action(env)
            if t == 0:
                for local, agent in enumerate(candidates):
                    actions[agent] = int(baseline[agent]) if bits[local] else NOOP
            _, rewards, done, _ = env.step(actions)
            total += int(round(float(rewards[0])))
            steps += 1
            if done:
                break
        values[active] = int(total)
    env.restore_state(snapshot)
    return values, steps


# --------------------------------------------------------------------------
# CATALOG (executable; each item is a real adapter call with a declared cost)
# --------------------------------------------------------------------------

def _fkey(array):
    return tuple(float(x) for x in np.asarray(array).reshape(-1))


def catalog_features(env, snapshot, outcome, candidates):
    env.restore_state(snapshot)
    out = {}
    out["relation_features"] = (
        [list(_fkey(env.relation_features(outcome, j))) for j in candidates],
        {"model_forward_passes": len(candidates)},
    )
    out["mechanism_features"] = (
        [list(_fkey(env.mechanism_features(j))) for j in candidates],
        {"model_forward_passes": len(candidates)},
    )
    out["weak_prior_score"] = (
        [float(env.weak_prior_score(outcome, j)) for j in candidates],
        {"model_forward_passes": len(candidates)},
    )
    w = env.raw_env
    requested = {(int(s.x), int(s.y)) for s in w.request_queue}
    goals = [(int(gx), int(gy)) for gx, gy in w.goals]
    geom = []
    for j in candidates:
        a = w.agents[int(j)]
        carrying = a.carrying_shelf
        carrying_requested = int(carrying is not None and any(carrying is s for s in w.request_queue))
        dgoal = min(abs(int(a.x) - gx) + abs(int(a.y) - gy) for gx, gy in goals)
        dreq = (min(abs(int(a.x) - rx) + abs(int(a.y) - ry) for rx, ry in requested)
                if requested else -1)
        geom.append([int(a.x), int(a.y), _dirval(a.dir), int(carrying is not None),
                     carrying_requested, int(dgoal), int(dreq)])
    out["privileged_geometry"] = (geom, {"privileged_state_reads": 1})
    env.restore_state(snapshot)
    return out


# --------------------------------------------------------------------------
# COLLECTION
# --------------------------------------------------------------------------

def collect(seeds, n_agents, episode_len, cadence, horizon_target, candidates_n,
            coalition_horizon, burn_in):
    from envs.external.registry import build_environment

    counts = collections.Counter()
    records = []
    outcome = 0
    candidates = list(range(1, candidates_n + 1))
    env = build_environment("rware", seed=int(seeds[0]), n_agents=int(n_agents))

    for seed in seeds:
        env.reset(seed=int(seed))
        counts["episodes"] += 1
        for t in range(int(episode_len)):
            counts["generated_steps"] += 1
            snapshot_here = (t >= int(burn_in)) and ((t - int(burn_in)) % int(cadence) == 0)
            if snapshot_here:
                counts["reachable_snapshots"] += 1
                snapshot = env.clone_state()
                pkey, rkey = physical_key(env), rng_key(env)
                try:
                    baseline = joint_collection_action(env)
                    rows1, c1, d1 = response_panel(env, snapshot, candidates, 1)
                    rows2, c2, d2 = response_panel(env, snapshot, candidates, 2)
                    rowsT, cT, dT = response_panel(env, snapshot, candidates, horizon_target)
                    coal, cc = coalition_table(env, snapshot, candidates, baseline,
                                               coalition_horizon)
                    feats = catalog_features(env, snapshot, outcome, candidates)
                except Exception as exc:  # noqa: BLE001
                    counts["filtered_panel_error"] += 1
                    records.append({"seed": int(seed), "t": int(t), "status": "FILTERED",
                                    "reason": f"{type(exc).__name__}: {exc}"})
                    env.restore_state(snapshot)
                else:
                    counts["panel_built"] += 1
                    records.append({
                        "seed": int(seed), "t": int(t), "status": "OK",
                        "physical_key": pkey, "rng_key": rkey,
                        "baseline": [int(x) for x in baseline],
                        "R1": [list(r) for r in rows1],
                        "R2": [list(r) for r in rows2],
                        "RT": [list(r) for r in rowsT],
                        "doneT": [list(r) for r in dT],
                        "coalition": {",".join(map(str, k)): int(v) for k, v in coal.items()},
                        "catalog": {k: v[0] for k, v in feats.items()},
                        "catalog_cost": {k: v[1] for k, v in feats.items()},
                        "env_steps": int(c1 + c2 + cT + cc),
                    })
                    env.restore_state(snapshot)
            actions = joint_collection_action(env)
            _, rewards, done, _ = env.step(actions)
            counts["collection_reward"] += int(round(float(rewards[0])))
            if done:
                counts["episode_terminated_early"] += 1
                break
    return records, counts


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--seeds", type=int, nargs="+",
                   default=list(range(20260912, 20260912 + 12)))
    p.add_argument("--n-agents", type=int, default=5)
    p.add_argument("--episode-len", type=int, default=60)
    p.add_argument("--cadence", type=int, default=3)
    p.add_argument("--burn-in", type=int, default=0)
    p.add_argument("--horizon-target", type=int, default=6)
    p.add_argument("--coalition-horizon", type=int, default=6)
    p.add_argument("--candidates", type=int, default=4)
    p.add_argument("--out", default="research/high_risk_20260910/QUERY_natural_panel_v2.json")
    a = p.parse_args(argv)
    maybe_reexec_in_external_runtime(require_ready=True)
    records, counts = collect(a.seeds, a.n_agents, a.episode_len, a.cadence,
                              a.horizon_target, a.candidates, a.coalition_horizon,
                              a.burn_in)
    payload = {
        "protocol": PROTOCOL,
        "evidence_class": "NATURAL_REACHABLE_PANEL_FIXED_COLLECTION_POLICY",
        "collection_policy": (
            "greedy_delivery: deterministic, state-only. If carrying a requested shelf -> "
            "BFS to nearest goal cell; if carrying a non-requested shelf -> BFS to nearest "
            "free storage slot then TOGGLE_LOAD; else BFS to nearest requested shelf then "
            "TOGGLE_LOAD. Rotation chosen by the shorter turn, ties -> LEFT. No RNG, no "
            "query outcome is consulted."),
        "continuation_policy": "rho = the same greedy_delivery collection policy",
        "state_selection": (
            "every cadence-th step of every episode from burn_in onward; NO filtering by any "
            "query outcome; panel-construction failures are recorded, not dropped"),
        "adapter": "rware", "n_agents": a.n_agents,
        "candidates": list(range(1, a.candidates + 1)),
        "outcome_agent": 0, "seeds": list(map(int, a.seeds)),
        "episode_len": a.episode_len, "cadence": a.cadence, "burn_in": a.burn_in,
        "horizon_target": a.horizon_target, "coalition_horizon": a.coalition_horizon,
        "discount": 1, "arithmetic": "integer returns throughout",
        "counts": dict(counts),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "records": records,
    }
    out = ROOT / a.out
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp = out.with_suffix(".tmp")
    tmp.write_text(json.dumps(payload, indent=1) + "\n")
    tmp.replace(out)
    print(json.dumps({"counts": dict(counts), "records": len(records), "out": str(out)}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
