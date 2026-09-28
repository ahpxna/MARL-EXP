# PROTOCOL v0 — Budget-adaptive coordination with limited revision (CityFlow)

Status 2026-09-27:
- The environment is implemented (`envs/external/cityflow_budgeted.py`).
- The leak tests pass 17/17 (`tests/test_cityflow_budgeted.py`).
- The real-engine smoke passes 24/24 (`research/marl_budget/P3_cityflow/smoke_20260927/smoke_result_v2.json`,
  log `work/run_logs/cityflow_smoke_20260927_v2.log`).
- No learning has been run. Nothing below is a result.

## 1. The question the experiment answers

The theory (Lean, `LeanMarlRevisionFrontierV1`, `LeanMarlNestingDegreeGeneralV1`) separates two
prices of a universal (nested) message priority:

- **(i) Price of a first-order-score priority.**
  - It is at most (d_k − R)₊·δ, where d_k = |prefix_k \ T_k|.
  - It is zero at every budget when every cut margin of the scores is ≥ 2δ.
  - It is sharp on D6's Vb family.
- **(ii) Price of nesting itself.** This is the best universal order, and it is combinatorial:
  - 0 or 1 revisions suffice for m ≤ 6 neighbours, for any loss;
  - ⌊(m+1)/4⌋ revisions are forced in the worst case.

Here δ is the i-versus-REST mixed difference of the team objective (`mixedDifference F i x c`),
**not** a pairwise one. The pairwise version is reported only as a lower-bound diagnostic.

**Prediction to test.**
- On states where the measured score margin is ≥ 2δ, a universal ranking (R = 0) matches the
  budget-aware selector.
- Where δ/margin is large, R = 1, 2 revisions recover most of the gap, at a measured latency cost.
- A result that contradicts this is reported as a negative result. The protocol does not inject
  a favourable regime.

## 2. Agents, observations, messages (information access is enforced)

- **Agents.** The non-virtual intersections of a rows×cols CityFlow grid, built by the pinned
  generator (`make_grid_scenario`). The smoke uses 3×3: 9 agents with 9 phases each; phase 0 is
  a 5 s clearance and is not a valid action.
- **Own sensor.** Vehicles and waiting counts on the intersection's OWN incoming lanes only,
  4 approach slots. Sensors are disjoint, so downstream state reaches i only by message.
  - This differs from the old `envs/external/cityflow.py`. Its sensor overlaps neighbours, and
    its `relation_features` reads neighbours' fresh observations.
  - It also differs from `models/core_behavior.py:474–495`, which reads every neighbour's
    obs/action. Neither may be used in the communication-limited track.
- **Message.** A 25-byte payload:
  - sender, measurement time, phase, phase-elapsed;
  - 4 × (vehicles, waiting).

  It is encoded to bytes and decoded at the receiver. A request costs 8 bytes.
- **Absent messages.** Agent i keeps the last message received from j, with its age. There is
  never a fresh hidden observation. "Never heard" is explicit.
- **Views.** `AgentView` is frozen and read-only. It contains only the own sensor, the inbox,
  the cache with ages, the budget (after the reveal), the own ranking and final set, and R.

## 3. Budget process and the revision interface

For each decision step (10 s of simulation), the stage machine enforces:

1. `views()`: the budget is hidden.
2. `commit_rankings`: a permutation of N(i), the universal priority.
3. `reveal_budget`: k_t is revealed. Traces are fixed, drops (geometric), bursty
   (Gilbert–Elliott) or per-episode; they are common or per-agent, seeded separately from
   traffic.
4. `submit_final_sets`: |T| = min(k, |N(i)|) with |prefix_k \ T| ≤ R. R = None means an
   unrestricted budget-aware selection.
5. `transmit`: the bytes are delivered, with an optional delay.
6. `step(actions)`.

Revision happens BEFORE transmission. Transmitted bytes are never refunded.

## 4. The set-valued team objective (for δ and the margins)

- Q(s, S) must be **the value of the decision taken with the heard set S, evaluated at the true
  state**:
  - the frozen actor acts on the view that would result from hearing S (`counterfactual_view`,
    oracle mode);
  - its joint action is scored by an oracle rollout (`oracle_rollout_value`: clone, apply, hold
    phases H decisions, return −Σ waiting, restore) or by a full-information critic.
- It must NOT be a critic's value estimate from the partial view. Bad news lowers that estimate
  while improving the decision.
- From Q(s, ·) over subsets of N(i), for small neighbourhoods (|N(i)| ≤ 4 on a grid):
  - response spans (first-order scores) and cut margins;
  - δ as the i-versus-rest mixed difference;
  - the exact per-budget optima and the nesting degree of the optimal system;
  - D6's loss when the D6 bridge is used.

  `models/set_critic_probe.py` implements these transcriptions. It has been hand-checked, and a
  test file is still owed.
- Oracle access is available only in `mode="oracle"`, is logged in `access_log`, and raises in
  deploy mode. A diagnostic that uses it is labelled ORACLE DIAGNOSTIC and never selects
  deployed actions.

## 5. Policies compared (same actor, same seeds, same budgets)

- **Matched-component track.** A frozen actor; only the message selector changes:
  1. full communication (upper reference); no communication (lower reference);
  2. random ranking; attention/score ranking in the CoLight style, R = 0;
  3. the same ranking + R = 1, R = 2 revisions;
  4. a budget-conditioned subset selector (no nesting restriction, R = None);
  5. an exhaustive subset oracle on small neighbourhoods (ORACLE, retrospective only).
- **Complete-algorithm track.** Reproduced external comparators (CoLight, CoSLight,
  MUTE-style pruning, a SchedNet/ETC scheduler), with their adaptations labelled.

## 6. Metrics and statistics

- **Traffic:**
  - mean travel time of finished vehicles, with unfinished vehicles reported separately
    (CityFlow's `get_average_travel_time` is censored);
  - queue;
  - throughput per hour.
- **Resources:**
  - payload and request bytes, messages;
  - revisions;
  - stale-message age (mean/max), never-heard pairs;
  - selector and actor wall-clock time.
- **Theory diagnostics** (oracle, labelled): δ, margins, and d_k per state; the fraction of
  states in the zero-price regime; the realised versus predicted revision gain.
- **Statistics:**
  - traffic seeds are paired across policies (identical arrivals: in the smoke, R = 0/1/None
    give identical traffic under a sensor-only actor);
  - training seeds are independent units;
  - unfinished and timed-out vehicles stay in the denominators.

## 7. What is NOT claimed

- No theorem covers expected return. The Lean results are about the set objective. The
  return bridge is the standard, conditional performance-difference argument.
- One budget reveal per decision step. Repeated switching is an empirical stress test, not a
  theorem.
- The smoke's heuristic policy is plumbing only.

## 7b. First oracle diagnostic (done, 2026-09-27)

`research/marl_budget/diag_20260927/set_objective_full.json`: 1180 tables, all self-checks pass.
- In one-hop grid signal control under message-using max-pressure, 82% of states are in the
  2δ-margin zero-price regime.
- The score-priority price is positive in 4.7% of states, and R = 1 removes all of it.
- The nesting price is essentially absent (0.17% at R = 0, none at R = 1), as the
  nesting-degree theorem forces for m ≤ 6.

The candidate set must therefore grow (m ≥ 7) before revision can matter: 2-hop or per-lane
packets, a learned policy, or vehicle-level V2X.

## 8. Next steps

1. `tests/test_set_critic_probe.py`, turning aa4bdbe's hand checks into tests that can fail.
2. An oracle-diagnostic script: over frozen states from a fixed-time or max-pressure
   controller, compute δ, the margins, the optimal systems and the nesting degrees per
   intersection. This measures whether regimes (i) and (ii) occur in traffic at all, before any
   learning.
3. Train a common budget-conditioned actor (sampled budgets) with a rank head and a bounded
   exchange head. Compare with the budget-conditioned selector and the per-budget oracle.
