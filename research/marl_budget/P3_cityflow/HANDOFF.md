# P3 CityFlow — handoff (2026-09-27, wrap-up order)

## Files created (all new; no existing file edited)

| File | Status |
|---|---|
| `envs/external/cityflow_budgeted.py` | Done. Unit-tested against an engine double. **Never run on real CityFlow yet.** |
| `tests/test_cityflow_budgeted.py` | **17/17 pass**: `.venv/bin/python -m pytest -q tests/test_cityflow_budgeted.py -p no:cacheprovider` (0.32 s) |
| `models/set_critic_probe.py` | Written. Sanity-checked by hand, but there is no test file; see below. |
| `research/marl_budget/P3_cityflow/{COMPACT,PROGRESS,HANDOFF}.md` | Notes |

### What `cityflow_budgeted.py` does

**Agents and sensors**
- Agents are the non-virtual intersections.
- The own sensor covers **incoming lanes only**: 4 approach slots × lanes, vehicles and
  waiting. So sensors are disjoint, and downstream occupancy reaches `i` only by message.

**Message and codec**
- The message is the sender's local summary, 25 bytes (`struct "<HIBH8H"`):
  - sender uint16, `measured_at` uint32 (simulator seconds);
  - phase uint8, phase-elapsed uint16;
  - 4 × (vehicles uint16, waiting uint16).
- A request costs 8 bytes. Out-of-range values are clipped and the clipped fields counted.

**Budget traces**
- `BudgetTraceSpec` supports fixed, drops (geometric durations), bursty (Gilbert–Elliott)
  and per_episode.
- The trace is common to all receivers, or per agent.
- Each trace is seeded separately from the traffic, so seeds can be paired.

**Stage machine**
- The order is `views → commit_rankings → reveal_budget → submit_final_sets → transmit → step`.
  Any other order raises.
- Rankings must be permutations of N(i).
- A final set must have |T| = min(k, |N(i)|) and satisfy |prefix_k \ T| ≤ R
  (R = None means an unrestricted, budget-aware selection).
- Messages travel as encoded bytes and are decoded at the receiver. An optional
  `delivery_delay`, in decision steps, is supported.
- Each cache entry holds `measured_at`, its age and the step it was delivered.

**`AgentView`**
- It is a frozen dataclass holding only numbers, tuples and read-only arrays.
- It carries the own sensor, the inbox for this step, the older cache entries, `never_heard`,
  the budget (None before the reveal), the past budgets, and its own committed ranking and
  final set.
- `PublicTopology` holds static facts only.

**Oracle mode (`mode="oracle"`)**
- It provides `counterfactual_view(i, S)`, which gives the view as if S were heard now,
  uncharged, in order to evaluate Q(s,S) for every S.
- It also provides `oracle_payloads`, `clone_state`/`restore_state` and
  `oracle_rollout_value`: apply the joint action, hold the phases for H decisions, and
  return −Σ waiting.
- Every call is counted in `access_log`, and `episode_summary` sets `oracle_access_used`.
- In deploy mode all of these raise `PermissionError`.

**Metrics** (`step_records`, `episode_summary`)
- queue, throughput, and finished-vehicle travel time (entry and exit tracked every
  simulator second);
- CityFlow's `get_average_travel_time`, labelled censored because it counts running vehicles
  at their elapsed time;
- payload and request bytes, messages, revisions, stale-age mean/max, never-heard pairs;
- selector and actor wall-clock time, recorded by `run_protocol_step`;
- `check_access_invariants` violations.

**Scenarios**
- `make_grid_scenario` builds a rows×cols grid through the pinned `tools/generator`
  (`gridToRoadnet`, `generate_route`), imported read-only.
- Arrivals are seeded Poisson, one flow per vehicle. The call refuses to overwrite an
  existing directory.
- `make_budgeted_grid_env` requires `CIG_EXTERNAL_RUNTIME_ACTIVE=1` and imports `cityflow`
  lazily.

### Tests that can fail

The non-interference test runs two engine doubles that differ only in neighbour l2's FRESH
lanes. When l2 is not in agent 0's final set, agent 0's canonical view bytes must be identical
at every stage over three steps. Two controls show the test has teeth:
- **Positive control:** when l2 is transmitted, the views differ at the "act" stage but not at
  "rank" or "revise".
- **Mutation control:** `_LeakyEnv` adds neighbours' fresh sensor readings to the view, which
  is the old adapter's `relation_features` pattern. The test detects it.

The file also covers:
- that stage order is enforced;
- that the budget stays hidden before the reveal;
- R and |T| enforcement;
- permutation checks;
- bytes = 25 per message plus 8 per request;
- that phase 0 (clearance) is rejected;
- that oracle entry points raise in deploy mode;
- that oracle calls leave the state byte-identical;
- clean invariants on a bursty R=1 run;
- that views are immutable;
- the codec round-trip with clipping;
- that traces are deterministic and typed.

### `set_critic_probe.py` (untested file; a hand check was run)

It transcribes the D6 objects from LeanProductMixedDifferenceV4 and LeanSupportGeometryV4:
`jointWeight`, `productResponse`, osc score, `mixedDifference`, and `productCompressionLoss`.
`check_margin_two` transcribes `margin_two_sufficient`. The module also provides the subset
objective (`revision_price`, `delta_pair`) and `check_exchange_bound`.

Hand check (`python -c`, nothing written):

| Instance | δ | δ_pair | Violations | Other results |
|---|---|---|---|---|
| Additive F | 0 | — | 0 | — |
| XOR game of Decision 5 (p=1/4) | 0.5 | 0.5 | 0 | price 0.25 at k=2, R=0; 0 at R=1 (matches the memo) |
| 300 random F on {0,1}^4 | — | — | 0 on both checks | — |

## Findings for main

1. **The old adapter has a second free channel.**
   - `envs/external/cityflow.py` builds the sensor from `item["roads"]`, which holds incoming
     and outgoing roads. Neighbour observations therefore overlap.
   - Its `relation_features(ego, j)` reads the neighbour's FRESH `_obs[j]` (`load_diff`,
     `wait_diff`). This comes on top of the `core_behavior.py:474–495` reads.
2. **D6's δ is i-versus-REST, not pairwise.** `mixedDifference F i x c` =
   F x − F(x[i:=c_i]) − F(c[i:=x_i]) + F c, with x and c full vectors. The pairwise
   subset mixed difference is only a lower bound on it. The protocol must name the theorem's δ
   and report δ_pair as a diagnostic.
3. **The right Q(s,S).** Q(s,S) must be the value of the DECISION taken with S, evaluated at
   the true state (frozen actor, then a full-information critic or an oracle rollout). It must
   not be a critic's value estimate from the partial view: bad news lowers that estimate while
   it improves the decision.
4. **An elementary revision bound for the subset objective** (my derivation, NOT in Lean).
   - Setting: g_j = F({j}) − F(∅), and δ is the D6 bound on {0,1}^n with a point reference.
   - Then |F(A∪i) − F(A) − g_i| ≤ δ.
   - An exchange chain gives, for the gain-ranking prefix P_k:
     best_k − best_{|P_k\T|≤R} ≤ 2δ·(d_k − R)_+, where d_k = min over optimal T* of |P_k \ T*|.
   - The price is zero when every cut margin is ≥ 2δ.
   - This is an upper bound only. Whether it is attained (the make-or-break question) is open.
   - It may be relevant to M2, but D6's compression loss is a different objective.

## CityFlow adapter and runtime: what works

- The runtime is `external_envs/runtime/bin/python`, Python 3.12.14. The ready marker is
  present, and `runtime.json` shows every import `ok`.
- In the runtime, `import cityflow` resolves to
  `external_envs/repos/CityFlow/cityflow.cpython-312-darwin.so`. The pin is 81ee0f47 and
  matches the manifest.
- Worked: `gridToRoadnet(rowNumber=3, columnNumber=3, …, tlPlan=False)` run in the runtime
  from the scratchpad. It gives 21 intersections, 9 of them non-virtual. Each non-virtual one
  has 9 light phases; phase 0 is a 5 s right-turn-only clearance, and phases 1–8 are
  movement phases. Road ids are `road_x_y_d` (d: 0 E, 1 N, 2 W, 3 S).
- The pinned repo ships only `examples/{config,roadnet,flow}.json`, a one-intersection
  example with `rlTrafficLight:false`. A real grid needs the generator.
- macOS has no `timeout` command; use the tool timeout instead.
- NOT yet run: `cityflow.Engine` on a `make_grid_scenario` output, and
  `BudgetedCityFlowEnv` on real CityFlow. No CityFlow error has been observed so far.

## Background processes

None.

## Exact next steps (handed to main)

1. **Smoke run (not started).** Write `scripts/SMOKE_cityflow_budgeted.py`:
   - Call `envs.external.runtime.maybe_reexec_in_external_runtime(require_ready=True)` first.
   - Add the repo root to `sys.path`.
   - Call `make_grid_scenario(research/marl_budget/P3_cityflow/smoke_20260927/seed{s}, 3, 3, s, 300)`
     for s ∈ {0, 1}.
   - Build `make_budgeted_grid_env(..., n_decisions=30, action_interval=10)`.
   - Use plumbing heuristics, not baselines:
     - a MaxPressure-like actor using its own queue and the downstream waiting count from the
       inbox or cache, found through `PublicTopology.outgoing` (road, j, slot);
     - rankings by cached downstream queue, or random.
   - Configurations: full (k=4), none (k=0), fixed k=1 at R=0, drops at R=0 and R=1,
     bursty at random/R=0 and at R=None. Add one `mode="oracle"` run that measures the centre
     node's 16 subsets:
     `counterfactual_view` → actor → `oracle_rollout_value` → `set_critic_probe` checks.
     Label it PLUMBING/ORACLE.
   - Log every `check_access_invariants` violation (expected: 0), `access_log`, the source
     SHA-256 values, the CityFlow HEAD and the scenario hashes.
   - Launch with
     `CIG_EXTERNAL_RUNTIME_ACTIVE=1 external_envs/runtime/bin/python -u scripts/SMOKE_cityflow_budgeted.py > work/run_logs/cityflow_smoke_20260927.log 2>&1`
     using `run_in_background`. It should take seconds and use little RAM.
2. **`research/marl_budget/PROTOCOL_v0.md` (not started).** Write it from the module
   docstring plus Findings 2–4. It needs sections on:
   - agents, sensors and the 25 B message;
   - traces, and the reveal after the commit (the ranking may use k_{<t}, never k_t);
   - rank → R replacements → paid messages → actor;
   - the absent-message rule: cache with age, or a predictor that sees only the view;
   - costs;
   - Q(s,S) as decision value, with its three sources: a frozen full-information critic
     composed with the frozen actor; an oracle rollout; a learned set-critic;
   - δ (D6, i-vs-rest) with δ_pair as a diagnostic, signed gains, and cut margins;
   - the predictions: zero price when margins ≥ 2δ (proved for the compression loss, elementary
     for the subset objective); revision gain grows with δ/margin (empirical);
   - the baselines listed in the assignment, with the exhaustive subset oracle labelled ORACLE;
   - metrics, including the censored CityFlow travel-time label;
   - paired traffic and budget seeds, with bootstrap CIs and a Wilcoxon test on per-seed
     differences;
   - negative results (Decision 9.8).
3. **A test file for `models/set_critic_probe.py`.** Turn the three hand checks above into
   `tests/test_set_critic_probe.py`.
4. **Later work.**
   - Pairwise vs i-vs-rest δ: settle which one PROTOCOL's headline uses; the theorem's δ is
     i-vs-rest.
   - Yellow/clearance handling: v0 forbids phase 0.
   - Per-agent joint subset counterfactuals: v0 measures one agent at a time, with the others
     fixed.
