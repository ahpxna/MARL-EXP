# P3 progress log

- 2026-09-27: Read the required material:
  - MARL_STORY_VERDICT;
  - FULL_CORPUS_AUDIT §10, §12, §19, §21;
  - MARL_SYNTHESIS Decisions 5–9.

  Read the code:
  - envs/external/{cityflow,runtime,common,registry}.py and ADAPTER_CAPABILITY_MATRIX;
  - core_behavior.py:474–495, policy_value.py, kprefix_net.py;
  - run_paper_b_allocation.py (header).

  Wrote COMPACT.md.
- Findings that shape the design:
  - The existing CityFlowCIGEnvironment builds each intersection's observation from
    `item["roads"]`, which holds BOTH incoming and outgoing roads. Neighbour observations
    therefore overlap. Its `relation_features(ego, j)` reads the neighbour's FRESH `_obs[j]`
    (load_diff, wait_diff), which is a second free channel on top of core_behavior's reads.
  - The budgeted module uses incoming-lane sensors only. Sensors are then disjoint across
    intersections, and downstream occupancy is known ONLY through messages.
  - The δ of D6 (`mixedDifference F i x c`, LeanProductSurrogateV4) is an i-VERSUS-REST mixed
    difference, not a pairwise one. The score is `osc (productResponse q F i)`. The loss is
    `productCompressionLoss` = osc(F − Σ_{T} response)/2 over the whole message grid U^n. The
    protocol reports the theorem's δ and a pairwise subset diagnostic separately.
  - The pinned CityFlow ships a one-intersection example only. The tiny grid comes from its
    tools/generator `gridToRoadnet`, imported read-only, with output written outside the repo.
    The generator gives 9 phases; phase 0 is a 5 s clearance.
  - CityFlow's `get_average_travel_time` includes running vehicles at their elapsed time: a
    censored mean.
- 2026-09-27: Wrote envs/external/cityflow_budgeted.py (NEW):
  - a codec giving 25 B per payload plus 8 B per request;
  - BudgetTraceSpec with fixed / drops / bursty / per_episode traces;
  - frozen AgentView, PublicTopology, and a stage machine
    rank → reveal → revise → transmit → act;
  - oracle-only counterfactual_view, clone/restore and rollout;
  - make_grid_scenario, which uses the pinned generator read-only, with Poisson arrivals.

  Next steps: a cleanup pass (vehicle tracker reset, a snapshot helper), then
  tests/test_cityflow_budgeted.py, then the smoke run, then PROTOCOL_v0.md.
- Design note (for PROTOCOL): Q(s,S) must be the value of the DECISION taken with S, evaluated
  at the true state. It is not the critic's value estimate from the partial view, since bad
  news lowers that estimate while improving the decision.
- Elementary bound (my derivation; NOT in Lean; for the subset objective F(T)):
  - Let g_j = F({j}) − F(∅) and δ = the D6 i-vs-rest mixed-difference bound on {0,1}^n.
    Then |F(A∪i) − F(A) − g_i| ≤ δ.
  - Exchange chain ⇒ the score prefix P_k satisfies
    max_{|T|=k} F(T) − max_{|P\T|≤R} F(T) ≤ 2δ·(d_k − R)_+, where d_k = |P_k \ T*_k|.
  - Zero price if every cut margin ≥ 2δ.
  - To be sent to main as an observation for M2 (the D6 compression loss is a different
    objective).
- 2026-09-27 (wrap-up order from main):
  - tests/test_cityflow_budgeted.py: 17/17 pass, including the positive and mutation controls.
  - models/set_critic_probe.py: written and hand-checked (additive, XOR, 300 random); it has
    no test file.
  - The smoke run and PROTOCOL_v0.md were NOT started; both are handed to main.
  - See HANDOFF.md. No background processes.
