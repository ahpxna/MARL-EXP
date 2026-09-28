# PROTOCOL v1 — information contract and naming (WP0 of MARL_ONE_PAPER_RESEARCH_AND_EXECUTION_20260927)

This supersedes PROTOCOL_v0 for the MAIN experiment. v0 and its diagnostics are kept unchanged
as history; their caveats are listed in §5.

## 1. Main contract: one network-wide packet budget, public scheduler, broadcast

- **Agents.** Every non-virtual CityFlow intersection is an agent. It has an own-incoming-lane
  sensor, fresh only at the owner, and it chooses its own phase.
- **Packets.** Each intersection can emit one 25-byte summary packet per decision step.
  Selected packets are broadcast through infrastructure to all agents.
- **Budget.** A network-wide grant k_t packets per step. The main theorem's feasible family is
  |S| = k over the pool of candidate packets. Per-receiver caps (v0) are kept as a diagnostic
  and ablation only; they give a partitioned feasible family, which needs its own proof.
- **Scheduler inputs.** Public context z_t only:
  - topology;
  - cached packets received earlier, with their ages;
  - charged metadata (request bytes).

  It never reads fresh unreceived payloads.
- **Round order:**
  1. z_t.
  2. The rank head gives π_t. Precomputation is charged as compute.
  3. The grant k_t is revealed. A budget-conditioned baseline sees the same k_t, at the same
     moment.
  4. Certificate check.
  5. If the certificate fails, repair candidates are scored by a deployable evaluator on
     permitted inputs.
  6. The final S_t is chosen with |S_t \ P_k(π_t)| ≤ R.
  7. Transmit. Bytes and delay consume simulation time.
  8. Actors act.
  9. Log.
- **Quantities.** N = paid calibration rollouts between frozen-actor rounds. R = pre-transmission
  replacements. k = runtime packets. The three are never merged.
- **Oracle access.**
  - Allowed in `mode="oracle"` only, and every oracle call is counted in `access_log`.
  - Deployed selections must not change when hidden payloads change while permitted inputs are
    fixed. This is a test that can fail: `tests/test_cityflow_budgeted.py` non-interference
    pattern.

## 2. Names (one symbol, one object)

| Name | Object |
|---|---|
| `f_joint(S)` | value of the JOINT decision profile when the broadcast set is S, at the true state, under a fixed continuation and horizon |
| `f_ego_oracle_i(S)` | v0 diagnostic: only ego i's information is changed, everyone else has full information (unilateral intervention) |
| `D6_loss(S)` | D6 half-oscillation compression loss (`productCompressionLoss`); frontier constant δ (LeanMarlRevisionFrontierV1) |
| `subset value` | decision value f(S); frontier constant 2δ (LeanMarlSubsetFrontierV1) |
| `delta_local` | max over A ∌ i of \|f(A∪i) − f(A) − g_i\| (the hypothesis of LeanMarlSubsetFrontierV1) |
| `delta_D6` | max over i, x, c of \|mixedDifference F i x c\|; implies delta_local ≤ delta_D6 (`bridge_mixed`) |
| `delta_pair` | max pairwise second difference; a LOWER diagnostic, never a certificate |
| `delta_U` | an upper confidence bound on delta_local; only this may enter a certificate |
| `V_det`, `V_rand`, `V^(R)` | best deterministic ranking; best pre-budget ranking law (max over k of the expectation); after R replacements. Ex-ante max_k E and ex-post E max_k are kept apart |

## 3. Corrected statements

- **m ≥ 7.** The nesting-degree results say that the BEST nested order may need more than one
  revision only when m ≥ 7 (for m ≤ 6 one revision always suffices, by exhaustive
  enumeration).
  - They do NOT say that revision is useless below 7.
  - For the SCORE priority, revision helps already at m = 3, e.g. `subset_constant_sharp` and
    the one-hop diagnostic.
  - v0 §7b overstated this.
- **Monotonicity.** Witnesses with non-monotone value tables (`sharpF`, `mirrorF`) are
  fixed-decoder or fixed-controller objects. They are not Bayes values of free information,
  since an optimal decoder can ignore extra messages. The joint-game construction
  (`research/marl_budget/proposed_joint_game/`) is Bayes-consistent for a > 0.
- **Existence versus algorithm.** `subset_frontier` asserts that a good repair EXISTS. A
  deployable selector must add:
  - estimated-score error u;
  - evaluator error ε;
  - search error ν;
  - candidate-coverage gap ζ.

  These are in LeanMarlEstimatedRevisionV1.

## 4. Diagnostics schema (v2 outputs, new files only)

Every table stores:
- the full subset→action→rollout-value map;
- the seeds and horizon;
- delta_local and delta_pair as separate fields;
- the access-log counts before and after the deployed step, with an assertion that they did not
  change;
- f_joint when the joint probe is used. f_ego_oracle is labelled as such.

## 5. Caveats on the v0 artifacts (kept unchanged)

- `diag_20260927/set_objective_full.json` and `set_objective_hops_full.json` are f_ego_oracle
  tables under a frozen max-pressure controller. They are NOT a learned MARL result, and NOT a
  team objective.
- Their check "deployed runs used no oracle data" is hard-coded `ok: True` in
  `scripts/DIAG_cityflow_set_objective.py`. It is an assertion, not a test; v2 replaces it with
  an access-log assertion.
- They do not store the full raw tables.
