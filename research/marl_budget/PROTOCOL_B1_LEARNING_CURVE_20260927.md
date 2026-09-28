# PROTOCOL B1 — learning curve on the heterogeneous-receiver objective (preregistered)

- **Written BEFORE any B1 data exists**, 27/09/2026 ~21:00. It is not edited after data are seen;
  any later change is appended as a dated amendment with its reason.
- **Authorisation.** The user lifted the audit stop rule for this one test
  (HETERO_DIAGNOSTIC_V2 "Decision"), and only for this test.
- No ledger is edited.

## Question

The Step 3 pilot and diagnostic v2 found no legal-information selector that improves on the prefix
on held-out traffic. Training contexts were few (72 fit contexts; 96 in the global checks), and
train regret was fitted while test regret was not. **Is that failure a data-scale failure?**

B1 asks whether a legal-information repair selector reaches a positive, repeatable gain on a FRESH
test panel when the training traffic grows 8×.

## Fixed design (identical to the pilot unless stated)

- **Environment, actor, labels.**
  - PROTOCOL_HETERO_v0 transport: one broadcast stream, receiver capacities, patches of radius R.
  - Frozen MP2 actor, held-phase H = 3 value, 3×3 grid, headway 8 and 16.
  - Snapshots t = 10, 13, …, 25.
  - The live capacity vector K, plus 3 random capacity vectors, per snapshot.
  - The same candidate family: all single-receiver one-swaps, 24 R ≤ 1, 24 R ≤ 2, 24 unrestricted.
  - Collector: `scripts/MARL_hetero_lc_collect.py`, which imports the pilot collector's
    `episode_env`, `Labeler`, `candidates` and `masks` unchanged.
- **Seeds, all never used before in this repository.**
  - Train pool 301–364 (64 seeds).
  - Select 401–408 (8 seeds).
  - Test 501–508 (8 seeds).
  - Each seed runs at both headways: an episode is a (seed, headway) pair.
- **Levels.** N ∈ {8, 16, 32, 64} train seeds, always the first N of the pool (nested).
- **Legal features.** `mirror` is the receiver-cache mirror, rebuilt by
  `scripts/MARL_hetero_mirror_replay.py` (unchanged). The replay asserts that labels are reproduced
  and that the mirror equals the true caches.
- **Learners.** Architecture, optimiser, epochs, anchoring and tie rule are exactly those of
  `MARL_hetero_diag_train_v2.py`.
  - `mlp_history`: legal, receiver history. **PRIMARY.**
  - `mlp_public`: legal. Secondary.
  - `ridge_edge_history`: legal. Secondary.
  - `mlp_joint_only`: PRIVILEGED joint actions. A reference only, never deployable.
  - MLP initialisation seeds 0, 1, 2.
- **Selection.**
  - The epoch (MLP) or λ (ridge) is chosen on the select split, by the v2 operating-point metric.
  - The no-edit threshold τ, including never-edit, is selected on the select split.
  - Operating point: cap = prefix bytes + 28.
- **Test.** Sealed. It is evaluated once, after selection, for every (N, learner, seed). No choice
  is changed after test results are seen.

## Endpoint and decision rule

- **Endpoint.** The `repair_R1` gain over the prefix at cap +28, as mean held-phase value over
  test groups (8 seeds × 2 headways × 6 snapshots × 4 capacity vectors = 384 groups).
- **Reference.** `oracle_R1` at cap +28 on the same groups.
- **Uncertainty.** A cluster bootstrap over the 16 test episodes (10,000 resamples) of the
  seed-averaged per-group gain.
- **PASS: the MARL route is alive. All three must hold for `mlp_history` at N = 64.**
  1. Each of the three initialisation seeds has a test gain > 0.
  2. The 95% bootstrap lower bound of the seed-averaged gain is > 0.
  3. The seed-averaged gain is ≥ 0.25 × the oracle R1 gain.
- **Reported but not used for PASS:**
  - the trend in N;
  - edit, harm and action-change rates;
  - bytes;
  - every secondary learner. Secondary learners do not rescue a failed primary.
- **Reading of outcomes.**
  - PASS: the pilot failure was data scale. Next is E2 on this protocol, with fresh seeds again.
  - FAIL, and `mlp_joint_only` meets criteria 1–3: the information bottleneck is confirmed at 8×
    the data. The next step is B2, a paid fresh-bid protocol. The legal learned selector is not
    claimed.
  - FAIL, and `mlp_joint_only` also fails: even the privileged reference cannot learn the
    headroom at this scale. The learned-method claim is dropped for this protocol.

## Self-checks (a failure aborts; nothing is reported)

- The collector asserts that labels do not change the live state. Smoke also checks live actions
  against counterfactual actions (contract A).
- The replay reproduces z, the order, K and two stored values per snapshot, and the mirror equals
  the receiver caches.
- Training asserts:
  - train, select and test seeds are disjoint;
  - the prefix delta is 0 in every group;
  - the oracle R1 gain is ≥ 0 in every group;
  - sources are unchanged during the run.

## Limits, stated in advance

- Still a frozen MP2 actor, one grid, one value horizon.
- The candidate-set argmax is not the deployed search.
- 8 test seeds.
- A PASS says nothing about learned actors (E3).
