# PROTOCOL B4 — on-policy (DAgger-style) data against covariate shift, then a fresh closed-loop test

- Written 27/09/2026 ~23:15, before any on-policy label exists.
- Motivation: B3 FAIL, diagnosed as covariate shift induced by the policy itself
  (`B3_CLOSED_LOOP_RESULTS_20260927.md`).
- No ledger is edited.

## 1. Data (one DAgger iteration)

- **Collector:** `scripts/MARL_hetero_onpolicy_collect.py`, β = 0.5. At every decision step the live
  profile comes from one of two sources:
  - with probability β, the oracle held-phase choice (the expert);
  - otherwise, the frozen B2 selector (mlp_top2_joint, init seed rotating) with its τ and the bid
    charged.
- **Seeds:** train 301–364 and select 401–408, headways 8 and 16. The traffic seeds are the B1
  pool; the trajectories and states are new.
- **Snapshots:** t ∈ {4, 7, 10, …, 25}, with the B1 label definition (live K + 3 random capacity
  vectors, the same candidate family, oracle held-phase values). Every development field is
  computed live from the same state.
- **Aggregation:** B1 prefix-trajectory data (`b1_lc_20260927_201443`, shards 0–3) + on-policy data.

## 2. Retraining (same code, same hyper-parameters)

- `mlp_top2_joint`: `scripts/MARL_hetero_top2_joint_dev.py` (stage A + critic) on the aggregate.
- Controls `ctrl_history`, `ctrl_public` and `bid_queue`: `scripts/MARL_hetero_mitigation_dev.py`
  on the SAME aggregate. The control gets the same data.
- Epoch and τ are selected on the aggregate select split (401–408, prefix + on-policy).

## 3. Closed-loop test (confirmatory)

- **Panel:** fresh seeds 801–816 × headways 8 and 16, 32 episodes, never used anywhere.
- **Evaluator:** `scripts/MARL_hetero_closed_loop_v2.py`, total cap +84, direct, bids charged.
- **Methods:**
  - prefix;
  - retrained `ctrl_history/s0-2`;
  - retrained `mlp_top2_joint/s0-2`;
  - the FROZEN B2 `mlp_top2_joint` (reference, not retrained);
  - `oracle_heldphase` (reference).
- **Endpoint and PASS:** identical to PROTOCOL_B3, applied to retrained mlp_top2_joint against
  retrained ctrl_history:
  1. the 95% upper bound of the relative Σ-waiting change is < 0;
  2. the mean against the prefix is < 0;
  3. the mean finished-trip difference against the control is ≥ 0.
- **Also reported:**
  - edits per episode (the covariate-shift symptom);
  - bytes;
  - every seed;
  - the frozen-B2 reference.
- Development check before the test: closed loop on 501–508, which is development only. It does
  not decide anything.

## 4. Limits

- One DAgger iteration. The retrained policy can again visit new states.
- Frozen MP2, 3×3 grid, one demand model. This is not learned-actor MARL.
