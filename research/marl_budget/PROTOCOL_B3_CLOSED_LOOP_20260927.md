# PROTOCOL B3 — closed-loop test of the frozen B2 design (preregistered)

- Written 27/09/2026 ~23:00, after the B2 held-phase confirmation PASS and BEFORE any
  closed-loop run of a learned selector.
- No ledger is edited.

## Question

B2 confirmed the frozen design's HELD-PHASE gain on fresh seeds: `mlp_top2_joint`, direct, total
cap +84 with the 10 B bid charged inside. Does that gain survive in CLOSED LOOP? In closed loop the
selector's choice is transmitted at every decision step, the frozen MP2 actors act on what they
received, and the trajectory continues from there.

## Design (fixed now)

- **Evaluator:** `scripts/MARL_hetero_closed_loop_v2.py`, with the frozen models, τ and stage A
  from `b2_freeze_20260927/dev_map.json`. Nothing is refitted.
- **Panel:** seeds 601–616 × headways 8 and 16, 32 episodes, 26 decisions each. These seeds have
  never been run in closed loop.
- **Methods:**
  - `prefix`, the paired baseline;
  - `ctrl_history/s0-2`, the frozen B2 control;
  - `mlp_top2_joint/s0-2`, the frozen B2 design;
  - `oracle_heldphase`, a non-deployable reference.
  - All at total cap +84, policy direct, bid bytes charged inside the cap and added to the byte
    count.
- **Primary endpoint.** Relative change in Σ waiting (the sum over decisions of total waiting
  vehicles) of `mlp_top2_joint` against `ctrl_history`, per episode. Each is averaged over its 3
  initialisation seeds.
- **Uncertainty:** a cluster bootstrap over the 32 episodes, 10,000 resamples.
- **PASS iff:**
  1. the 95% upper bound of the relative Σ-waiting change against ctrl_history is < 0;
  2. the mean relative Σ-waiting change against the prefix is < 0;
  3. the mean finished-trip difference against ctrl_history is ≥ 0.
- **Always reported:**
  - bytes (total, relative to the prefix);
  - edits per episode;
  - every seed;
  - the oracle reference;
  - episodes better or worse.
- **Scope of a PASS:** frozen MP2, 3×3 grid, this demand model. It is not a learned-actor MARL
  result.
