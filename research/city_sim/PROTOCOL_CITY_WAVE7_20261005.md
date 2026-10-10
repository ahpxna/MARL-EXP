# PROTOCOL WAVE 7: fresh-policy replication of TSI, and a faithful DC-Ada port (registered 05/10 ~15:15, before any wave-7 code was run)

**Why.** The user, 15:1x, asked for both experiments after the wave-6 review, which named three weaknesses: "fresh traffic, not fresh policy", "DC-Ada-style is not faithful", and "spider failed".
- These experiments add evidence; they do not change any earlier verdict.
- Results are reported as-is.

**Common rules:** PYTHONHASHSEED = 0, OMP_NUM_THREADS = 1; every run goes through the night queue (sequential spool, disk guard 15 GB); smoke first; reports refuse incomplete panels and check fuel, the three time losses, teleports AND unfinished trips.

## W7-1 FPR: fresh-policy replication of TSI on grid4 (one attempt)

**New, independently trained policies, never used before:**
- **Lights RL-H t9–t13:** the frozen Q7b recipe used for t4–t8 (`CITY_q7b_contract.py --train-light RL-H_t<k> --t <k> --episodes 120`, DQN seed 11 + 100 k), SUMO cars, TRAIN 0–7. Checkpoints in `research/city_sim/w7_20261005/fpr/lights/`. They are resolved through a call-time light_spec patch (`scripts/CITY_w7_run.py`, which chains the F1-A1 patch for t4–t8).
- **Fleets R10 s613 / s713 / s813 / s913:** the frozen v11 PPO recipe used for s213–s513 (`CITY_fleet_train_v11_ppo.py --spat on --seed <s> --episodes 400`), under the fixed-time program, as R10.

**TSI recalibrated from scratch for each new light (the TSI-2 procedure, unchanged), with the development fleet L11_s13:**
1. Traces: 8 TRAIN episodes, σ\* SUMO cars (`CITY_eval4_sigma.py --sigma 0.3 --fleet L-ACT:0 --guard always`, as F1-A1).
2. Open-loop table: `CITY_spat_forecast.py fit`.
3. Closed-loop c2 table: `CITY_f1b_prep.py` logic, 8 TRAIN episodes, dev fleet on c2 at q 0.5 (wrapper `CITY_w7_prep.py`; the only changes are the light ids and the directory).
4. N2 feature logs: 8 TRAIN episodes, dev fleet on fc2:0.1 (`CITY_n2_collect.py`).
5. Fit: `CITY_n2_fit.py` (MLP 64-64, quantiles 0.1 / 0.5).
6. Per-light adapter tuning on TUNE 660–663, with the TSI-2 grid of 10 (A, B) plus R and the TSI-2 rule (`CITY_w7_tune.py`, a copy of `CITY_tsi2_tune.py` with the light set and directory as arguments).

**Confirmation panel:** lights t9–t13 × fleets s613–s913 × fresh traffic **780–799** (20 seeds, period 2.0 s, after a non-existence check).
- **Arms:** R (no SPaT), TSI (hybrid service at q 0.5 + per-light (A, B)), HYB (service only), ADP (adapter only).

**Decision (registered primary, α = 0.05 one-sided, crossed bootstrap):** "TSI replicates with fresh policies" iff TSI vs R meets every M3 limit:
- agent fuel upper < 0;
- city, agent and human TL upper < +0.5;
- teleports ≤ R + 0.1; unfinished ≤ R.

This is a new single attempt with new checkpoints. It is not part of the TSI / TSI-2 Bonferroni chain; that chain stays at 0.075.

**Descriptive:** TSI − HYB and TSI − ADP; per-light chosen (A, B).

**Checks:**
- KF-1: each new light / fleet trained the full budget, and its file hash is recorded.
- KF-2: the N2 parity (offline vs online features and predictions), on one smoke log of light t9.
- KF-3: every c2 table holds 16 lights × 8 files.

## W7-2 DCA2: a faithful port of DC-Ada at matched simulated-time budget (grid4, TSI-2 lights)

**Port of the published algorithm** (Alqithami, IEEE Access 2026; code github.com/alqithami/DC-ADA, `src/agents/methods.py` `_adapt_accept_reject` and `src/agents/transformation.py`, read 05/10 15:0x).
- **Robots** = the 16 signal controllers. Each has its OWN transformation layer, a residual MLP on the 7 inputs:
  - encoder 7 → 32, ReLU, LayerNorm(32), hidden 32 → 32, ReLU, decoder 32 → 7, output + input;
  - initialised exactly to zero, so the starting point is the identity (DC-Ada's method default transform_init_std 0.0).
- **The frozen shared policy is RL-H; the TSI hybrid fleet service is unchanged.** As in W6-1, only the light-side adapter differs from TSI-2.
- **Accept / reject random search:**
  - robots in a fixed order (sorted controller id);
  - for each robot: one baseline rollout, then M = **5** candidates perturbing only that robot's parameters by σ = **0.05** · ε (ε ~ N(0, I));
  - all rollouts of a round under the same traffic seed (CRN);
  - accept iff best − baseline > τ = 0; update = step_size 1.0 · σ · ε_best.
- **Truncated rollouts:** candidate_rollout_fraction 0.25 of the evaluation horizon 5400 s, i.e. **1350 s**.
- **Return (scalar team reward)** = −J at the truncation horizon against R on the same seed and horizon, J = Δfuel_agent % + 4[ΔTL_agent + 0.25]₊ + 4[ΔTL_city]₊ + 4[ΔTL_human]₊ (as W6-1).
- **Budget matched in simulated time to TSI-2's 44 full rollouts per light:** 44 × 5400 s = 237 600 s = **176 truncated rollouts**, counting the R references.
  - Seeds: round r uses TUNE seed 660 + (r mod 4); R is run once per seed when first needed.
  - The search stops when the budget is used.
- **Tuning:** per light t4–t8, development fleet L11_s13, TUNE 660–663 only. Scripts `CITY_w7_dca2_tune.py` and the evaluator wrapper `CITY_eval_dca2.py` (CITY_eval_n4 imported unchanged; per-controller transforms applied in `obs`; truncation applied by a run wrapper).
- **Check KW7-1:** the zero transform reproduces HYB bit for bit (smoke seed 660, t4).

**Confirmation:** lights t4–t8 × fleets s213–s513 × traffic 760–779 (the W6-1 panel; not used to choose anything about DCA2); arms R, TSI2 (C-118 (A, B)), DCA2.
- **KW7-2:** the R rows equal W6-1's R rows bit for bit.

**Decisions (α = 0.05 one-sided):**
- (a) DCA2 meets every M3 limit vs R;
- (b) TSI2 − DCA2 on agent fuel and agent TL: "TSI better" iff both uppers ≤ 0 and one < 0; "DCA2 better" iff both lowers ≥ 0 and one > 0; else "no ordering".
- Accepted updates per light are reported.

**Remaining differences from the published setting, stated now:**
- DC-Ada adapts during training every 5 episodes. Here the whole budget is spent before deployment, because the deployed policy is frozen.
- The team reward is our deployment objective J, not an environment reward of the original benchmarks.
- TSI's adapter can see speed bins that no transform of the 7 inputs can create.

## Queue

| Job | Content |
|---|---|
| 060_W7_DCA2.sh | KW7-1, tuning, confirmation, KW7-2, report |
| 061_W7_FPR.sh | training (5 lights + 4 fleets in parallel), calibration chain, traffic 780–799, confirmation, report |

Each job writes into `research/city_sim/w7_20261005/<name>/`.
