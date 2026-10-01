# PROTOCOL E3-DFL — decision loss vs value regression on the same data (registered 28/09/2026, 19:32 EDT, before any DFL run)

Origin: the 19:3x assessment forwarded by the author ("Có thể đổi gì? ... loss trực tiếp theo lợi ích của lựa chọn").
Trainer v3 (`scripts/MARL_e3_selector_train_v3.py:115-116`) chooses the checkpoint and τ by the realised gain on SELECT,
but its gradient minimises the MSE of every candidate's value. The task is to pick a beneficial candidate, or keep
the prefix. This protocol tests ONE change, the training objective, with everything else fixed.

This is a method repair, not a novelty claim: decision-focused learning and learning-to-rank for decisions are
established (e.g. Mandi et al., ICML 2022). Development seeds only; seeds 1301–1316 stay closed.

## Question
On the same frozen actor, labels, legal inputs, candidate family, network, optimiser and training length, does
training the scorer by the expected gain of its own choice raise the realised selected gain on DEV, compared with
MSE value regression?

## Fixed (identical to the v3 `legal_bid_resp` arm)
- Actors: **scratch s3** (`e3_scratch_seeds34_20260928/actor_s3`, primary; recipe gate PASS);
  **BC s3** (`e3_run_seeds34_20260928/actor_s3`, secondary, descriptive; BC recipe pilot gate FAILED).
- Labels: each actor's existing `labels_train_*` (768 states), `labels_select` (48) and `labels_dev` (48).
- Inputs: legal only. The bid (10 B, charged inside the cap) and the response head trained on TRAIN (v3's
  `train_head`, epoch on SELECT log-loss). No privileged joint action.
- Feasible set: bytes ≤ b0 + 84 − 10, with the prefix always included (the trainer's `features`).
- Network `Net` (hidden 128); Adam, lr 1e-3, weight decay 1e-5; 40 epochs; one gradient step per train state per
  epoch, in the same permutation order; evaluation every 4 epochs.
- Checkpoint and τ are chosen on SELECT by the mean realised gain, direct policy. The τ grid is {−∞, 0, the
  per-state 0.9/0.99 score quantiles, +∞}. τ = +∞ means never edit: that is harm avoidance, not a benefit.
- Init seeds 0, 1, 2. They are averaged within an actor; they are not replications.

## Changed
Loss per training state s, with scores u_φ(c) (in units of ys = the std of train gains) over the feasible set C_s
(including the prefix), Δ(s, c) = the continuation gain in the labels (Δ(prefix) = 0):

    L_s = − Σ_{c ∈ C_s} softmax(u_φ / T)(c) · Δ(s, c) / ys.

- Temperature T ∈ {0.1, 0.3, 1.0}. The same init and the same permutation order are used for every T.
- T is chosen per init seed on SELECT, with the same select metric, jointly with the epoch and τ.
- Each T run has the same 40 epochs as the MSE arm. The T search is the only extra compute, and it is reported.
- Per-T DEV results are saved as secondary descriptions. They are never used to pick T.

## Comparator
The existing v3 `legal_bid_resp` checkpoints of the same actor, which were trained by MSE with seeds 0–2.

Self-check (abort on failure): the v6 trainer with `--loss mse --seed 0` must reproduce the v3 job of
`legal_bid_resp_s0` on each actor, with the same `dev_chosen` and `select_metric`. This proves that the only
difference in the DFL arm is the loss.

## Endpoints (DEV, direct policy)
- **Primary.** The realised selected gain (continuation, H = 3, relative to the prefix) of the arm. For each
  state it is averaged over the 3 inits. The arms are paired by state. DFL − MSE is reported with a
  traffic-seed cluster bootstrap CI (8 dev seeds; both loads and every snapshot of a seed together). The
  episode bootstrap is reported as well.
- **Secondary.** These are:
  - oracle regret;
  - edit rate;
  - harmful-edit rate P(gain < 0 | edit);
  - tie-half pair accuracy (selector diagnostic v3);
  - the same paired comparison on the dense development panel of scratch s3 (`dense/labels_dev`, 304
    states of the same 8 dev episodes, other candidates);
  - BC s3.

## Decision rule (fixed now)
A **development signal** needs BOTH of the following on scratch s3, on the primary DEV table:
- **S1.** The DFL arm's mean selected gain is > 0, with the traffic-seed CI lower bound > 0. This is a benefit
  over keeping the prefix, not only less harm.
- **S2.** DFL − MSE is > 0, with the traffic-seed CI lower bound > 0.

**If there is a signal**, the next steps are:
1. Train DFL with these exact settings on the other scratch actors (0, 1, 2, 4) once their labels are
   COMPLETE and audited, with T chosen on each actor's SELECT.
2. Offline DEV for each of them.
3. Closed loop v5 on 901–916, against the same actor's prefix and against `sel_nobid`.
4. Only then consider F6.

**If there is no signal**, stop:
- No further loss variant is tried on this question.
- The result is reported as negative ("no evidence of a benefit from the decision objective at n = 48 DEV
  states").
- A CI containing 0 is not equivalence, and 48 states give low power.
- The scope decision stays with the authors.

## Artifacts
| item | location |
|---|---|
| trainer | `scripts/MARL_e3_selector_train_v6.py` (v3 is unchanged) |
| checkpoints and jobs | `<actor>/selectors_v6/{model,job}_legal_bid_resp_{dfl,mse}_s*` |
| runner | `scripts/RUN_marl_e3_dfl.sh` |
| comparisons | `<actor>/dfl_paired_dev.{json,txt}` (MARL_e3_paired_eval.py) |
| diagnostics | `<actor>/selectors_v6_diag_v3.{json,txt}` |
| dense (scratch s3) | `<actor>/dfl_paired_dense_dev.{json,txt}` |

## Amendment 1 (28/09/2026, 20:08 EDT — written AFTER a 4-epoch smoke, BEFORE any full run)

**Disclosure.** A 4-epoch smoke (scratchpad `dfl_smoke`, scratch s3, seed 0, T ∈ {0.3, 1.0}) printed one DEV value,
−0.75 at T 0.3. It is not used for any decision, and it is the only DFL number seen before this amendment.

**Why.** An independent audit (`research/papers/audits/MARL_DFL_COMPARISON_RECHECK_20260928.md`) and the review of the
worker's rebuttal (`MARL_DFL_REBUTTAL_REVIEW_20260928.md`) found two confounds besides the loss:
- DFL gradients use only feasible candidates, while the v3 MSE uses every candidate;
- DFL searched 3 temperatures on SELECT, while MSE had one configuration.

The authors fixed four choices (20:0x); they are applied below.

**Corrections to the text above.**
- "This proves that the only difference in the DFL arm is the loss" is WRONG. The v3 reproduction only proves that
  the implementation is right; the set of candidates in the gradient also differs. That is why MSE-feasible is added.
- The expected-gain softmax loss is NOT new in this repository: `scripts/MARL_cheap_checks_v2_train.py` (the 27/09
  MP2 global-budget pilot) used it for its direct network. There, its held-out regret was 23.43, against 24.45 for the
  prefix and 25.65 for the MSE critic, on 2 traffic seeds and with no CI. This test is a REPLICATION of that learning
  rule on learned actors under the heterogeneous protocol.
- DFL scores are logits, not value estimates. So `LeanMarlSafeEditV1` (τ ≥ 2ε with ε a VALUE error) does not apply to
  a DFL selector, and the theory-to-implementation bridge is weaker for this arm.

**Arms (primary), all from `MARL_e3_selector_train_v6.py`.** Each arm uses the same legal bid + response-head inputs,
the same network and optimiser, 40 epochs, and the same init seeds 0, 1, 2.

| arm | loss | candidates in the loss |
|---|---|---|
| `legal_bid_resp_mse` (MSE-all) | v3 MSE | all |
| `legal_bid_resp_msefeas` (MSE-feasible) | MSE | feasible set, prefix included |
| `legal_bid_resp_dfl` (DFL) | expected gain, T = 1 FIXED | feasible set, prefix included |

**Equal tuning.**
- Every arm selects lr ∈ {1e-3, 3e-4, 3e-3} on SELECT, jointly with epoch and τ. The rule is the same as v3's: max
  SELECT mean realised gain, direct.
- Ties go to the first lr in that order, so the default lr is preferred.
- Each arm's selector init therefore costs 3 fits. The total is 27 fits per actor, and the prefix needs none.
- The earlier T grid {0.1, 0.3, 1.0} is dropped from the primary. It may be run later as exploration, reported apart.

**Comparators and reading.**
- The historical v3 `legal_bid_resp` (MSE-all, lr 1e-3 only) is reported descriptively.
- Self-check: the v6 MSE-all job of seed 0, sub-run lr = 1e-3, must reproduce the v3 job (dev_chosen, select_metric,
  best_epoch, τ). Otherwise the run stops.

**Primary cap.** Allowance +84 B over the prefix bytes, of which the bid takes 10 B (payload slack +74). Other caps are
secondary transfer checks, not part of this round.

**Screening rule (replaces §"Decision rule").** The rule is applied to scratch s3, the primary actor, on DEV (48
states, 8 traffic seeds). Per state, each arm's gain is averaged over its 3 inits; per traffic seed, the per-state
values are averaged (both loads and every snapshot of the seed).

- **Statistic.** The mean over the 8 seed means of:
  - (i) DFL − prefix (= DFL's own gain);
  - (ii) DFL − MSE-all;
  - (iii) DFL − MSE-feasible.
- **Screen.** Each contrast has mean > 0 AND one-sided sign-flip p ≤ 0.05, over all 2^8 = 256 sign vectors.
  - Stated assumption: under the null, the 8 seed-level differences are independent and symmetric about 0.
  - This makes the p-value a SCREENING statistic under that assumption. It is NOT a distribution-free guarantee
    about the mean. (Counterexample: D = +1 w.p. 0.9, −9 w.p. 0.1 has mean 0, yet all 8 seeds are positive with
    probability 43%.)
- **Combination.** All three contrasts must pass: an intersection-union screen. It needs no multiplicity correction
  for the conjunction, and it does not repair an invalid component p-value.
- **Always reported, and not used to pick anything:**
  - the 8 seed-level means;
  - traffic-seed percentile bootstrap CIs, not read as finite-sample coverage with 8 clusters;
  - episode CIs;
  - leave-one-seed-out ranges;
  - edit rate, harm | edit, oracle regret;
  - mean charged bytes of the chosen profiles, including the 10 B bid at every step.
- **If the screen passes**, the next step is §"If there is a signal" of the protocol: the same recipe on the other
  scratch actors, then closed loop. Closed loop on 16 seeds × 2 loads × several actors is stronger evidence, but it is
  still development and not 160 independent units.
- **If it fails**, stop as before. No further loss variant is tried, and the result is reported as "no evidence of a
  benefit at n = 48 DEV states / 8 seeds".
- **Secondary.** The dense DEV panel (304 states, the same 8 seeds, so no extra clusters) and BC s3.

**Deferred.** R1-DFL trained on C_R1 with its own tuning, and DFL-no-bid; the latter must precede any claim about the
bid. The shared-evaluator R1 stays a descriptive ablation.

**Evidence class (added 20:12, same amendment, before any full run).**
- This round is DEVELOPMENT. DEV 501–508 was opened in earlier E3 rounds, and one DEV value of the smoke was seen
  (−0.75). A result of this round is not a confirmation on unseen data.
- The question is only: with everything else fixed, does the decision objective choose better profiles?
- "Beats both MSE arms but not the prefix" does NOT meet the goal (contrast (i) must pass).
- No R1-DFL, new architecture or co-training arm is opened in this round.
- If the screen fails, the conclusion is: the recipe under test adds no benefit on the learned actor. It is NOT
  "every selector is impossible", and not a completed analysis paper.

**Second smoke disclosure (20:13).**
- A 2-epoch smoke of the amended trainer (all 3 arms, seeds 0–2, lr {1e-3, 3e-3}, scratch s3; scratchpad
  `dfl_smoke2`) prints DEV values at the end of each job. Two were read while checking the logs: DFL s0 +1.85 and
  MSE-all s2 0.00, both at 2 epochs.
- The smoke decision table is checked for errors only; its numbers are not read.
- None of these values is used for any decision. The full runs use 40 epochs and the lr set {1e-3, 3e-4, 3e-3}.
