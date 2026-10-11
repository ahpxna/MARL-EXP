# PROTOCOL — receiver adaptation PILOT (W4 screening), 03/10/2026 19:0x EDT

Written before any adaptation run beyond the code smoke of scripts/MARL_e3_actor_adapt_v12.py.

**Sources:**

* External audit: METHOD_ADVANTAGE_PLAN_20261003 and RECEIVER_ADAPTATION_IMPLEMENTATION_SPEC_20261003 (W1–W5).
* research/papers/audits/WHY_NOT_WIN_REVIEW_20261003.md: the ceiling, the plateau, and the disagreements behind §3.

**Status: SCREENING, not confirmation.**

* It uses 2 checkpoint seeds on a development panel.
* It decides only whether a confirmatory panel is opened (§6).
* The P1 / P2 panels (5301, 5401) are not read for any choice made here.

## 1. Problem (fixed now)

* **Old receiver π0:** relayCK1_st_s (4×4), trained on const1 (K1). It is deployed on the iid channel (U1, as deployed),
  where it falls about 9 points below its own-channel gain (4201).
* **Adaptation:** start from π0 with the same architecture and a fresh optimiser. The adaptation budget B is counted in
  **simulated episodes on all channels**; a paired episode counts 2. Teacher queries are counted and reported.
* **Goal:** higher closed-loop gain on the NEW channel at a small B, without degrading the OLD channel (K1) by more than ε.

## 2. Arms

All arms share:

* the same parent;
* teacher, labels and the teacher-acceptable margin (0.25);
* optimiser (Adam, lr 1e-3), epochs (2), minibatch (256), DAgger buffer and episodes per iteration (8 simulated);
* β0 = 0: student-driven, on-policy states;
* NO hyperparameter tuning in the pilot: each arm runs one fixed setting chosen a priori.

| Arm | Data per budget B | Loss |
|---|---|---|
| FT-new | B new-channel episodes | CE |
| FT-mix | B/2 new + B/2 old, independent | CE |
| PCT | as FT-mix | CE + λ·KL(π0‖π) where π0(x) is teacher-acceptable (λ = 1) |
| PAIRED | B/2 paired episodes | CE on x_new weighted 1 + γh (γ = 2) + ρ·CE(x_old) (ρ = 1) + λ·KL(π0(x_old)‖π(x_old)) where acceptable (λ = 1) |

PAIRED ablations, with all else fixed:

| Ablation | γ | λ | What it isolates |
|---|---|---|---|
| A0 | 0 | 0 | pairing alone vs FT-mix's independent episodes |
| A1 | 2 | 0 | prioritisation without preservation |
| A2 | 0 | 1 | preservation without prioritisation |

* BCWI: after the fine-tuned descendants exist, interpolate π0 ↔ FT-mix(B), with α ∈ {0.25, 0.5, 0.75} chosen on the
  SELECT block. It is reported as a cheap baseline.
* From-scratch reference: the 4×4 CK1 / Cage training curves (select every 20 iterations of 8 episodes). Not re-run.

## 3. Budgets and evaluation

**Budgets.** B ∈ {8, 16, 40, 80} simulated episodes, i.e. 1, 2, 5 and 10 iterations. These are well below the
from-scratch plateau (iteration 40 = 320 episodes; WHY_NOT_WIN §2.2). The audit's 10 % / 20 % of 500 iterations lies past
that plateau and is not used (§5 of the review).

**Seeds.** Checkpoint seeds 0 and 1. The training RNG seed equals the checkpoint seed.

**Evaluation.**

* Every saved checkpoint (b8, b16, b40, b80, and b0 = π0), on the NEW (iid) and OLD (K1) channels.
* Evaluator: scripts/MARL_e3_repair_panel_eval.py, arm PLAIN (the frozen evaluator path, parity-checked in P1).
* **SELECT block:** traffic seeds 5701–5716 × {8, 16}, used for BCWI α only.
* **DEV block:** 5717–5748 × {8, 16} (64 episodes), used for the screening verdict.
* Z on the same episodes; gain vs Z per seed.

## 4. Endpoints

| | Definition |
|---|---|
| **Primary (data efficiency, declared here)** | New-channel gain vs Z at B = 40 (5 iterations), PAIRED minus FT-mix, paired per seed. |
| Secondary | The same at B = 16 and B = 80; old-channel gain at each B, relative to π0's own K1 gain on the same episodes; h-rate; teacher queries; wall time. |
| Old-channel tolerance | ε = 0.5 point of gain vs Z, measured as the drop from π0 on K1. |

**Why data efficiency is primary.** Final-return headroom over MIX or retraining is at or below the select noise
(students ≈ the full-view teacher). Only the size and speed of closing the hazard can separate the methods (WHY_NOT_WIN
§2.1).

## 5. Self-checks

* The b0 checkpoint is identical to the parent.
* With identical channels, x_new = x_old at every step.
* Paired environments stay physically identical at every step: queue and every agent's own sensor block.
* The source hashes do not change during a run.
* The evaluator's own checks apply (P1 §5).

## 6. Go / no-go for the confirmatory panel

The pilot is screening on 2 seeds, so the bar is about direction and size, not CIs.

**GO to confirmation** (10 seeds, fresh panel 5801–5864, the protocol frozen first) only if all three hold:

1. PAIRED − FT-mix > +1.0 point at B = 40 on BOTH seeds, on DEV.
2. PAIRED's old-channel drop is ≤ ε on both seeds.
3. A0 does not explain the gain: PAIRED − A0 > 0 on both seeds. Otherwise "pairing alone" is the finding, not
   prioritisation.

**Otherwise NO-GO.** The pilot is then reported as is: where PAIRED loses, and to which arm. A failure does not mean that
"adaptation cannot win".

If FT-mix or FT-new already closes the hazard at B ≤ 16, the finding is that **plain fine-tuning is enough**. It is
reported, and FT-mix stays as the strong baseline.

## 7. Smoke and freeze (19:11 EDT, before the pilot launch)
Code smoke (CK1 s0, NOT evidence): b0 == parent weights and evaluator queue (1841 = 1841); identity check with equal channels PASS; paired physical identity asserted every step; all 7 arms ran; h-rate 0.10-0.12 (cf. the flip probe's ~12 %); a shape bug in acceptable() found and fixed in the smoke (failed outputs archived in legacy/).  SMOKE=1 pipeline (traffic 9001-9002, budgets 8/16) through the report; single-traffic-seed blocks swing by ±10 points, so no reading.  Frozen (sha256, first 16 hex):
* MARL_e3_actor_adapt_v12.py bf071bde9d712df0
* MARL_e3_bcwi_interp.py 1060fa8d070afd9c
* RUN_marl_e3_adapt_pilot.sh 60ded1e3caa92c37
* QUEUE_marl_e3_adapt_pilot_20261003.sh 59834f915a4cabbf
* MARL_e3_adapt_pilot_report.py 9993b92e4853d5d2
* MARL_e3_repair_panel_eval.py db7ceb9284d42999
Launch: after the P2 queue frees its 3 lanes (LANES=3, nice 10).

## 8. Amendment 1 (20:0x EDT, 03/10; before ANY pilot result was read: 38 of 328 evaluations existed, no report line with numbers had been produced or read; external audit ADAPT_V12_P2_AUDIT)

**1. Completeness.** If any registered seed × arm × budget × channel × block evaluation is missing, the report says
INCOMPLETE and gives no verdict. Previously, completed seeds alone could yield GO.

**2. BCWI.**
* α runs over {0 = parent, 0.25, 0.5, 0.75, 1 = FT-mix at the same budget}. The two endpoints come from existing rows; no
  new rollout.
* Feasible means the SELECT old-channel drop is ≤ ε. α = 0 is always feasible, so an α that violates the tolerance is never
  chosen.

**3. Component contrasts reported at every budget:**

| Contrast | Isolates |
|---|---|
| PAIRED − A2 | the h-weighting, given preservation |
| PAIRED − A1 | preservation, given weighting |
| A0 − FT-mix | pairing alone |
| PAIRED − PCT | vs the PCT-style arm |
| PAIRED − BCWI | vs BCWI |
| FT-new − FT-mix | old-channel replay |

**4. GO is tightened.** On top of the registered (1)–(3), GO now also needs, on every seed at B = 40:
* (4) PAIRED > A2; and
* (5) PAIRED > PCT and PAIRED > BCWI.

The registered GO is still printed. A GO is screening only: it does not mean PAIRED beats PCT or BCWI in confirmation.

**5. Loss formula and its limit.**

$$L = \frac{\sum_i w_i \, \mathrm{CE}_i}{\sum_i w_i} + \lambda \cdot \overline{\mathrm{KL}}$$

The weights are w = 1 + γh on new-channel samples and w = ρ on old-channel samples, normalised TOGETHER. So γ > 0 also
raises the new channel's share of the CE weight: from 0.50 to about 0.61 at h̄ ≈ 0.11, γ = 2. PAIRED − A2 therefore confounds
regression targeting with that shift. The confirmation stage must add a control arm with uniform new-channel up-weighting of
the same share. No pilot gain may be called "finding the right regressions" without it.

**6. Savings vs training from scratch.** No claim is made: there is no from-scratch baseline at the same small budgets yet.
The old training logs (select every 20 iterations) do not provide one.

**7. Runner.** RUN_marl_e3_adapt_pilot.sh is running and is not edited. Its `|| echo FAIL` is covered by the completeness
check in item 1.
