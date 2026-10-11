# PROTOCOL / DESIGN — every pending hypothesis (03/10/2026 23:0x EDT)

**Request.** User, 23:0x: "Thiết kế thí nghiệm cho tất cả!! literally TẤT CẢ!!" — design an experiment for every item.

**Sources:**
* external audits LATEST_COMPLETED_RESULTS_AND_DIRECTION, ADAPT_V12_P2_AUDIT, P2_COMPLETED_EVIDENCE_AUDIT;
* DECISION_FORKS_AND_HYPOTHESES (G1–G8);
* ledger L-304 … L-315.

**Status of the items:**
* Wave 1 items (E6, E3, E11, NYC) are **protocols frozen here**: their predictions and decision rules are fixed before any run.
* Wave 2 items are **designs**. Each gets its predictions frozen in an addendum to this file BEFORE its first panel episode, after its code smoke.

**Panels** (checked unused 23:0x):

| Use | Panel |
|---|---|
| E3 | 7301–7332 |
| E8 | 7401–7464 |
| E7 | 7501–7564 |
| E2 / E10 confirmation (only if the pilot passes) | 7601–7664 |
| E11 and the E2 / E10 pilots | the adaptation pilot's DEV 5717–5748 and SELECT 5701–5716, so they compare directly with L-312 (development blocks) |
| Spare | 7701–7764 |

**Common rules:**
* Gain vs Z, per actor seed.
* Two-level crossed bootstrap (2000 draws, rng 0).
* Paired per seed.
* Runners propagate exit codes.
* Reporters return INCOMPLETE on any missing cell.
* Dedupe (hard links) when disk < 25 GB.

---

## E6 (wave 1, prerequisite of E7) — does the emulator use only what packets carry?

**Fact.** In the 25 B nearest8 packet, a relayed copy carries a 4-bit age (0–14 steps, saturated at 14) and no timestamp. The
receiver therefore knows a copy's measurement time exactly only if it received that copy at an age < 14. A direct packet has
age 0. `Exact` keys copies by the simulator's exact `measured_at`.

**Design.**
* `scripts/MARL_e3_emulator_variants.py` adds:
  * `ExactAudit`: `Exact` + for every seen copy, the minimum age (steps) at which this receiver received it;
  * `ExactPacket`: the packet-only emulator — a copy is usable only if it was once received at age < 14; otherwise it is
    treated as missing.
* Measured on:
  * (a) trace level: U2 and U1 over the 136 non-panel traces (301–364, 901–904 × 8/16);
  * (b) closed loop: homogeneous CK1 on U2, dev episodes 901–904 × 8/16, seeds 0–9, comparing EXACT and EXACT_PACKET with
    K1 (lock recorded as in P2 Amendment 1).

**Endpoints.**
* The share of emulated entries whose chosen copy is ambiguous (min reception age ≥ 14).
* EXACT_PACKET vs K1: mismatched steps and queue difference.

**Decision rule (fixed).**
* If the ambiguous share is ≤ 0.1 % of entries AND EXACT_PACKET − K1 has |mean| ≤ 0.05 points, then EXACT_PACKET (packet-only)
  replaces EXACT in E7 with no other change.
* Otherwise E7 uses EXACT_PACKET anyway, so that only packet-recoverable information is used. The gap to EXACT is then reported
  as the cost of 4-bit timestamps.

**Cost.** Trace-level analysis, plus 10 × 8 × 3 short episodes.

## E3 (wave 1) — why does the partial emulator hurt on U1?

**Question.** On U1, the emulator misses 21.6 % of the K1 entries and fills them with OLDER copies (−4.17 vs PLAIN, P2 N3).
Three explanations compete:
* (i) older copies;
* (ii) the information dropped;
* (iii) mixing exact and substituted entries, i.e. joint inconsistency.

**Arms.** Homogeneous CK1 team on U1, with the same emulator for the available entries. Only the missing-entry rule differs:

| Arm | Missing-entry rule |
|---|---|
| EMU_OLDER | the existing rule |
| EMU_ABSENT | missing entries shown as never heard |
| EMU_FRESH | missing entries take the CURRENT U1 merged-view copy (fresh, true age) |
| PLAIN | no emulation |
| Z | silent baseline |

All arms use the packet-only key (E6).

**Panel.** 7301–7332 × 8/16; seeds 0–9.

**Predictions (registered).**
* E3a: EMU_FRESH − EMU_OLDER > 0 (CI lower > 0). If older copies are the harm, using the fresh one recovers.
* E3b: EMU_ABSENT − EMU_OLDER: no prediction; this reading is exploratory.
* E3c: all three emulator arms stay below K1-level, i.e. none recovers ≥ 50 % of the CK1 hazard (PLAIN(K1) − PLAIN(U1),
  taken from the same episodes run under K1). K1/PLAIN is run as a reference arm.

**Reading.**
* E3a true and EMU_FRESH ≈ PLAIN: the substituted old copies drive the harm.
* E3a false: mixing per se (joint inconsistency) is the remaining suspect. This stays a hypothesis, because the audit's
  confounds (age, mask) are only partly separated.

## E11 (wave 1) — training a new receiver from scratch at 8–80 episodes

**Purpose.** The comparator the audit requires before any "adaptation saves training" claim.

**Arms.** `scripts/MARL_e3_actor_adapt_v12.py --from-scratch`: random initialisation, otherwise the identical v12 recipe and
budgets.

| Arm | Data | β0 |
|---|---|---|
| SCRATCH_NEW | iid episodes | 0 |
| SCRATCH_MIX | iid / K1 alternating | 0 |
| SCRATCH_MIX_T | iid / K1 alternating | 1, constant; teacher-driven rollouts, the stronger scratch variant |

**Setting.** Seeds 0, 1. Budgets 8 / 16 / 40 / 80. Evaluated with the same evaluator on the pilot's SELECT and DEV blocks
(Z and parent rows reused, parity asserted on the parent).

**Prediction.** E11: at B ≤ 40, FT-mix (warm start, L-312) − SCRATCH_MIX > 0 on the NEW channel on both seeds (screening,
point estimates). There is no claim about B = 320 (the plateau).

## NYC (wave 1) — restart, throttled

* The same queue and producers.
* Two seeds at a time (at most 6 student trainers + teacher s1) instead of five. The 22:42 launch ran 13 trainers × 2
  threads on 10 cores / 16 GB and was killed at about 22:58 (swap 1.6 GB).
* Order: teacher s1 finishes (iterations 1998–2000), then student stages for seeds {0, 2}, {3, 4}, {1}, then the queue's
  evaluation stages and reports.

---

## E8 (wave 2) — a stronger Gaussian baseline: residual guard

**Fact.** CK1's calibration covariance has rank 7 (feature 0 constant under K1). The pseudo-inverse ignores the null-space
direction, so a view that differs ONLY along it is never flagged.

**Detector.** FB_Mr± = FB_Mq± OR (‖(I − CC⁺)(x − μ)‖ > r*), with r* = the maximum residual over the calibration views
(empirical; ties grouped as in the shared d2 rule; strict >). Its calibration is frozen as in P1 (same counts, same parity
checks).

**Arms.**
* PLAIN, FB_S+, FB_Mq−, FB_Mq+, FB_Mr−, FB_Mr+, Z.
* Receivers CK1 and Cage.
* K ∈ {1, iid, 2, 3}.

**Panel.** 7401–7464 × 8/16; seeds 0–9.

**Predictions** (cell groups as P1):
* E8a: FB_Mr− − FB_Mq− > 0 in the CK1@iid hazard cell (CI lower > 0) and in Cage@K1 (point estimate).
* E8b: own-channel retention ≥ 90 % for FB_Mr±.

**Code.** `MARL_e3_repair_panel_eval_v2.py` imports v1 and adds the FB_Mr family. v1 stays unchanged.

## E9 (wave 2) — a truly exact compatibility protocol

**Design.**
* Base packets carry the sender's LEGACY relay table. This is the table it would hold under K1, built from its own
  K1-scheduled receptions.
* Every scheduled packet carries the upgraded table. Old receivers read only base packets; new receivers read both.
* Simulation: a lockstep K1 environment stepped with the team's actions is exactly the state the senders would maintain, so
  old agents' inputs are the K1 merged views on the real trajectory.

**Byte accounting.**
* Base packets: 25 B each, |T^K1| = 2 per step, decoded by every old receiver: +25 B per old receiver per step.
* Upgraded packets: as U1 / U2.
* Unique broadcast bytes are reported separately from delivered bytes.

**Arm.** U2/EXACT_PROTO_OLD in E7.

**Replay check (implementation).** A homogeneous CK1 team with EXACT_PROTO on U2 equals the K1 run on every step and episode
(dev 901–904). It must be exact; a failure stops E9.

## E7 (wave 2; needs E6, E8 code, E9 code and the FT-old training) — mixed-version fleet CONFIRMATION

**Team.** 50 % CK1 / 50 % Cage. Primary layout D (checkerboard); secondary C (left columns), fixed now.

**Panel.** 7501–7564 × 8/16; seeds 0–9.

**Arms:**

| Arm | Notes |
|---|---|
| U1/PLAIN | |
| U2/PLAIN | |
| U2/EMU_OLD | packet-only, per E6 |
| U2/EXACT_PROTO_OLD | E9 |
| U1/FB_OLD | FB_S+ |
| U1/FBR_OLD | FB_Mr−, E8 |
| U1/FT_OLD | OLD agents run CK1 fine-tuned with FT-mix B = 80 (v12 recipe of L-312, seeds 0–9, trained before the panel) |
| U1/PCT_OLD | PCT B = 80 |
| K1/ROLLBACK | |

References: ALLNEW, ALLOLD, ZTEAM. Counters per OLD receiver: entries / missing / older / ambiguous.

**Primary endpoints (layout D):**
* P-a: U2/EMU_OLD − U1/FB_OLD > 0 on the system (CI lower > 0).
* P-b: U2/EMU_OLD − U2/PLAIN > 0 (CI lower > 0).
* P-c: NEW-group non-inferiority vs U1/PLAIN with margin 0.5, by CI (lower bound of the difference > −0.5).

**Secondary:**
* EMU_OLD vs FT_OLD and PCT_OLD (two-sided; retraining cost reported);
* EXACT_PROTO_OLD vs EMU_OLD (bytes vs replay exactness);
* layout C;
* references.

**Cost vector:**
* delivered bytes;
* unique broadcast bytes;
* emulator / legacy-state entries for the OLD group only;
* receivers to retrain;
* training episodes and teacher queries (FT / PCT).

No win over ALLNEW / ALLOLD is claimed without a CI.

## E2 (wave 2) — why did PAIRED (v1) lose? A 2 × 2 data factorial

**Factors.**
* Source of old-channel samples: O = old-policy rollouts on K1, or S = shadow old views on new-policy trajectories.
* Pairing with the new samples: P = same trajectories, or I = independent trajectories.

**Arms.** Loss = plain CE (γ = λ = 0), the same optimiser and updates. 20 new-channel episodes at B40-equivalent, reported as a
budget vector (new episodes, old episodes, physical trajectories, teacher queries):

| Arm | Cell | Description |
|---|---|---|
| FT-mix | O-I | the L-312 arm |
| A0 | S-P | the L-312 arm |
| S-I | S-I | the shadow old view taken from SEPARATE new-policy trajectories |
| O-P | O-P | new views shadowed onto old-policy trajectories |

Plus:
* A0×2 (S-P with twice the trajectories);
* UNI: PAIRED with h replaced by its batch mean (uniform new-channel up-weighting of the same share), which is the
  confound control of the audit.

**Setting.** Seeds 0, 1; B40 and B80; DEV block.

**Readings (registered contrasts):**
* O-I vs S-I: occupancy of the old-channel data.
* S-I vs S-P: pairing at equal views.
* S-P×2 vs S-I: pairing at equal trajectories.
* PAIRED vs UNI: whether h targets anything beyond a weight shift.

## E10 (wave 2) — PAIRED v2 (side branch)

**Design.**
* Backbone FT-mix: independent old-policy K1 episodes + new episodes.
* On the new episodes, a shadow K1 view supplies h dynamically: h = π_fixed-anchor acceptable on x_old AND the CURRENT student
  not acceptable on x_new. It is recomputed every update and is not differentiated.
* New-sample weights 1 + γh are normalised to mean 1 within the new samples, so the new channel's share stays fixed.

**Arms.** FT-mix, PCT, v2-static (h from π0), v2-dynamic, UNI.

**Setting.** Seeds 0, 1; budgets 8–80; DEV block.

**GO** (to the 7601 confirmation): v2-dynamic − FT-mix > +1.0 AND v2-dynamic − PCT > 0 on both seeds at B40, with the old
drop ≤ 0.5.

## E5 (wave 2) — G1, G2, G3, G4, G6

| | Design |
|---|---|
| **G2** (RI, cheap) | Frozen RI receiver trained on ages 4–7, deployed on 0–3, with drift λ ∈ {0, 0.1, 0.2, 0.4}, 5 seeds. Arms: plain; age-only remap; actual buffered emulation; current-state filtering; the known-parameter Blackwell garbling kernel (B = 0.98^Δ R(−λΔ), added noise covariance (p + 0.0025)(1 − 0.98^{2Δ}) I, age shown as d_old). Metric: MSE vs the Bayes floor; buffer / runtime cost. **Prediction G2a:** the kernel and actual emulation are both ≤ plain at every λ > 0, and the remap is worst. |
| **G1** (RI) | Add the Bayes line and the intrinsic / excess split to the age-role table for every λ (computation on the existing results.json + the G2 runs). No new claim beyond the RI. |
| **G3** (C0) | On the C0 exact tables: raw out-of-support mass vs loss- / action-margin-weighted out-of-support mass as predictors of a light's regret change; fit on half the controllers, test on the held-out half. C0's producer is unverifiable (C-9), so this runs on a FROZEN C0 rerun (c0_v3 code, hashed) first. **Prediction G3a:** weighted Spearman > raw Spearman on held-out controllers. |
| **G4** (SUMO, heavier) | Exposure measured three ways — human traffic only, a receiver stub (an occupancy model fixed before the test panel) and the actual learned fleet — same checkpoints, same traffic seeds. Two errors separated: stub occupancy error and receiver decision error. **G4a:** stub exposure predicts the fleet's regression better than human-only exposure on held-out lights. |
| **G6** (offline first) | On Q7b's per-seed rows (caps 30–∞), simulate a sequential "find one adequate upgrade" test (G_up ≥ γ, H_R ≤ ε) with valid confidence bounds and stopping, by resampling the existing seeds. Measure paid rollouts, false acceptance and retained gain vs full evaluation. A live run follows only if the offline test shows savings. |
| **G8** | Partly answered by the mixed fleet; the rollout-cohort extension is in E7's secondary layouts. |

---

## Order and CPU plan

The machine has 10 cores and 16 GB.

| Wave | Contents | Lanes |
|---|---|---|
| Wave 1, now | NYC throttled (≈ 6–7 processes, nice 5) + chain [E6 → E11 → E3] | 3 lanes |
| Wave 2, after code + smoke | E8 panel; FT / PCT-old training (10 seeds × 2 methods); E9 replay; E7 confirmation; E2 + E10 pilots; E5 (G2, G1 now — RI is minutes; G3 after the C0 frozen rerun; G6 offline; G4 last) | |

## Wave 1 smoke and freeze (23:09 EDT, before any wave-1 panel run)
E6 trace-level (analysis, not a panel): ambiguous share 0.0 on U1 and U2, 4x4 and 3x3, 136 non-panel traces (research/marl_budget/e3_wave_20261003/e6_packet_audit.json); packet-only availability U2 4x4 0.9999916, U1 0.7805.  Smoke (traffic 9001-9002, seed 0; NOT evidence): ExactV(older, all copies) == P2 Exact on U2 and U1 (identity PASS); pipeline through the report.  Frozen (sha256, first 16 hex):
* MARL_e3_emulator_variants.py 31d84cb5303e1ee7
* MARL_e3_emulator_rules_eval.py a7c00082e42f6a3c
* MARL_e3_e6_packet_audit.py bc1924f606b55b75
* MARL_e3_actor_adapt_v12.py a4807bc29e023f4d
* RUN_marl_e3_wave1.sh 90eeb168e71815d0
* QUEUE_marl_e3_wave1_20261003.sh 41ef4d56876ffcec
* MARL_e3_wave1_report.py ba59c78f3ef4cf0a
* MARL_e3_repair_panel_eval.py db7ceb9284d42999

## Wave 2a (E8 / E9 / E7) predictions as written above, smoke and freeze (23:26 EDT, before any wave-2a panel run)
E6 closed loop finished (10 seeds, dev): ambiguous 0, EXACT_PACKET == EXACT == K1 -> decision: EXACT_PACKET replaces EXACT in E7 with no other change.  Smoke (traffic 9001-9002, seed 0; NOT evidence): repair eval v2 calibration parity + FB_Mr in-sample false alarm 0; mixed fleet v2 identities PASS (ZTEAM, OLD=all PLAIN, OLD=none, OLD=all EMU = homogeneous packet-only run, OLD=all EXACT_PROTO = homogeneous K1, exact); E9 replay smoke PASS; pipeline through both reports.  Incident 23:2x: NYC students (6 trainers, 3.8-5.9 GB each) drove swap to 21.9 GB and free disk to 7 GB; wave-1 jobs were REFUSED by the guard; NYC stopped (processes killed), dedupe freed 1.56 GB, disk back to 26 GB.  NYC student stage is NOT runnable on this machine with the registered buffer (40 iterations of 48-agent states); it needs the other machine or a recorded protocol change.  Frozen (sha256, first 16 hex):
* MARL_e3_repair_panel_eval_v2.py 504fde6626d55da1
* MARL_e3_mixed_fleet_eval_v2.py b656a1f68464eb84
* RUN_marl_e3_wave2.sh 14561be076d94515
* QUEUE_marl_e3_wave2_20261003.sh 183c84d0b50d0551
* MARL_e3_wave2_report.py bb36f5afb04a7baa
* MARL_e3_emulator_variants.py 31d84cb5303e1ee7
* MARL_e3_actor_adapt_v12.py a4807bc29e023f4d

## Wave 2b (E2 / E10) smoke and freeze (23:34 EDT, before any wave-2b run)
Levels L = 1 / 2 / 5 / 10 iterations = 4 / 8 / 20 / 40 new-channel AND old-channel episodes for every arm (budget vector in each manifest: new / old views, physical trajectories, simulated episodes, teacher queries); the pilot's FT-mix / PCT / PAIRED / A0 rows at budgets 8 / 16 / 40 / 80 are the same levels.  Registered contrasts and the E10 GO rule as in the E2 / E10 sections (report header).  Smoke (seed 0, traffic 9001-9002; NOT evidence): v13 methods si / op / paired --uniform-h / v2 / v2 --dynamic-h ran; pipeline through the report.  Frozen (sha256, first 16 hex):
* MARL_e3_actor_adapt_v13.py 0657ab25809fcc9d
* RUN_marl_e3_wave2b.sh 2460d14da6c70bfa
* QUEUE_marl_e3_wave2b_20261003.sh 7756e64b89e6899f
* MARL_e3_wave2b_report.py 24ac925a647ca593
Launch: chained after the wave-1 rerun queue (LANES=3).

## E9b — distributed legacy decoder (04/10 00:2x EDT; external audit WAVE1_AND_COMPATIBILITY_PROTOCOL; before any E9b panel run)
scripts/MARL_e3_legacy_decoder_eval.py: every agent keeps LOCAL legacy state (cache of decoded base packets, own legacy merged view) and updates it only from base packets it physically received (public legacy schedule; base packet = fresh summary + the sender's legacy relay table); OLD agents act on the decoded legacy view.  A lockstep K1 reference environment is used ONLY for the per-step check of packets / cache / view / input / action for every agent.  Costs: base packets decoded by ALL 16 agents (10 400 B / episode), unique base broadcasts, legacy-state entries.
Registered: E9b-1 zero mismatches in all five parts and zero missing base packets on dev 901-904 x 8/16, seeds 0-9, layouts ALL / D / C (implementation check; any mismatch = FAIL, reported as is).  E9b-2 on the E7 panel (7501-7564, layouts D / C, seeds 0-9) the decoder arm's queue equals E7's EXACT_PROTO_OLD on every episode (consistency with the reference-state arm).  The E7 report's EXACT_PROTO cost line (OLD-only base decodes, 5 200 B) is superseded by the decoder's all-agent accounting.
Smoke (dev 901, seed 0; NOT evidence): 0 mismatches in all parts on ALL / D / C, 0 missing; layout ALL == homogeneous K1 (1574); base 416 packets (10 400 B).  NEGATIVE CONTROL (decoder on the non-nested U1, layout D): 208 base packets missing; mismatches packets 208, cache 366, view 365, input 365, action 93 — the check can fail.
* MARL_e3_legacy_decoder_eval.py 2f318e21b0086553; RUN_marl_e3_e9b.sh 5829ed230ebbd017 (frozen 00:12)

## E9c — per-node decoder, wire-format base packets, decisive negative controls (04/10 00:3x EDT; review HISTORY_FRAMING_REVIEW_20261004 items 1-4; before any E9c run)
Why: (1) E9b keeps every agent's state in one object and passes relay tables as Python objects with full-precision measurement times, while the deployed 25 B layout carries 4-bit ages saturated at 14 steps; (2) its only negative control is a missing-packet one (U1).  A first E9c smoke with a weak table corruption (only the freshest entry one step older) produced ZERO mismatches — that entry is always also in the receiver's own cache under the shared age-first order — so that control was replaced before any registered run (smoke dir in the scratchpad, recorded here as a design lesson, not evidence).
scripts/MARL_e3_legacy_decoder_nodes_eval.py: one Node object per agent (own schedule replica — replicas asserted identical every step —, own cache, own legacy table); a node's update receives ONLY its physical U2 view and the base packets delivered to it; tables are serialised slot-positionally in a declared format: full (measurement time; the simulator semantics), wire4 (4-bit ages saturated at 14: the deployed 185-bit layout), wire5 (5-bit ages saturated at 31: 193 bits <= 200, the same 25 B packet).  Checks every step / agent vs the lockstep K1 reference (packets, cache, view on actor-visible (sender, age, payload), input, action; timestamps separately as ts) and vs the E9b single-object decoder (old_dec).  Diagnostic relay_needed: reference merged-view entries supplied by a relay table and strictly fresher than the receiver's own cache.  Controls (with format full only): ages (all table entries one step older), empty (no tables = packet-only), u2table (senders put their U2 merged view in the table = NEW senders keep no legacy state), stale (decoded fresh entry one step old).
Lean: work/p13_conjectures/LeanMarlLegacyViewDecoderV1.lean — per-node decoder = reference K1 cache and view at every step under nesting S_t(i) subset of D_t(i) (dec_eq_ref), with saturated ages exact for t <= c + 1 (dec_wire_eq_ref: wire5 covers the 26-step episode, wire4 does not), tie-breaking immaterial on honest entries (ref_merge_perm), same input and action (same_action), nesting and the age bound not vacuous (miss_breaks, saturation_can_flip).  Enters no manuscript before the smoke gate.
Registered predictions:
* E9c-1 (implementation, any failure reported as is): full and wire5 — zero mismatches in packets / cache / view / input / action / ts / old_dec and zero missing base packets, on dev 901-904 x 8/16, seeds 0-9, layouts ALL / D / C, and on the E7 panel 7501-7564 x 8/16, layouts D / C; the wire5 panel queue equals E9b's decoder queue on every episode.
* E9c-2 (exploratory, the theorem does not cover it): wire4 — count of mismatches per part on the same episodes (prediction: zero; a nonzero count is a property of the deployed 4-bit layout and is reported).
* E9c-3 (the controls can fail): on every dev seed and layout, each control has > 0 view mismatches; u2table and empty have > 0 action mismatches summed over each seed's dev episodes; relay_needed > 0 on every dev seed.
Costs reported per episode: base packets delivered / decoded by all 16 agents (416 x 25 B = 10 400 B), unique base broadcasts (x 25 B), bits per base packet (185 / 193); extra decoding = one base packet per node per step.
Smoke (dev 901, headway 8, seed 0; NOT evidence): full / wire4 / wire5 zero mismatches in all parts on ALL / D / C, 0 missing; ALL == homogeneous K1 (1574); relay_needed 628; controls: ages view 286 / action 0-4, empty view 286 / action 16-23, u2table view 400 / action 39-59, stale all parts 416 / action 111-140.
* QUEUE_marl_e3_e9c_20261004.sh 2087ea3b30254b00 (frozen 00:35)
* MARL_e3_legacy_decoder_nodes_eval.py 2d2687430c709136
* RUN_marl_e3_e9c.sh 2e757e4cf4923c7a
