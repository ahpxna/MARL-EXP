# PROTOCOL — M4 stage 3, complete version: the full M2 matrix on spider (04/10/2026 22:08; DRAFT, registered before any new stage-3 run)

Parent: `PROTOCOL_CITY_M4_ARTERIAL_20261004.md`. That file registered stage 3 as "the M2 matrix (FT → RLK; labelled / naive / forecast)".
- Amendment M4-A5 ran **labelled / naive** (C-81).
- It deferred the **forecast** arm (no forecast model for three-green lights).
- The M2 target design (`PROTOCOL_CITY_M2_COMPAT_20261004`) also asks for the **adapted-fleet column**: the 2 × 2 matrix L0/F0, L1/F0, L1/F1, L0/F1.

This file completes both on spider. Nothing already run is re-run or re-read: 3a stays exactly as C-81.

## Populations (frozen unless stated)

| Symbol | Definition |
|---|---|
| L0 | FT, the spider static programs |
| L1 | RLK_sp11, RLK_sp111 (stage 1, C-76) |
| F0 | the rule GLOSA-L∘σ\* (`GLOSAL:0.3`), the only spider fleet that passed its stage (C-77; the TL caveat of C-81 applies) |
| F1 | the ADAPTED fleet: the v11 PPO speed residual on GLOSA-L∘σ\*, trained from zero under L1 with the stage-3 provider (`CITY_fleet_train_f1k.py`, the F1 recipe, 200 episodes, spider TRAIN 0–7). Seeds 213 / 313 under sp11, 413 / 513 under sp111. |
| References | σ\* 0.3 and OFF (σ 0.5), rows already on the panel (C-81) |

## 3a (DONE, C-81; not re-run)

Under L1:
- labelled → F0 ≡ σ\*, benefit LOST, no harm;
- naive → LOST with harm (fuel +7.16 %, agent TL +2.71, human TL +0.57 / up +0.82).

## 3b. The forecast arm: L1 / F0 with an honest empirical forecast

The question M2b asked on grid4: does the frozen fleet keep its benefit if the learned light publishes a forecast of its own timing, correctly labelled?

**Provider `CITY_spat_forecast_k`:**
- Multi-green, convention-corrected in every branch, C-84 included. The convention check PASSED on 16 traces, and its negative control fails (`spider/s4b/check`).
- Links served by the current and the next green get `unavailable`.

**Lineage (= the M3 prep procedure, with the spider frozen fleet in place of the grid4 dev fleet):**
- (i) Open-loop table: RLK traces with σ\* cars, TRAIN 0–7. These are already fitted: `spider/s4b/prov/fk_rlk<k>.json`.
- (ii) Closed-loop table: F0 drives on table (i) at q 0.5, 8 TRAIN episodes per light, phases recorded, then `fit_k` → `spider/s3b/prov/fkcl_rlk<k>.json`.

**q selection on DEV (the F1 §0 / M3 §6 rule, mechanical):**
- Candidates: q ∈ {0.1, 0.2, 0.3, 0.5} with table (ii).
- Each is evaluated with F0 on spider DEV 100–109 (the 2a seeds; disjoint from the panel) under sp11 and sp111. R = F0 with no SPaT (≡ σ\*).
- Select the feasible q under M3-2 (city, agent and human TL upper < +0.5; teleports ≤ R + 0.1; unfinished ≤ R) with the best agent fuel. If none is feasible, take the best agent fuel and mark it INFEASIBLE.
- The locked q is used by 3b AND 3c.

**Panel.**
- The stage-3 panel 1000–1019, re-used: no forecast choice was ever made on it, and q is chosen on DEV. Declared.
- The rows L0/F0 (F0_FT, S03_FT) and L1 σ\* rows (S03_RLK<k>, F0_RLK<k>_labelled) are those of C-81.
- New rows: F0_RLK<k>_fcast.

**Endpoints (= M2):**
- M2-B: F0 − σ\* under L1 with forecast (agent fuel %, agent TL, human TL).
- M2-C: DiD vs L0. LOST if the one-sided lower bound > +1; KEPT if the upper bound < +1; otherwise not separated.
- M2-D: valid-SPaT share, plus the `ambiguous-end` share.
- M2-E: harm (agent / human TL upper < +0.5).
- **Forecast quality (descriptive):** offline, on the DEV closed-loop traces of the locked q. Per second and per non-active green: forecast ttg vs the actual time to that green; MAE, bias, and the share within ±1 s (the grid4 D-dir tolerance).

**Prediction P-S3-1:** 3b is LOST.
- On grid4 every forecast arm failed for the frozen fleet: the M2b empirical forecast; F0 with the corrected forecast +0.39 %; the zero-residual rule +3.28 %.
- D-dir showed that ±1 s accuracy is needed.
- Harm (M2-E NO) is possible. Prior: LOST high; harm moderate.

**P-S3-2:** forecast MAE > 3 s; share within ±1 s < 40 %.

## 3c. The adapted-fleet column: L1 / F1 and L0 / F1 (descriptive matrix cells, NOT a method test)

**Honesty notes:**
- This uses the F1k machinery prepared for stage 4b (M4-A7). 4b was registered as a REPLICATION of a confirmed grid4 method, conditional on F1-A1, and was not run because F1-A1 failed (C-85).
- 3c does not reopen 4b. Its cells are the adapted column of the M2 matrix, reported descriptively.
- No claim that "retraining works" may be drawn from 3c. The grid4 confirmation of the recipe failed on agent TL by 0.05.

**Cells (panel 1000–1019, crossed over 2 lights × 4 fleets × 20 traffic where applicable):**
- **L1 / F1:** each F1 fleet under BOTH lights, with that light's locked provider (8 jobs). Own-light cells are 213 / 313 @ sp11 and 413 / 513 @ sp111.
- **L0 / F1:** each F1 fleet under FT with the program-derived SPaT (the old light publishes its plan) (4 jobs). This asks: does adapting to the new light cost the fleet its benefit under the old light (reverse compatibility)?
- **RULE reference:** F0 with the forecast = the zero-residual F1 (KS3-2), i.e. the 3b rows.

**Reported (with the F1 §3 limits shown, never gated):**
- [F1 − σ\*]_L1;
- [F1 − σ\*]_L0;
- adaptation gain D_adapt = [F1 − σ\*]_L1 − [F0 − σ\*]_L1,forecast;
- reverse cost D_rev = [F1 − σ\*]_L0 − [F0 − σ\*]_L0;
- own-light vs cross-light cells.

**Predictions:**
- P-S3-3: [F1 − σ\*]_L1 fuel < 0 (grid4 F1-A1: −2.6 %). The TL limits are uncertain (grid4 missed by 0.05). Prior moderate.
- P-S3-4: D_rev > 0, i.e. the adapted fleet keeps less of the FT benefit than F0 (−9.2 %). Prior moderate.

## Self-checks (exit 1, before the DEV selection and the panel)

| Check | Content |
|---|---|
| KS3-1 | The forecast-K convention check on the CLOSED-loop traces (ii) shows 0 error in every branch; its negative control FAILS. |
| KS3-2 | RULE0 (zero residual) + forecast ≡ F0 (GLOSAL) + forecast, bit-identical (seed 100, sp11), so the 3b rows are the RULE reference. |
| KS3-3 | The F1k trainer with 0 episodes, evaluated, ≡ KS3-2's rows (zero-init residual = the rule). |
| KS3-4 | The light sha in each trained F1 checkpoint = RLK_sp<k>.pt; the trainer reads TRAIN 0–7 only (`Q7.TRAIN_SEEDS`, patched to range(8)). |
| KS3-5 | Under the forecast the fleet receives valid SPaT (> 0 calls). The `unavailable:ambiguous-end` count is reported. |

## Stages and compute

1. Closed-loop prep (TRAIN), fit, then KS3-1.
2. DEV q selection (4 q × 2 lights × 10 seeds, plus R) → `spider/s3b/prov/locked.json`.
3. KS3-2 / 3 / 5.
4. 3b panel (2 jobs × 20).
5. 3c training (4 × 200 episodes), KS3-4, then 3c panel (12 jobs × 20).
6. Report: `CITY_m4_s3full_report.py`.

Spider episodes take seconds, so the whole run is about 30–40 min.

* 22:11 — **Code prepared and smoke-tested** (scratch; 300 s episodes; not endpoints):
  - The source-counting evaluator runs the frozen 4b evaluator verbatim (forecast 9 042 calls, ambiguous-end 478 on smoke seed 0).
  - `--record` traces fit to 18 lights.
  - The validation script runs.
  - The trainer with 0 episodes saves a zero residual. KS3-2 and KS3-3 identity hold on the smoke seed.
  - The q-selection and report scripts recover synthetic injected effects; the selection picks the feasible q with the best fuel and rejects a better-fuel infeasible q.
  - **Disclosed before any DEV / panel run:** on the 300 s smoke (seed 0, sp11), F0 with the open-loop forecast at q 0.5 showed agent TL 52.8 vs human 34.9 s/veh. This is a first-300-s transient, not an endpoint.
* **Frozen:** CITY_m4s_s3_eval.py f1d045077a9e3f48; CITY_m4_s3_select.py 8f65ad769de3c968; CITY_spat_forecast_k_validate.py 87f5e6030ea11dff; CITY_m4_s3full_report.py 9cca1fb601c0e6a4; CITY_m4_s3full_check.py 4b20e89ef8fa5520; RUN_s3full.sh 35d9ad5475867463; CITY_m4s_f1k_eval.py 34d82814491ad12f; CITY_fleet_train_f1k.py 7ee3b5b609cd80c5; CITY_spat_forecast_k.py 7848a3f3219b83dc; CITY_spat_forecast_k_conv.py 6cf21dd2c977c9a7; 
* **Status:** `RUN_s3full.sh prep` (TRAIN only, ends at KS3-1) launched at 22:11. The DEV selection and the panel (`RUN_s3full.sh all`) wait for the user's go-ahead.

* 22:33 — **Erratum (C-88):** the justification of P-S3-2 ('the grid4 D-dir tolerance' of ±1 s) is withdrawn. D-dir does not imply a ±1 s tolerance (fuel and time effects are asymmetric, C-72). The share within ±1 s stays as a descriptive metric only.
* 22:34 — Launched `RUN_s3full.sh all` (user 22:4x: 'Thử hết M3 chưa?? ... hoàn thành M3 M4 chưa hết à?' → run the drafted stage now).
