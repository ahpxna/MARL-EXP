# PROTOCOL — F1: does an ADAPTED fleet recover eco benefit under the upgraded learned light? (04/10/2026 19:57; DRAFT, registered before any F1 run)

Follows C-68…C-71. M3 version E stopped after DEV (C-69). The guide's M2 "frozen / adapted fleet" column is still open.

**Narrow question.** Under the ORIGINAL learned light RL-H (frozen, not fine-tuned) and one locked, valid forecast service:
- does R10 fine-tuned under that light (F1) beat the σ\* fleet within the time-loss limits?
- F1 must beat **σ\***. Beating only the harmed frozen fleet F0 is not enough.

**Rights.** The fleet's weights may be updated; the light may not. This is a different right from M3, and is reported as such.

## 0. Provider: convention fix, then mechanical re-selection on DEV

**Convention fix (C-71).** `scripts/CITY_spat_forecast_c.py` wraps `CITY_spat_forecast.make_spat` unchanged, and adds +1 s to ttg ONLY when the light is in a green and the link is served by the other green. Nothing else changes.

Check **KF-0:** on all RL-H traces the convention check gives 0 error in all three branches with the corrected formula (true durations).

**DEV re-selection** (the M3 §6 rule, mechanical):
- Candidates: the corrected closed-loop provider of RL-H:k (`m3_20261004/prep/prov_rlh<k>_cl.json`) at q ∈ {0.1, 0.2, 0.3, 0.5}, plus q 0.05 if the diagnostic below triggers its rule.
- Each candidate is evaluated with the FROZEN fleet F0 (L11_s13 and L11_s113) on DEV (SELECT 100–104 + 200–209), light seeds k = 0, 1.
- Selection: the feasible candidate under M3-2 with the best M3-1. If none is feasible, the best M3-1, marked infeasible.
- **This locked provider is used for F0, F1 and F1-scratch alike.**

## 1. Diagnostic D-dir: does the DIRECTION of the time-to-green error matter? (run first; cheap; ORACLE, open-loop)

Setting: the C-61 replay. RL-H:k schedules recorded with σ\* cars, SELECT 100–104, k = 0..3. The frozen R10 fleet is paired as in C-61 (L11_s{213 + 100k}).
- The fleet receives the EXACT oracle ttg shifted by δ: ttg′ = max(0.5, ttg + δ), with δ ∈ {−8, −4, −2, −1, 0, +1, +2, +4, +8} s.
- ttr is unchanged.
- **Self-check KD-1:** δ = 0 reproduces the C-61 F0b rows bit-identically.
- **Endpoint:** fleet contribution vs the σ\* replay rows (C-61), as agent fuel %, agent TL and human TL, per δ, with the crossed bootstrap (4 pairs × 5 traffic).

| # | Prediction |
|---|---|
| P-F1-0 | Asymmetric: for each magnitude m ∈ {1, 2, 4, 8}, the fuel contribution at δ = +m (green predicted LATER than it comes) is worse than at δ = −m. |

**Provider rule (registered).** If the contribution improves monotonically from δ = 0 to δ = −4 to δ = −8 (point estimates), q 0.05 is added to the §0 candidate set. Otherwise the set stays {0.1, 0.2, 0.3, 0.5}.

D-dir is a mechanism diagnostic on an open-loop replay. It does not establish closed-loop behaviour.

## 2. Arms (DEV development)

| Arm | Definition |
|---|---|
| **R (σ\*)** | RL-H:k with no SPaT; the fleet falls back to σ\* (identical rows, KM2-2) |
| **F0** | Frozen R10 (L11_s13, L11_s113) with the locked provider |
| **F1** | R10 FINE-TUNED under RL-H:k with the locked provider. v11 PPO recipe unchanged (CITY_fleet_train_v11_ppo semantics: speed residual on GLOSA-L∘σ\*, dense per-agent credit, intervention-indexed discount C-51), initialised from L11_s13 / L11_s113, **200 episodes**, TRAIN 0–7, light RL-H:k frozen. DEV runs: (s13, k0), (s113, k1), (s13, k1), (s113, k0). |
| **F1-scratch** (optional, efficiency reference) | The same trainer from the zero-init residual (V9.NetR), same 200 episodes, seeds 13 / 113 × k 0 / 1. |

## 3. Endpoints (as M3; fuel primary)

Endpoints are vs R under the same light seed, the same traffic and the same cohort:
- agent fuel % (superiority: upper < 0);
- city, agent and human TL (upper < +0.5);
- teleports mean ≤ R + 0.1;
- unfinished ≤ R.

Descriptive: F1 vs F0; F1 vs F1-scratch; commanded vehicle-seconds; forecast error at query times (bias by sign).

**DEV gate for confirmation:** F1 pooled over the 4 DEV runs (crossed with the two light seeds and both dev traffic sets) passes all of the above.

## 4. Confirmation (only if the DEV gate passes; registered now, frozen at the gate)

- **Traffic:** fresh 530–549 (generated after the gate).
- **Lights:** the five NEW independent RL-H seeds t4…t8 (`m3_lights_20261004`, unused by M3). For each, a closed-loop provider is refitted with the identical procedure, and the locked q is applied.
- **Fleets:** F1 fine-tuned from L11_s213 / s313 / s413 / s513, each under one new light (t4, t5, t6, t7), with the frozen F1 recipe.
- **Evaluation is CROSSED** over all 5 lights × 4 F1 runs × 20 traffic. The bootstrap is over light, fleet and traffic. This tests robustness to a light seed the fleet was not adapted to; this is declared.
- **Gate:** F1 vs R as in §3. F1-scratch is reported, never gated.

## 5. Self-checks (exit 1)

| Check | Content |
|---|---|
| KF-0 | Corrected-provider convention check: 0 error. |
| KF-1 | The F1 trainer with 0 episodes ≡ F0 rows (light RL-H:k, locked provider), bit-identical. |
| KF-2 | The light in F1 training is RL-H:k unchanged: LightRL with the original checkpoint, with a hash check. |
| KF-3 | Provider lineage: table hash and q recorded per row; F0, F1 and R use the same file. |
| KF-4 | Training seeds TRAIN only; no DEV or confirmation traffic read by the trainer. |
| KD-1 | δ = 0 ≡ C-61. |

## 6. Predictions

| # | Prediction |
|---|---|
| P-F1-0 | Asymmetry (§1). |
| P-F1-1 | F0 with the corrected, re-selected provider is still NOT better than σ\* on DEV (fuel upper ≥ 0), as in C-68. |
| P-F1-2 | F1 beats σ\* on DEV within all TL limits (moderate prior: the C-61 diagnostic shows a −6.6 % opportunity for R10 with exact information; with forecast error it should be smaller). |
| P-F1-3 | F1-scratch reaches less than F1 at the same budget. |

## 7. What a result means

| Outcome | Reading |
|---|---|
| F1 passes on confirmation | Updating the fleet is a beneficial deployment option under the upgraded light, given a valid forecast. This is the adapted-fleet column of M2. |
| F1 beats only F0 | Not enough. |
| F1 fails | This recipe is rejected. It does not show that adaptation is useless in general. |

* 20:07 — **Checks PASS:** KF-0 (convention), KD-1 (δ = 0 ≡ C-61), KF-1…KF-4 (`f1_20261004/check/f1_check.txt`).
* **D-dir result:** P-F1-0 FAILS (C-72). The q 0.05 rule is not triggered, so the candidate set stays {0.1, 0.2, 0.3, 0.5}.
* **Frozen before the §0 selection and the F1 runs:** CITY_eval_f1.py 3b09b5aa39f42cc9; CITY_fleet_train_f1.py 9c413f20d3624261; CITY_f1_check.py f6f386ac498dc84a; RUN_f1_provider.py c0c8602bfc3e50f3; CITY_f1_provider_select.py 268239f352def7f6; RUN_f1_train_dev.py c6f5b0aeb81365f6; RUN_f1_eval_dev.py 8b1d4b39e0262d43; CITY_f1_dev_report.py 1072d4afd4a50200;
* **Chain:** §0 provider selection → F1 / F1-scratch DEV training (200 episodes) → DEV evaluation → DEV gate. All are automatic and rule-based.

## Amendment F1-A1 (21:09, 04/10): post-DEV promotion of F1-SCRATCH to a confirmation (registered after the DEV result C-78, before any F1-A1 run)

**Why this is an amendment.**
- §3 gated F1 (fine-tune), and it FAILED on DEV, so §4 is not run for F1.
- F1-scratch was registered as "reported, never gated". On DEV it passed every §3 criterion (C-78: agent fuel −3.06 % [−3.60, −2.46], agent TL +0.13 up +0.30, human −0.76, city −0.33, 0 teleports).
- Promoting it is a choice made AFTER seeing DEV, between two arms. This is declared. The confirmation below is its first test on data the choice never saw, and the only confirmatory test of F1-A1.

**Design (= §4 with F1-scratch in place of F1).**
- **Traffic:** fresh grid4 530–549, generated after this registration with the verified grid4 randomTrips configuration (checked first by regenerating seed 509 into scratch). 510–529 stay unused.
- **Lights:** the five new RL-H seeds t4…t8 (`m3_lights_20261004`, unused by any evaluation). They are reached through a call-time patch of `CITY_xplay2.light_spec` (`RL-H:4…8` → those files; `RL-H:0…3` unchanged; check KA-1).
- **Providers, refitted per new light with the identical procedure:**
  - (i) M2b open-loop table: RL-H:t with σ\* cars on TRAIN 0–7, recorded, then `CITY_spat_forecast fit`.
  - (ii) Closed-loop table: `CITY_m3_train_E prep` (8 TRAIN episodes, dev fleet L11_s13 driving on table (i) at q 0.5), then `fit`.
  - (iii) The fleet uses the convention-corrected table (ii) at the locked q 0.1.
- **Fleets:** F1-scratch with the frozen `CITY_fleet_train_f1.py` (zero-init residual, 200 episodes, TRAIN 0–7), seeds 213 / 313 / 413 / 513, each under one new light (t4, t5, t6, t7) with that light's provider.
- **Evaluation:** CROSSED over all 5 lights × 4 fleets × 20 traffic (`CITY_eval_f1.py`, each light with its own provider). The bootstrap is over light, fleet and traffic (`R.crossed`, 2 000 draws).
- **R:** per light, the same evaluator with `--spat-arm none` and fleet L11_s13 (the fleet falls back to σ\*), as R_k*_s13 on DEV.

**Gate (= §3), F1-scratch pooled vs R of the same light and traffic:**
- agent fuel upper < 0;
- city, agent and human TL upper < +0.5;
- teleports mean ≤ R + 0.1;
- unfinished ≤ R.

**F1-A1 is CONFIRMED** iff all of these pass.

**Reported, never gated:**
- the RULE reference: `RULE0_fleet.pt` (sha 4b8d4d3c46621e6f, zero residual = GLOSA-L∘σ\*), with the corrected provider q 0.1 under each new light, vs R;
- F1-scratch vs RULE (what learning adds);
- the own-light cells (fleet trained under t vs evaluated under t) vs the cross-light cells;
- commanded vehicle-seconds; spat valid share.

**Checks (exit 1, before the panel):**
- **KA-1:** light_spec patch: RL-H:0…3 return the same paths as unpatched; RL-H:4…8 return the m3_lights files (sha recorded).
- **KA-2:** convention check on the new traces (the KF-0 procedure applied to RL-H:t4…t8 traces): 0 error for the corrected ttg.
- **KA-3:** each closed-loop table covers all 16 grid4 lights.
- **KA-4:** traffic 530–549 did not exist before generation; the trainer reads only TRAIN 0–7 (KF-4 code unchanged).

**Predictions.**
- P-F1A1-1: F1-A1 is confirmed. Prior MODERATE. The fuel effect should transfer (−3.1 % on DEV with a CI far from 0), but DEV agent TL had an upper bound of +0.30, close to the +0.5 limit, and 16 of 20 light-fleet cells are cross-light.
- P-F1A1-2: RULE is worse than R in fuel and agent TL, as on DEV (+3.28 %, +2.18). So the benefit comes from adaptation, not from the rule.
- P-F1A1-3: Own-light cells are better than cross-light cells (descriptive).
* 21:12 — **Smoke** (scratch, light t4, 300 s episodes): trace → fit (16 lights) → prep → 1 training episode (light sha fb270118 = RL-H_t4.pt) → eval with the corrected provider → report on synthetic rows (it recovers the injected −3 % / +3 %). KA-2 logic on the smoke trace: 0 error on corrected ttr / ttg (green, yellow); the negative control (uncorrected green ttg) is −1 s on every observation. Regenerating grid4 seed 509 gives an identical file. **Frozen at launch:** CITY_f1a1_run.py a517bb07ea0e2da3; CITY_f1a1_prep.py 588f3e21827f6584; CITY_f1a1_checks.py 7584c38585a56b9f; CITY_f1a1_report.py cdec2d41061cee0e; RUN_chain.sh 97c5409d38784e8d; CITY_eval_f1.py 3b09b5aa39f42cc9; CITY_fleet_train_f1.py 9c413f20d3624261; CITY_m3_train_E.py 48458e5d0e14cc9b; CITY_spat_forecast.py f0fe94f9a7e76ae3; CITY_spat_forecast_c.py f4e4c5c233dd1eb3; 
* 21:13 — **Launch 1 failed before any job ran** (`traces/tmp` missing, so every trace job errored on its temp file; the fit step stopped the chain). Fix: `mkdir -p` added to RUN_chain.sh, new sha 56fde44a9b1c60cd. The failed logs are kept (`*_failed_tmpdir.*`). Relaunched.
