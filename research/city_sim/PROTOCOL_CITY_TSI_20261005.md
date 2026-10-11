# PROTOCOL TSI: a two-sided interface between two frozen learned populations (registered 05/10 ~01:02, before any TSI selection run)

## Why

- HYBQ (C-106) is the strongest arm so far, at an untuned adapter: −4.40 % agent fuel, city TL −0.34, human −1.09, agent TL +0.39 (upper +0.67).
- X3 (C-107): exact timing costs the frozen fleet no time. The remaining time cost is forecast error.
- N2M (C-100): the eco fleet hides its demand from the halting-based light.

## Method (both populations frozen; only the two interfaces between them change)

1. **Fleet-side service.** The hybrid forecast:
   - where the light's schedule is determined (yellow phases), the exact program answer (provider c2);
   - elsewhere the state-conditioned quantile forecaster at q0.5 (N2; or N2P, if registered by Amendment before the SELECT run that uses it).
2. **Light-side demand adapter.** In front of the frozen RL-H's halting features:
   q = halting + A·count(0.1 ≤ v < 2) + B·count(2 ≤ v < 5) on the served lanes.
   - Light weights are frozen.
   - Rights: a sensor definition at the infrastructure (speed bins on the served lanes, as existing detectors / V2I can provide).

**Related work to beat or distinguish:**
- DC-Ada (observation transforms for one frozen policy);
- HONEST-CAV (policy-aware SPaT);
- integrity gating;
- retraining (F1-B).

No novelty claim before confirmation and the ablations.

## SELECT (650–655; k0 / k1 × fleet s13; R rows from n4_20261005/sel)

- Grid (A, B) ∈ {(0, 0), (1, 0), (1.5, 0), (2, 0), (1, 0.25), (1, 0.5), (1.5, 0.25), (2, 0.25)}, with the hybrid forecast at q0.5 (16 jobs × 6 seeds).
- **Selection rule (aligned with the M3 gate, registered):**
  - Among configurations whose SELECT points have agent TL ≤ +0.20 and city / human TL ≤ +0.20 (vs R), choose the most negative agent fuel.
  - If none qualifies, choose the minimum agent TL.
  - Ties: the smaller A + B.

## Confirmation (registered now; run only after SELECT and the per-light fits; one attempt; no added samples)

**Panel:**
- **Lights:** RL-H t4…t8. Five independent seeds via the F1-A1 light_spec patch; used before only to evaluate F1 fleets, never to choose any M3 service.
- **Fleets:** frozen R10 L11_s213 / s313 / s413 / s513, never used in M3 / N development.
- **Traffic:** 700–719 (20 seeds; generated after a non-existence check).
- Crossed 5 × 4 × 20 = 400 episodes per arm. Crossed bootstrap over light, fleet and traffic (2000 draws).

**Per-light pipeline (TRAIN only, identical to N2):**
- c2 table = the F1-B refit `f1b_20261004/prep/prov_rlh<t>_cl.json`;
- 8 collection episodes (TRAIN 0–7, fleet L11_s13 using c2 on that light);
- `CITY_n2_fit.py` → `n2_t<t>.pt`.
- Checks: KT-1 (KN2-style parity) on one light; KT-2 (hybrid share > 0).

**Arms:**
- R (no SPaT);
- **TSI** (hybrid q0.5 + adapter A\*, B\*);
- HYB-only (no adapter);
- ADP-only (σ\* fleet + adapter).

**Primary decision (one-sided 95 %).** TSI vs R must meet every M3 limit:
- agent fuel upper < 0;
- city, agent and human TL upper < +0.5;
- teleports ≤ R + 0.1; unfinished ≤ R.
- PASS → M3 met by TSI on this panel (claim scoped to grid4, RL-H, R10).
- FAIL → reported as-is, no second attempt on this panel.

**Secondary (component value, descriptive with CIs):**
- TSI − HYB-only (value of the light-side adapter);
- TSI − ADP-only (value of the fleet-side service).
- F1-B is a reference with more rights; it is not on this panel.

## Amendment A1 (01:02, before any TSI run): forecaster variant chosen on SELECT

**Variant "refit under the deployed interface"** (N3(b)'s idea, made specific):
- The N2 forecaster was fitted on data where the fleet used c2 and the light saw raw halting.
- Under TSI, both the fleet's behaviour and the light's input change, so the forecast target shifts. The refit pipeline is:
  1. TRAIN 0–7 × k0 / k1 (fleets s13 / s113, as N2), running TSI(A\*, B\*) with feature logging (`scripts/CITY_eval_n4f.py`, identical to the N4 evaluator plus `--featlog`);
  2. the unchanged `CITY_n2_fit.py` → `tsi_20261005/model/n2_k<k>.pt` (one round, same data count as one-shot);
  3. TSI-refit on SELECT 650–655 (k0 / k1 × s13).

**Choice** between one-shot and refit at (A\*, B\*): the SELECT rule above, applied to these two configurations. The confirmation pipeline per light follows the chosen variant: for refit, c2 collection → fit → TSI collection → refit, all on TRAIN.

## Note N1 (01:23; description only, no change to the frozen design)

**Correct description of the fleet-side service.** In every yellow phase the query is answered by c2.
- That answer is exact only when the target green is the one right after the yellow.
- For a link waiting through an intermediate green, it is c2's age-only forecast (offline MAE 3.7 s at 5–15 s and 14.4 s at ≥ 15 s).
- See C-113. The implementation is unchanged during the confirmation.

KT-1 runs as queue job 033 after the panel. No self-check claim is made before it passes.
