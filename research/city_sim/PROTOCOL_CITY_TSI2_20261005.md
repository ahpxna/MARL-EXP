# PROTOCOL TSI-2: per-light-tuned two-sided interface, the second and LAST confirmation (registered 05/10 ~01:50, after the TSI FAIL C-114, before any TSI-2 run)

## Why

- TSI failed only on agent time: +0.85 s/veh (upper +1.27), while agent fuel −4.56 %, city TL −0.20 and human TL −1.23 all improved.
- The cost was heterogeneous across lights (t4 +0.04 … t5 +1.36).
- The adapter is the agent-time lever (TSI − HYB: −1.05 s).
- One global (A, B) chosen on k0 / k1 under-predicted the cost.

## Method change (one change only)

- The light-side adapter (A, B) is tuned PER DEPLOYED LIGHT from that light's own TRAIN episodes, like its forecaster.
- Everything else is frozen as in TSI: hybrid forecast q0.5, per-light N2 one-shot fit, c2 tables `f1b_20261004/prep`.
- This is a deployment procedure (calibrate both interfaces per light from TRAIN data), not a choice on the confirmation panel.

## Per-light tuning (TRAIN only)

- **TUNE seeds** 660–663 (generated after a non-existence check; never used before); fleet L11_s13 (a development fleet).
- **Grid (A, B):** (1, 0), (1.5, 0), (2, 0), (1, 0.25), (1.5, 0.25), (2, 0.25), (1, 0.5), (1.5, 0.5), (2, 0.5), (3, 0.5); plus R per light.
- **Rule (registered, stricter than TSI's):**
  - per light, among configurations with agent TL point ≤ −0.25 and city and human TL points ≤ 0 (vs R on the TUNE seeds), the most agent fuel saving;
  - if none, the minimum agent TL;
  - ties → smaller A + B.

## Confirmation (one attempt; no added samples; the last for this method family tonight)

**Panel:** lights t4–t8 × frozen fleets s213 / s313 / s413 / s513 × reserved traffic **720–739** (generated after a non-existence check). Crossed bootstrap over light, fleet and traffic.

**Arms:**
- R;
- **TSI2** (per-light (A, B));
- HYB (service only);
- ADP2 (per-light adapter only);
- **F1B** (reference with retraining rights): the four F1-B fleets (F1B_s213_t4, s313_t5, s413_t6, s513_t7), each crossed with all five lights, using provider c2 q0.1 on that light's table (the F1-B recipe). R is fleet-independent (fleets fall back to σ\*), so F1B is compared with R on the same lights / traffic, fleet index i paired with s(213 + 100 i).

**Primary decision (α = 0.025 one-sided, because this is the second attempt; Bonferroni chain bound with the first TSI attempt 0.075):** TSI2 vs R meets every M3 limit at the one-sided 97.5 % upper bound:
- agent fuel upper < 0;
- city, agent and human TL upper < +0.5;
- teleports ≤ R + 0.1; unfinished ≤ R.
- PASS → M3 met by TSI-2 (scope: grid4, RL-H, R10, this panel).
- FAIL → M3 not met by the TSI family; reported as-is, with the mechanism and the component results.

**Secondary (descriptive, CIs):**
- TSI2 − HYB; TSI2 − ADP2;
- TSI2 − F1B (different rights; same panel);
- per-light chosen (A, B) and per-light TSI2 − R.
