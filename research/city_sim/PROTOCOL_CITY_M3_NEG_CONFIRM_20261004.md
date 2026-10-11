# PROTOCOL — M3-NC: confirming the light-side NEGATIVE of M3 on a fresh panel (04/10/2026 21:22; registered before any M3-NC run)

## Why

M3 asks for a light-side method that returns the light upgrade's benefit to the FROZEN fleet at less light cost than the strongest commitment baseline (finish-line M3).

Every light-side candidate stopped at DEV under registered gates:
- E family (C-68);
- W-c and B-ETA (C-68);
- RPC (C-79).

These are DEV negatives. M3 is "complete" only with a confirmed negative whose reason is named. This protocol tests, on data none of the DEV choices saw, whether the two strongest and cleanest light-side mechanisms are WORSE for the frozen fleet than the no-SPaT fallback, and why.

No candidate is tuned here. Every arm is exactly its DEV definition.

## Panel

- **Traffic:** fresh grid4 510–529 (reserved for the M3′ confirmation, which was never opened; generated now with the verified grid4 command after a non-existence check).
- **Lights:** the five new RL-H seeds t4…t8 (`CITY_f1a1_run` light_spec patch, KA-1). Provider tables are the F1-A1 closed-loop tables `f1a1_20261004/prep/prov_rlh<t>_cl.json`, made with the M3 prep procedure (KA-2 / KA-3 PASS).
- **Fleets:** the four M3 confirmation fleets, frozen R10 L11_s213 / s313 / s413 / s513.
- **Evaluation:** crossed over 5 lights × 4 fleets × 20 traffic; bootstrap over light, fleet and traffic (`R.crossed`, 2 000 draws).

## Arms (unchanged DEV definitions)

| Arm | Definition |
|---|---|
| R | RL-H:t + `unavailable` (fleet → σ\*). Rows per light; fleet-independent by KM2-2, checked once here (R with s213 ≡ R with s313 on light t4, traffic 510). |
| **WC5** (primary 1; the DEV-best comparator) | `M3WC:t:5` + `commit:<table>`: commitment while pending, else forecast 0.5 of the table, UNcorrected. |
| **RPC-receiver** (primary 2; the clean commitment) | `RPC:t:receiver`: commitment or `unavailable`. |
| WC5-c (descriptive, NEW, declared) | `M3WC:t:5` + commitment while pending, else the convention-CORRECTED forecast at the F1-locked q 0.1. Addresses the C-71 confound in WC5's fallback. It is never gated, and it could only open a new registered test, not a claim. |
| Shadow rows (clean decomposition, A2) | WC5 with σ\* cars (`--base-sigma 0.3 --fleet L-ACT:0 --guard always`; W-c is fleet-blind) per light; RPC with `SHADOW:<fleet>` (`CITY_eval_m3p_shadow`) per light × fleet. |

## Endpoints

- **M3-1:** agent fuel % vs R.
- M3-2 TL is reported.
- **M3-4clean, light cost:** shadow − R (agent fuel %, city TL).
- **M3-3clean, fleet contribution:** fleet − shadow (agent fuel %).
- By construction, M3-1 = M3-4clean + M3-3clean (fuel % on the same rows, up to ratio composition).

## Decision rule (per primary arm)

- **NEGATIVE CONFIRMED:** the one-sided 95 % LOWER bound of M3-1 agent fuel > 0, i.e. significantly worse for the frozen fleet than having no SPaT at all.
- **NOT SHOWN BETTER:** the upper bound ≥ 0 but the lower bound ≤ 0.
- **Positive:** upper < 0. This would contradict DEV and is reported as such; it is not a method claim without its own confirmation.
- **Reason named** iff light cost (M3-4clean, agent fuel lower > 0) AND fleet contribution (M3-3clean upper < 0) are both established. Then the reading is "the fleet gains from the exact messages, but the light cost of making them exact is larger".

**M3 completion statement (written only if both primaries are NEGATIVE CONFIRMED):** "Under the learned light RL-H on grid4, the light-side mechanisms tested (fixed-window and receiver-triggered commitment) make the frozen SPaT fleet worse off than the no-SPaT fallback, on new lights, fleets and traffic. The exact timing they publish helps the fleet less than holding the light costs."

## Checks (exit 1, before the panel)

- **KN-1:** WC5 and RPC on light t4, fleet s213, traffic 510: 0 commitment violations (end and onset).
- **KN-2:** WC5-c differs from WC5 only in the non-pending SPaT. While pending, both return the commitment (one-episode comparison of the commitment-source query counts > 0 in both).
- **KN-3:** R identity across fleets (above).
- **KN-4:** 510–529 did not exist before generation.

## Predictions

| # | Prediction |
|---|---|
| P-NC-1 | WC5 NEGATIVE CONFIRMED (DEV +3.60 [+2.77, +4.26]). Prior: high. |
| P-NC-2 | RPC NEGATIVE CONFIRMED (DEV +9.40). Prior: high. |
| P-NC-3 | Light cost > 0 and fleet contribution < 0 for both (DEV: WC5 −1.49 %, RPC −0.62 %), so the reason is named. Prior: moderate for RPC, whose fleet contribution upper bound on DEV was −0.19. |
| P-NC-4 | WC5-c is better than WC5 (corrected fallback), still worse than R. Descriptive. |

* 21:24 — **Frozen at launch:** CITY_eval_m3nc.py e777bb1563538f30; CITY_m3nc_check.py dc84f476c8b08321; CITY_m3nc_report.py a9c280b67e97e7a4; RUN_m3nc.sh 651101744ee23b25; CITY_eval_m3.py 6ee43e55d635247b; CITY_eval_m3p.py a877207461de65f9; CITY_eval_m3p_shadow.py 0b406dee5d0bd54a; CITY_m3p_rpc.py 89ed42e7b2b269d9; CITY_f1a1_run.py a517bb07ea0e2da3; 
