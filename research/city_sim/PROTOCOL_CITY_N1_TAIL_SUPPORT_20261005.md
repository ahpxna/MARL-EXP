# PROTOCOL — N1: is part of the forecast harm caused by answering beyond the tail support? (05/10/2026 00:01; registered before any N1 run)

**Hypothesis** (user list N1). When no recorded green of this light / green lasted longer than the current age, `ForecastK.rem` falls back to "the next decision tick" and still labels the answer as a valid forecast. Part of the frozen fleet's harm under the forecast arms comes from those answers.

**Provider** `CITY_spat_forecast_n1` (subclass of forecast-K; identical answers in mode `all`, check KN1-1). Every fleet query is labelled `local` / `pool` / `none` / `program`.

**Arms:**
- `all` (= c2);
- `tail`: `none` → `unavailable`;
- `strict`: `pool` or `none` → `unavailable`.

**Panels:**
- **grid4 (primary):** RL-H:k (k 0, 1) × frozen R10 (s13, s113), crossed. The closed-loop prep tables `m3_20261004/prep/prov_rlh<k>_cl.json`, q 0.1 (F1-locked). FRESH DEV **600–611** (generated in this job after a non-existence check). R = no SPaT.
- **spider (secondary):** the rule under RLK sp11 / sp111, DEV 100–109, the fkcl tables at q 0.1. R and `all` rows are the stage-3b DEV rows (C-89).

**Offline:** error by support state on the closed-loop traces (grid4 prep traces k0 / k1; spider s3b traces).

**Decision (registered):**
- SUPPORTED iff the tail exposure (the share of the fleet's forecast queries with support `none`) is ≥ 1 % AND tail − all agent fuel has an upper bound < 0, in at least one setting.
- REJECTED as a material harm source otherwise.
- Every arm vs R is reported. A win over R would be a baseline fix, not a method.

**Checks:**
- **KN1-1:** `all` ≡ provider c2 (CITY_eval_f1b fc2) bit-identical, one smoke seed.
- **KN1-2:** 600–611 did not exist before generation.

**Prediction.** Grid4 exposure is small (greens are short; C-91 grid4 durations p90 31 s), so N1 is rejected on grid4. On spider (max greens 500 s) the exposure is larger, but abstaining does not remove the harm (C-89's MAE 22 s is spread over all states). Prior for SUPPORTED: low.
