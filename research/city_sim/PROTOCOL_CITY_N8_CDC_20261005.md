# PROTOCOL N8: a predictable split controller as a structural baseline (registered 05/10 ~00:40, before any CDC run)

**Hypothesis N8** (`METHOD_HYPOTHESES_NIGHT_20261004` §2; literature S02 HONEST-CAV, S03 DHCP):
- Part of M3's cost comes from forcing keep / switch commitments on RL-H.
- A light whose action space is predictable by construction (it commits each green's duration at its onset) may keep the frozen fleet's benefit more cheaply.
- This is a baseline (a port of the idea, not those papers' algorithms). It is not a new method.

## Controller

**CDC(θ):** at every green onset of a light (static program; the yellows follow the program), it commits

  d = clip(θ0 + θ1·n_cur + θ2·n_oth + θ3·h_oth, 5, 60)

once, via setPhaseDuration.
- n = vehicles and h = halting on the lanes served by the starting green (cur) or the other green (oth).
- The fleet's SPaT is the program SPaT (`CITY_spat_feature.spat`). It is exact by construction for the current phase and the following yellows.
- **KN8-1:** a 1-in-10 sample of queries is compared with the realized link-state change. Any mismatch stops the job.
- Rights: replaces the learned light (a different light upgrade). The fleet is frozen (R10 L11_s13; s113 = transfer). Inputs: counts / halting on served lanes, the same sensors as RL-H.

## Tuning (TRAIN only; common random numbers)

- CEM over θ ∈ [5, 40] × [0, 3] × [−3, 0] × [−3, 0]: population 12, 3 elites, 5 iterations, TRAIN seeds 0–2, fleet s13.
- **Variant m3:** CDC + fleet with program SPaT. J = agent fuel % vs R + 5 · Σ max(0, ΔTL) over city / agent / human TL. R = RL-H k0 + no SPaT on the same seeds.
- **Variant city:** CDC + fleet without SPaT. J = city TL (a light tuned for traffic alone).
- **Selected θ = the final CEM mean** (registered; the best single candidate is reported, not used).
- Budget: 2 × 5 × 12 × 3 = 360 TRAIN episodes, plus 3 R episodes.

## DEV evaluation (600–611; R = RL-H k0 / k1 + no SPaT; crossed bootstrap, CDC rows paired with each R_k)

- CDCm3 / CDCm3sig, CDCcity / CDCcitysig (with / without SPaT);
- FTp / FTsig (the static FT program with / without SPaT; the old light);
- fleets s13 / s113.

## Decisions (registered)

- **N8 CANDIDATE (variant v):** CDCv + fleet vs R meets every M3 limit:
  - agent fuel upper < 0;
  - city / agent / human TL upper < +0.5;
  - teleports ≤ R + 0.1.
  - A candidate is a DEV result. It is then frozen and confirmed (700–739, new fleets) against RL-H + the best SPaT service (N2 / N4).
- **N8 SUPPORTED (mechanism):** for some v, both of:
  - the fleet contribution under CDCv (CDCv − CDCvsig) has agent fuel ≤ −3 %;
  - the light alone (CDCvsig vs R) has city TL upper < +0.5.
  - Read as: a predictable controller of RL-H quality keeps the fleet benefit.
- Otherwise REJECTED for this parameterization: one 4-parameter rule family, CEM budget as above.

## Amendment A1 (00:47, before any CEM or DEV run)

**KN8-1 failed at smoke:** 64 / 1440 sampled queries were off (4.4 %).
- Cause: during the yellow that precedes the other green, the program SPaT used the program's static duration (42 s) for the next green. That green had not been committed yet.
- The check works (it can fail).

**Fix (`CITY_eval_n8.py`):**
- The next green's duration is now decided and committed at the onset of the yellow that precedes it, from the counts at that second. It is applied at the green onset. The very first green is decided at its onset.
- The fleet's SPaT uses the committed plan for future greens. A future green without a commitment answers `unavailable`. Yellows are static, hence exact.
- The controller family, the CEM, the decisions and the budget are unchanged.

The failed job file and its log are kept: `queue_night_20261005/failed/032_N8_cdc.sh`, `logs/032_N8_cdc.log`. The rerun is `032b_N8_cdc.sh`.

**A1 rerun note (01:00):** the rerun 032b also stopped at smoke, for a reason unrelated to the fix. E4 skips an existing tag, so the old SMK.json from the first attempt made the smoke a no-op (0 checked → KN8-1 refuses, as designed). The old smoke files were moved to `n8_20261005/check/legacy_smoke_v1/` (kept). The job is requeued as `035_N8_cdc.sh`, unchanged.

## Amendment A2 (01:13, before any CEM or DEV run)

**KN8-1 failed again at smoke:** 71 / 1488 (4.8 %).
- Cause: `setPhaseDuration(d)` was called at the first OBSERVED second of a green, when that green had already run 1 s. The green therefore lasted d + 1 s from its actual start.
- Answers spanning a future green (queries during the preceding yellow) were off by exactly 1 s.

**Fix:** the remaining time is set to max(1, d − getSpentDuration), so each green lasts d from its actual start, which the SPaT's plan uses. Nothing else changes.

The old smoke files are kept in `check/legacy_smoke_v2/`. The job is requeued as `036_N8_cdc.sh`.
