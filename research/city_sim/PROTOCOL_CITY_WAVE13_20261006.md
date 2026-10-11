# PROTOCOL W13: fuel robustness and the retraining comparison (registered 06/10/2026, 23:1x, before any W13 result)

User request (06/10, 22:5x): improve TSI towards "always beats retraining" and "saves fuel in reality", in the order
2 → 3 → 1 → 4, then 5 and 6 (see the chat plan). Neither "always" is attainable:
- retraining under TSI weakly dominates TSI;
- simulation cannot certify field fuel.

The registered targets are therefore measurable:

- **(T1)** fuel non-inferiority of TSI to fleet retraining (margin +0.5 pp), with the M3 time limits;
- **(T2)** a fuel saving under both HBEFA4 and PHEMlight5 on the same trajectories;
- **(T3)** recalibration under IDM.

Panel: the W8-2 FRESH2 panel. It has five fresh learned lights t14–t18, frozen fleets s1013–s1313, the development fleet L11_s13, and the freshly retrained F1-B fleets of W8-2.

Fixed elements:
- Providers and models come from `w8_20261005/fresh2/{prep,cmodel}`. TUNE uses seeds 660–663.
- Emission model: HBEFA4 is the SUMO default. PHEMlight5/PC_EU4_G is set at departure through `CITY_w9_run.py em:` (the dynamics are unchanged).
- No existing script is edited. The new code is `scripts/CITY_w13_*.py`.
- Environment: PYTHONHASHSEED=0, OMP_NUM_THREADS=1.

## W13-1 (step 2): where the PHEMlight5 reversal comes from (descriptive)

### (a) Tuning grid under the second model and the second quantile

Grid:
- FRESH2 lights t14–t18 × C (10 adapter settings, as in TSI-2) × q ∈ {0.1, 0.5}.
- q is the quantile the hybrid provider publishes; the network already outputs both quantiles, so no refit is needed.
- Run under both HBEFA4 and PHEMlight5, on TUNE 660–663 with fleet L11_s13.
- The R rows are also run under PHEMlight5.

Existing rows reused: the q = 0.5 HBEFA4 rows (`fresh2/tune`).

**KM13-1a.** For every PHEMlight5 row, timeloss, n, teleports, unfinished and action_digest must equal its HBEFA4 twin. This is checked against the reused rows for q = 0.5 and against the new HBEFA4 rows for q = 0.1. Any mismatch stops the job.

### (b) Fuel by driving mode

`CITY_w13_modes.py` accumulates, every second and per vehicle, `getFuelConsumption` and vehicle-seconds in a grid:
- 3 acceleration classes: a < −0.1, |a| ≤ 0.1, a > 0.1 (m/s²);
- 5 speed bands: [0, 0.1), [0.1, 2), [2, 5), [5, 10), [10, ∞) m/s;
- separately for agents and humans.

Self-checks:
- **KM13-1b.** The grid total over all vehicles divided by the tripinfo fuel total of the same run must lie in [0.98, 1.02].
- **KM13-1c.** HBEFA4 rows must equal the corresponding W8-2 rows in timeloss and fuel. The smoke test passed at 23:0x: t14 × s1013 × seed 800, R arm, equal to the stored row; ratio 0.9998, and 0.9987 under PHEMlight5.

Runs:
- Arms R, HYB, TSI (the W8-2 choice), F1B × t14–t18 × fleet s1013 × traffic 800–803 × {HBEFA4, PHEMlight5}.
- Contrast under fixed time: R_FT and PL_FT (the fleet with exact SPaT) × s1013 × traffic 820–823 × {HBEFA4, PHEMlight5}.

Report: for each arm − R and each model, the change in agent fuel per agent trip split into the 15 cells. The cells are ranked by their share of the positive part of Δ_P5(TSI − R).

**Registered reading:**
- **"re-acceleration"** if cells with a > 0.1 at v ≥ 2 m/s carry > 50% of the positive Δ_P5(TSI − R);
- **"slow running"** if cells with |a| ≤ 0.1 at 0.1 ≤ v < 5 carry > 50%;
- **"idle credit"** if the negative Δ_H4 at v < 0.1 (idle avoided) is larger in magnitude than the total Δ_H4, and the P5 idle cell credits less than half of it;
- otherwise **"mixed"**.

This reading is descriptive. It only selects which W13-2b gate amendment, if any, is worth proposing.

## W13-2 (step 3) and W13-3 (step 1): selection rules and one confirmation

Per light, on the W13-1a tuning grid, define the qualifying set:

S = {(A, B, q) : agent TL ≤ 0, city TL ≤ 0, human TL ≤ 0}

Time losses are point differences against R over TUNE. They are the same under both emission models.

Two rules:
- **R13-F (step 1, fuel-aware):** argmin over S of fuel_H4.
- **R13-RB (step 3, robust):** argmin over S of max(fuel_H4, fuel_P5).

Shared conventions:
- Fuel is the agent fuel change against R in % (ratio of TUNE means, as in TSI-2).
- If S is empty, both rules fall back to the minimum agent TL.
- Ties: smaller A + B first, then q = 0.5.

### Confirmation (job 084)

Traffic: fresh grid4 traffic 900–919, generated only after checking that none of those route files exists.
Arms (each on t14–t18 × s1013–s1313 × 20, under both HBEFA4 and PHEMlight5, with the modes wrapper):
- R;
- TSIW8, the W8-2 choice;
- TSIF, rule R13-F;
- TSIRB, rule R13-RB;
- F1B, the W8-2 retrained fleets, same light–fleet pairing as W8-2.

Statistics:
- Every one-sided bound comes from the crossed bootstrap of `CITY_w6_report_v2`, B = 2000.
- Limits are the M3 set: fuel upper < 0, every time loss upper < +0.5 s/veh, teleports and unfinished trips not above R.

**D13-1, the retraining question (T1).** This is the second attempt after W8-2, so α = 0.025 one-sided.
- TSIF must meet every M3 limit against R under HBEFA4.
- TSIF − F1B relative agent fuel (HBEFA4) must have upper < +0.5 pp.
- If additionally the upper is < 0, the report states "TSIF saves more fuel than F1B on this panel".

**D13-2, two emission models (T2).** The PHEMlight5 question was tested descriptively in W9-3, so α = 0.025 one-sided.
- TSIRB must meet every M3 limit against R.
- TSIRB − R agent fuel must have upper < 0 under PHEMlight5 and upper < 0 under HBEFA4.

**Descriptive arms:**
- TSIW8 − R and F1B − R under PHEMlight5. This shows whether the retrained fleet also loses its saving under PHEMlight5; if it does, the reversal is a property of fleets trained on HBEFA4, not of TSI.
- TSIRB − F1B and TSIF − TSIRB.

**Self-check:** PHEMlight5 rows equal their HBEFA4 twins in time, n, teleports and unfinished (KM13-1a); KM13-1b holds on every row.

## W13-2b (step 3, conditional): uncertainty gate

Run only if W13-1b reads "re-acceleration" and D13-2 fails.
- Design: the hybrid provider withholds the learned forecast when its interval width (q0.5 − q0.1) exceeds τ ∈ {5, 10} s. Yellow answers stay exact.
- This is a new provider wrapper, registered by amendment before launch, with α = 0.0125 as a third attempt at T2.

## W13-4 (step 4): iterated closed-loop refit

Design, with implementation details registered by amendment before launch:
- Up to two rounds on FRESH2 lights.
- Each round collects features with the development fleet while TSI is published:
  - the adapter and q are the R13-RB choice if D13-2 passed, otherwise the R13-F choice;
  - the 8 original TRAIN episodes are used.
- Each round refits the network (same architecture and loss) and checks offline–online parity (zero mismatches).
- Each round is evaluated on TUNE under both models.
- Keep the round with the lowest max(fuel_H4, fuel_P5) among those meeting S; round 0 counts as a candidate.
- Confirm once on fresh traffic 920–939 against R and F1B. D13-1 and D13-2 are repeated at α = 0.0125 (third attempts).

## W13-5 (step 5): retraining on top of TSI

- F1B-T: a fleet trained from scratch for 200 episodes, exactly as F1-B, but under the upgraded signal with TSI in force (adapter plus hybrid provider).
- One fleet per light, with the same pairing as F1-B.
- Confirmation on fresh traffic 940–959 under both models.
- **D13-4** (α = 0.05, first attempt): F1B-T meets the limits, and F1B-T − F1B fuel upper < 0. In words: the light-side half adds what fleet retraining alone cannot.
- Implementation by amendment before launch.

## W13-6 (step 6): IDM, then a real network

- **(a) IDM.** Policies stay frozen. The forecast tables, the network and the adapter grid are refitted under IDM, with the same recipe and seeds. Confirmation under IDM on fresh traffic 960–979.
  - **D13-5** (α = 0.05): every M3 limit holds and fuel upper < 0 under HBEFA4. PHEMlight5 is reported descriptively.
- **(b) Real network.** A separate protocol, because it needs new learned signals and fleets: InTAS or RESCO, with a loop-presence detector model.

## Order and stopping

- Jobs 083 (W13-1) then 084 (W13-2/3) run on the sequential spool.
- 085 and later (W13-4 … 6) are added only after their amendments.
- A failed self-check stops its job, and no report is written.
- No rule above is changed after its rows are seen. A failed decision is reported as "not shown" and does not reopen the rule.

## Amendment A1 (23:1x, 06/10): implementation of W13-4, W13-5 and W13-6a

Written before any W13 result: job 083 is still running, and 084–087 have not started.

### Order and seeds

- The spool runs 083 → 084 → 085 → 086 → 087.
- Seeds:

| Step | Job | Fresh traffic |
|---|---|---|
| W13-4 | 086 | 920–939 |
| W13-5 | 085 | 940–959 |
| W13-6a | 087 | 960–979 |

- Each job generates its traffic only after a non-existence check.
- W13-5 is placed before W13-4 because its configuration (the W8-2 TSI) does not depend on 084.

### W13-5 (085, `CITY_w13_train_f1bt.py`)

- **Training.** The F1-B trainer is used unchanged, with two substitutions:
  - the provider becomes the W8-2 TSI fleet side, N4 hybrid at q = 0.5 on the light's network and table, with its tracker stepped after the cars;
  - the light becomes LightRLX with the light's W8-2 adapter.
- Fleets: seed s(1013 + 100i) is trained under light t(14 + i), i = 0..3, for 200 episodes from scratch, as for F1-B.
- The trainer's `--table`/`--q` arguments are ignored. The saved file records `w13_tsi`: the provider, the adapter, model and table hashes, provider counters and the light class.
- Smoke: 11,067 provider queries over 2 short episodes, 3,510 of them answered by the hybrid branch, light class LightRLX.
- **Arms.** Five arms, crossed over every light as in W8-2:
  - R;
  - TSI;
  - F1B;
  - F1BonT (the F1B fleet under TSI; descriptive);
  - F1BT.
- **Decision.** D13-4 as registered, at α = 0.05.

### W13-4 (086, `CITY_w13_refit.py`)

- **Configuration.** R13-RB if 084's D13-2 is SHOWN, else R13-F.
- **Rounds.** For r = 1, 2:
  - collect TRAIN 0–7 with the development fleet, with round r−1's network published (`CITY_eval_n4f`);
  - fit with `CITY_n2_fit`;
  - check KF-2 parity on t14.
- **Tuning.** TUNE rows are run for R and for rounds 0–2 under both emission models.
- **Selection.** Per light: argmin of max(fuel_H4, fuel_P5) among the rounds meeting S; if none meets S, round 0.
- **Confirmation.**
  - Arms: R, TC (round 0), TREF (the chosen round), F1B.
  - Decisions D13-1′ and D13-2′ at α = 0.0125.

### W13-6a (087, `CITY_w13_idm.py`)

**Why a new wrapper.** CITY_w9_run's idm mode patches only CITY_eval4.run_episode. The closed-loop table prep (CITY_m3_train_E.prep) calls CITY_env.run_episode directly. The new wrapper patches both, and can set the emission class through W13_EM.

**Self-checks.**
- KI-1 passed at 23:08: the wrapper reproduces the W9-4 row R_IDM_t9_s613, seed 780, bit for bit (timeloss 24.5290).
- KI-0 reads the type's carFollowModel parameter, which libsumo returns as '' here. It is therefore not discriminating, and KI-1 is the operative check.

**Recipe.** The FRESH2 calibration recipe is run under IDM, with seeds unchanged:
- traces at σ 0.3;
- open-loop tables;
- closed-loop c2 prep, checked by KF-3;
- N2 logs and fit, checked by KF-2;
- the adapter grid with the TSI-2 rule (CITY_w7_tune).

**Arms.** R, TSIK, TSII and F1B, under IDM, with HBEFA4 and PHEMlight5.

**Decision.** D13-5 at α = 0.05.

### Smokes

All three smokes (085, 086, 087) passed end to end on short budgets, in the scratchpad.
