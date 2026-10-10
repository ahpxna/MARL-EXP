# PROTOCOL: B6, a fleet that beats human driving (development screen)

Written 04/10/2026 05:22 EDT (wake 3), before any v3 training.

## Motivation

Ledger C-17: no Q7 / Q7b fleet beats SUMO's human model on the same vehicles, on time or fuel, even under its own training light. C-18: always-SUMO beats every guarded variant. A staged-upgrade study needs a population with a benefit to protect.

## Candidates (development; SELECT traffic 100–104 only)

| Candidate | Recipe | Source |
|---|---|---|
| v2 | CarRLv2, realized idle | Job 020: L-ACT-v2_t0 / t1 against ACT |
| v3 | `scripts/CITY_fleet_train_v3.py`: cost = (1 − v′/v_allowed) + 0.5 · fuel′(mg/s)/1000 on REALIZED quantities one second later; 120 episodes against ACT; DQN seeds 13 / 113 (same as L-ACT_t0 / t1) | Smoke OK; fuel units checked: mg/s, idle ≈ 490, moving ≈ 790, max ≈ 3000 |

## Criterion B6-1 ("beneficial fleet"; registered here, read on SELECT)

Under ACT, the agent vehicles driven by the fleet vs the SAME vehicles in the human-only run (always-SUMO, identical membership):
- agent fuel change with one-sided 95 % upper bound < 0 (fuel saved);
- agent TL change with one-sided 95 % upper bound < +0.5 s/veh (non-inferior on time).

Bootstrap: traffic seeds, 2000 draws, rng 0; one fleet seed at a time.

## Readings

- **A v2 or v3 fleet passes** → it becomes the deployed F0 for the staged-upgrade program (A-L and A-F re-run on it in development, then the confirmation panel).
- **None passes** → the fleet action space / observation, not only the reward, is the bottleneck. Report it and do not run compatibility claims on non-beneficial fleets.

## Jobs

- `035_B6_v3_train`: 2 trainings, 2 lanes.
- `036_B6_eval`: v2 and v3 fleets × {ACT, RL-H_0..3} × SELECT, via CITY_eval3, plus the B6-1 analysis in CITY_wave2_report_v2 section b6.
* B6 jobs: 035 909f0200e0f7, 036 5ab47a95b04b; CITY_fleet_train_v3.py 5f35065e4685fdd0
* report v2 + section b6 sha d019e84dabab3389 (05:22, before 036 ran)

## Amendment B6-A1 (05:31 EDT, user audit Addendum B6, before any v3 training or B6 evaluation ran)

**1. Reading corrected.** The line "None passes → the fleet action space / observation … is the bottleneck" is WITHDRAWN. If no candidate passes, the only conclusion is:

> No beneficial fleet was found under the B6 criterion in the recipes tried.

Two seeds, one fuel weight (0.5), one DQN recipe and the approach-zone horizon do not separate optimization, data, horizon or reward scaling from information or action limits. A later diagnostic, not a new branch now: the action set has no "release to SUMO" action, so the policy class may not contain the baseline it must beat. An explicit release action, or a residual / distilled policy on the SUMO driver model, would test that.

**2. Reward-v3 conventions (published, counted by `scripts/CITY_v3_trace_check.py`):**
- An API read failure gives cost 0.
- An arrived car's terminal cost is 0.
- The reward covers only the approach zone (≤ 200 m before the next light); the endpoint is whole-trip. The discounted approach reward is NOT the full-trip time loss + fuel objective. Tripinfo timeLoss uses SUMO's ideal speed (with speedFactor); fuel_abs is the trip total.

Smoke trace (ACT, 900 s, random commands):

| Check | Result |
|---|---|
| Transitions | 61 491 non-terminal and 509 terminal match −[(1 − v/v_allowed) + 0.5·fuel/1000]; 0 bad, 0 unattributed |
| Fuel consistency | Per-trip sum of the logged fuel rate × 1 s vs tripinfo fuel_abs: median −0.03 %, p95 \|rel\| 0.43 % |
| Time-loss consistency | Summed (1 − v/v_allowed) − tripinfo timeLoss: median −0.02 s |

Job 034 runs the full horizon with FT (teleports) and RL-H_0, so the arrival, teleport, gap and truncation paths are exercised and counted. **Job 035 refuses to train unless jobs 021 (v2) and 034 (v3) are both PASS.**

**3. B6-1 is a development SCREEN.** Four candidates (v2 / v3 × policy seeds t0, t1) on five SELECT traffic seeds. A pass selects a candidate RECIPE; it does not show "the learner is beneficial". The screen also reports, against always-SUMO (= SUMO's default driver model, NOT data from real human drivers), each with a one-sided bound:

| Quantity | Requirement |
|---|---|
| agent fuel | superiority |
| agent TL | NI +0.5 s/veh |
| human-vehicle TL | NI +0.5 s/veh: no cost shifted to other drivers |
| city TL | reported |
| teleports per run | not above always-SUMO + 1 |
| unfinished trips | not above always-SUMO |

**4. B6-2 recipe confirmation** (job 037, run only for a recipe with ≥ 1 passing seed):
- Retrain that recipe on NEW policy seeds t = 2, 3 (DQN seeds 213 / 313, never trained under v2 / v3).
- Evaluate on FRESH traffic 400–409, generated 05:31 with the identical generator, never used. 300–319 stay reserved for the program's final confirmation.
- "Beneficial fleet recipe" requires the B6-1 criteria to hold on BOTH new seeds, on 400–409.

**5. Wording.** In every new document, "human" means SUMO's default driver model (Krauss), not real human drivers.

**6. Order.** 021 (v2 trace) → 034 (v3 trace) → 035 (v3 training, gated) → 036 (B6-1) → 037 (B6-2, gated). The exploratory jobs on non-beneficial fleets run after these (030 → 041, 040 → 042, 055 → 043, 080 → 044, 090 → 045). Adapter (060), DC-Ada (070) and handoff (095) are HELD until a beneficial candidate exists.
* B6-A1 freeze (05:32): CITY_v3_trace_check.py 7cf9cecedf519f47; CITY_wave2_report_v2.py cd9b0ad1cf2b9f34 (b6 / b6c sections, written before 036 / 037 ran); jobs 034 b88d0b01f42c, 035 a615eb9d8012 (gated on 021 + 034 PASS), 037 e283b0f07cbe (gated on a B6-1 pass); demand rou_s400..409 generated with the identical generator.

## Prepared, NOT queued (05:45): the policy-class diagnostic for a negative B6 (B6-A1 §1, audit item 6)

`scripts/CITY_fleet_train_v4.py` (sha 2a6961936740f407), reward v3, two action sets:
- `release` = ACC + "release to SUMO for this second";
- `residual` = δ ∈ {−3, −2, −1, 0, +1} m/s added to SUMO's own next speed (`getSpeedWithoutTraCI`). δ = 0 is close to, not identical with, SUMO's choice.

Smoke: 2 × 300 s episodes each, scratchpad, saved. These are known recipes (explicit fallback, residual policy); they are not a novelty.

Use, only if B6-1 / B6-2 are negative after the validity checks: does a policy class that contains the baseline reach or beat it? Before it runs, an evaluator that understands these action sets must be added: `CITY_eval3` maps only the 6 ACC actions. That will be a new version, not an edit of eval3.
* CITY_eval4.py 8648077de023608e (prepared 05:47; eval3 behaviour unchanged for ACC fleets: ACT x L-ACT_0 = h0; v4 smoke checkpoints evaluate)

## Decision tree after B6 (registered 05:47, before any B6-1 row exists)

### Branch P: a recipe passes B6-2 (beneficial on BOTH new seeds, fresh traffic 400–409)

The recipe becomes the deployed fleet F*. The light-upgrade study (A-L) is re-run on F*, on development seeds (SELECT 100–104, then VALIDATION 200–209). The endpoints are fixed now:

| | Prediction | Supported iff |
|---|---|---|
| AL*-1 | F* regresses under a learned light | Agent TL(F* \| RL-H_t) − agent TL(F* \| ACT) > 0, crossed CI lower > 0 over RL-H_0..3 × F* seeds × traffic |
| AL*-2 | **The key endpoint: the fleet's benefit survives the light upgrade.** Under RL-H_t, F* (plain, or with the best guard chosen on SELECT) beats always-SUMO on agent fuel and is non-inferior on agent TL | Fuel upper < 0, TL upper < +0.5, judged on VALIDATION |
| AL*-3 | Partner protection | Human-vehicle TL NI (+0.5) vs always-SUMO under the same light |
| AL*-4 (reported) | Where it is repaired | input (τ-clip) vs reaction (fallback / green guard) vs rights (cap); release shares |

If AL*-1 fails (F* is robust to light upgrades), the A-L compatibility problem does not arise for a beneficial fleet. That is reported as a main result: the earlier fragility belonged to the reward-loophole fleets.

### Branch N: no recipe passes

The conclusion is limited to "not found in the recipes tried" (B6-A1 §1). Then the policy-class diagnostic runs (prepared: `CITY_fleet_train_v4.py`, `CITY_eval4.py`):
- `release` and `residual`, reward v3, against ACT;
- policy seeds t0, t1;
- B6-1 criteria vs always-SUMO.

| Outcome | Reading |
|---|---|
| A v4 class passes | The ACC class could not represent the baseline. That is a control limit of the old action set, not of RL. |
| v4 fails too | Recipe, horizon and optimization remain open. No compatibility work runs on these fleets. |

In both branches, the confirmation panel (traffic 300–319, policy indices 4–8) stays untouched until a method is frozen.
* Branch-P job generator CITY_make_alstar_jobs.py 4472b9c4ebcde13d (05:49); appended to job 037, which now has sha bcc7aff657d7); writes 038_ALstar_select only if a recipe passes B6-2 on both new seeds

## B6-1 result (05:49) and the registered branch

**All four candidates FAIL B6-1**: v2_t0, v2_t1, v3_t0, v3_t1. Every one is worse than always-SUMO on agent fuel AND agent TL (report in `wave2_20261004/report_v2_b6.txt`). No recipe has a passing seed, so B6-2 is not run (gate). **Branch N.**

## B6-D1, descriptive diagnostic of the failure (written 05:51, before it runs)

Expectation, mechanism H-crawl-v2. Under v2 a stopped car costs 2 per second (time + idle) while a car crawling at ≥ 0.1 m/s costs 1. The reward therefore pays the fleet to crawl instead of stopping, which blocks the queue.

Measurement, under ACT, seeds 100–101, no hypothesis test: the share of agent zone-seconds halted (v < 0.1), crawling (0.1 ≤ v < 2) and moving, for always-SUMO, v1 (L-ACT_0), v2_t0 / t1 and v3_t0 / t1.

Expected: v2 crawl share ≫ v1 and ≫ always-SUMO. If not, H-crawl-v2 is dropped and other causes (optimization, horizon) stay open.

## B6-N: policy-class diagnostic (Branch N), run as job 039 — predictions registered 05:53, before training

Fleets: `CITY_fleet_train_v4.py` (`release`, `residual`) × policy seeds DQN 13 / 113, reward v3, against ACT, 120 episodes. Evaluation: `CITY_eval4.py` under ACT, SELECT 100–104, vs always-SUMO (B6-1 criteria, same report function). Two predictions:

| | Prediction | Supported iff |
|---|---|---|
| N-1 | The `release` class at least REACHES the baseline | Agent TL upper < +0.5 and agent fuel upper < +1 %, for ≥ 1 of 2 seeds. A class containing the baseline should learn to use it. |
| N-2 | The `residual` class does better than the baseline | B6-1 PASS (fuel upper < 0, TL upper < +0.5, human TL NI, teleports, unfinished) for ≥ 1 of 2 seeds |

**Readings:**

| Outcome | Reading |
|---|---|
| N-1 holds, N-2 fails | The learner can recover the baseline but finds no improvement on it: a recipe / objective limit |
| N-1 fails | Even with the baseline inside the class, this DQN recipe does not find it: an optimization / data problem, not the action set |
| N-2 holds | Candidate recipe → B6-2 confirmation (new seeds 213 / 313, traffic 400–409) before any upgrade work |
* 039_B6N_v4 7ff84685373f; CITY_fleet_train_v4 2a6961936740f407; CITY_eval4 8648077de023608e; CITY_b6_speed_profile 440a75720932f32d
* prepared (not queued) CITY_fleet_train_v5.py 1633c9e3d7d6ade1: B6-R recipe screen (reward v3 / CoTV Eq. 2 as cost; actions acc / release / residual; episodes; gamma)

## After 039 (registered 05:56, before 039 ran): automatic next job (`scripts/CITY_make_b6_next.py`, appended to job 039)

**(a) A v4 class has a B6-1 passing seed** → job `040_B6_2_v4`. That recipe goes to B6-2: new policy seeds DQN 213 / 313, fresh traffic 400–409, always-SUMO on the same traffic. B6-1 criteria on BOTH seeds are required to call it a beneficial recipe.

**(b) No v4 pass** → job `040_B6R_recipes`, the recipe / horizon screen (user step 4). The question is whether budget or a published objective changes the answer. Development, SELECT 100–104, seeds DQN 13 / 113, 480 episodes each (4× the earlier budget; CoTV trained on about 4.5× ours in simulated seconds):

| Arm | Reward | Actions |
|---|---|---|
| R1 | v3 | ACC |
| R2 | CoTV (published, Eq. 2 as a cost) | ACC |
| R3 | CoTV | release |

There is no directional prediction. The B6-1 criterion is applied per candidate, and a passing recipe goes to B6-2 as in (a).

**If R1–R3 all fail as well,** the result stands as: "no beneficial learned fleet under B6 in 5 recipes × 2 seeds, including a published CAV reward and 4× budget". Compatibility work on learned fleets in this environment is then not justified. The report recommends changing the fleet model (information: SPaT / V2I) as a new, separately registered direction, not in this program.
* CITY_make_b6_next.py 0b412f39de46f7be (dry-run in scratchpad: writes 040_B6R_recipes with 6 trainings + 7 evals); 039 now sha 91864a1bb17a; CITY_fleet_train_v5.py 1633c9e3d7d6ade1

## Amendment B6-A2 (05:58, before job 039 started and before 040 was written)

C-21b shows coarse ±1–2 m/s² steps every second (early hard braking, then bursts). So the B6-R screen gains **R4: reward v3 with a FINE action set** {−1.5, −1, −0.5, 0, +0.5, +1} m/s², 480 episodes, seeds 13 / 113.

The `fine` set is added as a new branch in `CITY_fleet_train_v4`, `CITY_fleet_train_v5` and `CITY_eval4`. The `release`, `residual` and ACC paths are unchanged. Check: eval4 with the plain L-ACT_0 fleet still equals h0 bit for bit; smoke of a 2-episode `fine` fleet OK.

New hashes:
* CITY_fleet_train_v4 a141376f31b7e368
* CITY_fleet_train_v5 ee385cec3d27b864
* CITY_eval4 92195f159407719c
* CITY_make_b6_next 708f05d73756f7e0 (8 lanes for 8 trainings)
* C-22 (06:21): CITY_fleet_train_v6.py 92882f8b18490055 (sanitized readings; smoke residual / release / cotv: 0 invalid); job 040b 55f6257bbaf3 reruns the void residual arm; same B6-N predictions and criteria.
* job 040c f52a9cca1af2 (06:22): R4 (v5, unsanitized) is void (R4_t0 episode 9 mean +2.9); rerun with v6; R1 rerun too if contaminated.

## B6-I: can the discrete action class represent SUMO's driver? (registered 06:23, job 040d, before any BC run)

`scripts/CITY_fleet_bc.py` behaviour-clones SUMO's default driver model:
- data: always-SUMO runs under ACT, TRAINING demand 0–7;
- target: the realized acceleration mapped to the nearest action;
- action sets ACC and `fine`; the Q7 network shape; 20 epochs.

The smoke run shows the discretization MAE: ACC 0.30 m/s², fine 0.46 m/s². SUMO often accelerates or brakes beyond ±1.5 m/s².

Evaluation: eval4 under ACT, SELECT, vs always-SUMO, with the B6-1 report.

| | Prediction | Supported iff |
|---|---|---|
| I-1 | At least one BC fleet comes CLOSE to the baseline | Agent TL change < +2 s/veh and agent fuel change < +3 % |

**Readings:**
- I-1 holds and the RL fleets stay far worse → the class can nearly represent the baseline and RL does not find it. The next recipe is RL initialized from BC (`CITY_fleet_train_v6` would need an --init option, added only then).
- I-1 fails → even imitation of the baseline through this 6-feature observation and 1-s discrete control loses materially. That is an observation / control limit of this fleet interface, and it is a finding.
* job 040d ede4bb462269; CITY_fleet_bc.py 5d9151808a6d8995
* v6 validity (06:24): the exact failing training episode (v4res_t0 ep 0: DQN seed 13, eps 1, demand 0) rerun with CarRLv6: identical trajectory (1 353 981 transitions, 30 teleports), sanitizer counted 33 invalid readings (= the 33 bad transitions; min raw -1073741824), mean reward -1.2269, 0 positive.
* v6 amended (06:26, before 040b / 040c ran): agents mid-teleport are skipped for that second (no observation, decision or transition; counted). Re-check on the failing episode: 140 skipped teleport-steps, 0 invalid readings, 0 garbage next-states, 0 positive rewards, mean -1.227. A v1 random-fleet episode and L-ACT_0 under RL-H_0 had 0 garbage-state transitions (CarRL's setSpeed exception path keeps them out), so the v1 / v2 checkpoints are not affected by garbage states. CITY_fleet_train_v6.py beeaea368ee62cb6.
* job 040c REWRITTEN (06:26, before it ran): all four B6-R arms rerun with v6 (garbage next-states are possible in every v5 arm, invisible in the reward for the CoTV arms); sha c7d15f443618. The v5 B6-R (job 040) is reported labelled unsanitized; decisions use 040c.
* v1 / v2 garbage-state check (06:27): 5 random-policy CarRLv2 episodes under RL-J_0 (as early NEWv2_RJ0 training): 2 438 943 transitions, 77 teleports, 0 garbage-state transitions. Earlier: v1 random fleet under ACT (6 teleports) and L-ACT_0 under RL-H_0 (13), also 0. The v1 / v2 checkpoints are not affected; v3 / v4-release are clean by the reward signature; only the residual path (and possibly the v5 CoTV arms, which carry no reward signature) needed v6.

## B6-T: time-beneficial fleet, confirmation only (registered 08:45, AFTER the B6-R v6 SELECT results; labelled post hoc)

**Why.** On SELECT, the CoTV-reward recipes were faster than SUMO's driver model with no harm to other vehicles: R3v6_t0 agent TL −2.05, city −0.98; R2v6_t1 −2.18, city −1.07. They cost +1.5 … +1.8 % fuel, so they fail the registered B6-1 (fuel superiority). The criterion below was chosen after seeing those numbers. It can therefore only be CONFIRMED on data not used to choose it.

**Criterion B6-T** (each fleet vs always-SUMO, same vehicles, under ACT, one-sided 95 % bounds; traffic seeds resampled, 2000 draws, rng 0):

| Quantity | Requirement |
|---|---|
| agent TL | SUPERIORITY: upper < 0 |
| agent fuel | NI: upper < +2 %. The margin is reused from L4's GG-4, registered before any B6 result. |
| human-vehicle TL | NI: upper < +0.5 s/veh |
| teleports per run | ≤ always-SUMO + 1 |
| unfinished trips | ≤ always-SUMO |

**Confirmation (job 046):** recipes R2 (CoTV / ACC) and R3 (CoTV / release), trainer v6 (sanitized), 480 episodes, NEW policy seeds DQN 213 / 313, evaluated on FRESH traffic 400–409 (never used for any choice). A recipe is "time-beneficial" iff B6-T holds on BOTH new seeds. SELECT seeds 13 / 113 and traffic 100–104 are not re-used for the verdict.

**Readings:**

| Outcome | Reading |
|---|---|
| A recipe passes | It is the deployed F* for the two-population study, as a TIME-beneficial fleet (not fuel). The A-L study (Branch P, AL*-1 … 4) then runs with "benefit" meaning time, and the fuel cost is always reported. |
| Neither passes | The SELECT time gains were seed- or traffic-specific; B6 stays negative. |
* B6-T freeze: job 046 c463eb728e71; CITY_wave2_report_v2 (rb6 mode=time, rb6t) 2edbdfadf4269a7e
* Branch-P job 047 (prepared 08:45, runs only on a B6-T pass) 15886610e270; SPOOL_eval4_run.sh b17c9972aaebfc2c
* Job 047 revised (08:46, before it ran). Trainers v4–v6 store no τ support (tmax = [1e9, 1e9]), so support gates would never fire. Job 047 now uses `CITY_eval5.py` (sha 6d67af43c4f62429; identical to eval4 without the flag) with `--support-from L-ACT:0`: ACT's τ range, the training light of every candidate.
* **Disclosure:** one smoke seed of the candidate R3v6_t0 under RL-H_0, seed 100, was seen. City TL plain 22.09; with the fallback gate (ACT support) 21.98; always-SUMO under RL-H_0 is 22.08. AL*-1 / AL*-2 are unchanged.
* 047 sha 54a88b6b0644; SPOOL_eval5_run.sh bcf4114052f6e5ac
* report v2 + section alstar bf1b14ea14e2b0f0 (08:47, before 047 ran)
* job 048 (A-L* VALIDATION, prepared 08:49 before 047 ran) c657578f9a0a; CITY_alstar_validation.py af727fce89190d81

### Pre-read audit of the B6-T reading (08:57; before any 046 evaluation row exists)

1. **Reporter provenance.** B6-T was frozen with the reporter at 2edbdfad…; the file is now bf1b14ea…. The session transcript shows that the only edit in between (12:47Z = 08:47 EDT) inserted `ralstar` before `__main__` and added `alstar=ralstar` to the dispatch dict. `rb6` / `rb6t` are byte-unchanged, so the B6-T computation is the frozen one.
2. **Decision rule.** `rb6` prints "recipes with >= 1 passing seed" (the B6-1 screen wording). For B6-T the registered rule is BOTH new seeds. Job 047 implements BOTH (it reads `046/b6_verdicts.json` and requires t2 AND t3). The reading will use the 047 rule, not the printed screen line.
3. **Tie rule disclosed.** If R2 and R3 both pass, job 047 (frozen 08:45) takes the first in sorted order, i.e. R2v6. This rule was fixed in the frozen job, not in the protocol text. It is disclosed here before results; the other recipe would be reported but not used for A-L*.
4. **Bootstrap.** Per fleet, traffic seeds 400–409 resampled (10), one-sided 95 % bounds, 2000 draws, rng 0. Directions: TL upper < 0 (superiority); fuel upper < +2 %; human TL upper < +0.5. Teleports: mean per run ≤ always-SUMO + 1. Unfinished: mean ≤ always-SUMO. All checked against the code (`rb6` l.208).

## B6-Z: baseline reproducibility, i.e. does each policy class contain SUMO's driver model? (registered 09:00, before any B6-Z run)

**Why.** This is user step 4 ("kiểm recipe/horizon và khả năng tái tạo baseline"). B6-R covered the recipe. Two classes were never tested at their null element:
- **B6-I** (behaviour cloning of SUMO): agent TL +33 / +52 vs always-SUMO.
- **residual** (v6res): +42 / +59.

If the zero element of a class is not SUMO, a learned policy in that class starts from a handicap. Then "no beneficial fleet" says something about the class, not about learning.

**Arms** (no training; constant-action checkpoints written by `scripts/CITY_make_null_fleets.py`, which also asserts the argmax on 1000 random inputs):

| Arm | Action every second |
|---|---|
| Z-rel | release (`setSpeed(-1)`) |
| Z-res0 | residual δ = 0: `setSpeed(getSpeedWithoutTraCI)` |
| Z-hold | acc a = 0: `setSpeed(current speed)` |
| OFF | always-SUMO |

All under ACT, SELECT traffic 100–104, `CITY_eval4`, one directory, same vehicles (`_stable_u`).

**Predictions (registered):**

| # | Prediction |
|---|---|
| Z-1 | Z-rel is identical to always-SUMO: agent TL, human TL, city TL, fuel and teleports equal on every seed (abs diff < 1e-9). A failure is a plumbing bug in the release path, and every release-class result would need re-reading. |
| Z-2 | Z-res0 reproduces always-SUMO within agent TL ±0.5 s/veh (crossed 95 % CI inside [−0.5, +0.5]; traffic resampled, 2000 draws, rng 0). **If not:** `getSpeedWithoutTraCI` is SUMO's speed of the LAST step, not the next one, so δ = 0 lags the driver model by 1 s. The residual class then does not contain the baseline, and the residual results (039 VOID, 040b) are read as class-limited. |
| Z-3 | (descriptive) Z-hold: agent TL / fuel vs always-SUMO, the cost of commanding alone. |

**Reading for step 4.** Whatever Z-2 says, it does not touch B6-T: R2 is ACC and R3 is release, and Z-1 checks the release path. If Z-2 fails, the residual class is set aside, not repaired (a new class would be a new registration).

**Placement.** Spool job 046z, after 046 and before 047; about 20 episodes.

### B6-Z amendment Z-4: a non-learned perfect-driver comparator (registered 09:03, BEFORE any 046 evaluation row exists; 046 is still training)

**Mechanism found by the B6-Z smoke and probe (scratch, not evidence).**
- *Probe:* three cars commanded `setSpeed(getSpeedWithoutTraCI)` every second. While a car is under `setSpeed`, `getSpeedWithoutTraCI` never exceeds the commanded speed (dawdling pulls it down). A car that stops at red stays at 0 after the light turns green.
- *Consequence:* δ = 0 is "never accelerate", not "SUMO". The residual class's only acceleration is δ = +1 m/s². Its results are about that class:
  - 039 v4res (VOID anyway);
  - 040b v6res, agent TL +42 / +59.
- *Related:* SUMO's default passenger vType has accel 2.6 m/s² and Krauss σ = 0.5. ACC's largest step is +2, and the fine class's largest is +1. Neither class can launch from standstill as fast as SUMO.

**Why Z-4.** A commanded fleet removes the driver imperfection (σ) of the cars it commands. A learned fleet's TIME gain over always-SUMO may therefore be the gain of a perfect SUMO driver, not of learning.

**Disclosure.** Before this registration one smoke seed was seen (traffic 100, 600 s). Z-sig0 agent TL 17.76 vs always-SUMO 22.20; city 20.72 vs 22.87.

**Z-4 arm.** `scripts/CITY_eval4_sig0.py`: eval4 with `--fleet L-ACT:0 --guard always` and `setImperfection(v, 0)` on the agent vehicles at departure. Same membership. SUMO drives every agent decision. The wrapper hash is recorded in each JSON's `source_sha256`.

**Runs** (job 046z):
- traffic 100–104 (SELECT, with the B6-Z arms);
- traffic 400–409, the B6-T traffic, so the 046 fleets are compared on the same vehicles.

**Registered readings:**

| # | Reading |
|---|---|
| Z-4a | (descriptive) Z-sig0 − always-SUMO: agent / human / city TL, agent fuel %, SELECT and 400–409. |
| Z-4b | For every 046 fleet: F − Z-sig0 agent TL on 400–409 (traffic resampled, one-sided 95 %), and fuel %. |
| Z-4c | **Wording rule for B6-T.** The B6-T verdict is unchanged (criterion as registered). But "the learned fleet beats SUMO's driver model in time" may be written only together with Z-4b. If a passing fleet's F − Z-sig0 upper is ≥ 0, the sentence must read: "faster than SUMO's default (imperfect) driver, but not faster than the same driver model without imperfection; the learned policy adds no detected time benefit over a perfect SUMO driver". Then A-L* (047/048) still runs as registered, but its premise is reported as "a fleet that beats imperfect SUMO", not "a beneficial learned fleet". |
* B6-Z freeze (09:04): job 046z e14f1c8e74cd; CITY_make_null_fleets 480f4bb91d666409; CITY_eval4_sig0 f3f383abc9d00d03; CITY_b6z_report 0299bc67856b7a0a; CITY_eval4 92195f159407719c. Runs after 046 and before 047 (spool name order).
* Z-4d (registered 09:06, DESCRIPTIVE, before 047 / 048 ran): if A-L* validation runs, F* under RL-H_i vs Z-sig0 under the same light on 200–209 (job 048z, `CITY_alstar_sig0.py` e34903daebd7d52c; job 0c620621cf30). Reported beside AL*-2 under the Z-4c wording rule. No verdict.
* Literature note for Z-4 (no novelty claim). It is known that SUMO's Krauss σ matters when RL vehicles are compared with SUMO-driven ones. Makantasis et al. (arXiv 1907.05246) evaluate with both σ = 0 and σ = 0.5 manual drivers. The SUMO mailing list documents that `setSpeed` persists until `setSpeed(-1)`; `getSpeedWithoutTraCI` is read-only. Z-sig0 is used as a comparator only.

### B6-T result (09:10): NOT CONFIRMED. All four fleets FAIL (ledger C-26). The registered reading is "Neither passes": B6 stays negative, and 047 / 048 / 048z exit without running (their gates). The decision rule was applied as pre-read (BOTH seeds); the screen line "recipes with >= 1 passing seed: []" agrees.
### B6-Z result (09:12): Z-1 SUPPORTED; Z-2 NOT SUPPORTED; Z-4a: σ = 0 SUMO is −5.2 s/veh at +2.6 % fuel; Z-4b: no B6-T fleet is faster than Z-sig0 (ledger C-27). The 047 / 048 / 048z gates exited as registered (no F*).

## B6-S and B6-H: the rest of user step 4 (registered 09:13, after the B6-T / B6-Z results and before any B6-S / B6-H run)

### B6-S: the non-learned σ-family (baseline frontier)
**Arms:** SUMO drives the agent cars with imperfection σ ∈ {0.1, 0.2, 0.3, 0.4} (`scripts/CITY_eval4_sigma.py`). Together with σ = 0 (Z-sig0, 046z) and σ = 0.5 (always-SUMO), this gives six points. Traffic: SELECT 100–104 and 400–409, under ACT.

**Self-check (blocks the report):** σ = 0.5 equals always-SUMO exactly. The smoke showed this on one seed.

**Reading S-1 (descriptive):** agent TL and agent fuel vs always-SUMO for each σ, on both traffic panels. This is the trade-off a learned fleet must beat.

**Definition S-2 ("beyond the σ-family"; used for every later fleet claim in this program).** Fleet F is beyond the σ-family iff, for EVERY σ in the six points, F is better than SUMO_σ on at least one of agent TL and agent fuel with a one-sided 95 % bound: TL(F) − TL(σ) upper < 0, or fuel%(F vs σ) upper < 0. Applied descriptively now to the four B6-T fleets (400–409) and the R3v6 / R1v6 / R2v6 / R4v6 SELECT fleets.

### B6-H: horizon (approach-terminal vs whole trip)
**Trainer:** `CITY_fleet_train_v7.py`. v6 plus `--horizon`. In trip mode the stop-line terminal is replaced by a non-terminal transition into the next approach.

**Horizon trace check:** `CITY_v7_horizon_check.py`, PASS at 09:1x.
- H-1: the physical stream is identical (same multiset of (action, cost)).
- H-2: approach mode has no crossing transitions.
- H-3: in trip mode, chained = 115 = terminals 125 − 10, and every crossing transition has done = 0.

The first version of the check FAILED on transition ORDER, a check bug. It was fixed before any training.

**Arms** (480 episodes, DQN seeds 13 / 113, against ACT; the SELECT development seeds, paired with the existing R3v6_t0 / t1 = cotv / release / approach):

| Arm | Reward / actions / horizon |
|---|---|
| R3h | cotv / release / trip |
| R5a | v3 / release / approach |
| R5h | v3 / release / trip |

Release is used because it is the only class shown to contain SUMO (Z-1). v3 carries the fuel term.

**Evaluation:** eval4, SELECT 100–104, ACT, with always-SUMO in the same directory (049h).

**Readings:**

| # | Reading |
|---|---|
| H-1 | B6-1 as registered: agent fuel superiority (upper < 0), agent TL NI +0.5, human TL NI +0.5, teleports ≤ +1, unfinished ≤. B6-T is reported beside it. A recipe passing on BOTH seeds is a candidate only. It then needs a new registered confirmation on new seeds and new traffic. 400–409 is now seen; fresh traffic would be generated by the same demand generator. |
| H-2 | Horizon contrast (descriptive, CI per seed): trip − approach, paired by DQN seed and reward, on agent TL, agent fuel %, human TL. "The horizon matters" only if the CI excludes 0 on both seeds in the same direction. |
| H-3 | S-2 applied to every B6-H fleet on SELECT. |

**Prediction (registered):** no B6-H fleet passes B6-1 on both seeds, and none is beyond the σ-family. Reason: the observation has no time-to-switch, and the fuel gains in the literature come with SPaT.

**If this holds**, step 4 is complete (recipe B6-R, horizon B6-H, baseline B6-Z / B6-S) with no beneficial learned fleet. Further learned-fleet work in this observation space is not justified. The proposed next direction is information (SPaT, `PROPOSAL_SPAT_CONTRACT_20261004.md`), which awaits the user.

**Order in the spool:** 049a B6-S (evaluation only, about 3 min), then 049b B6-H (6 trainings in parallel, about 30 min, then evaluation).
* B6-S / B6-H freeze (09:14): 049a e4d5faca2ea5; 049b d8b4e20d6d7e; CITY_eval4_sigma c277775c606529b2; CITY_fleet_train_v7 180c83fb6e502e4e; CITY_v7_horizon_check da84124cc3587589; CITY_b6sh_report a1cf94b085ccb25d
### B6-S result (09:15): self-check PASS; σ 0.2–0.4 dominate always-SUMO in both TL and fuel; S-2: no learned fleet is beyond the σ-family (ledger C-28).

## B6-SL: a beneficial (non-learned) fleet upgrade under the frozen learned light (registered 09:17, after B6-S and before any B6-SL run)

**Why.** B6-S found a fleet upgrade that is beneficial in time AND fuel: SUMO-driven agent cars at σ 0.3 instead of 0.5. It stands for driver assistance or a better driver model. It is not learned. This gives the reviewer's chosen branch a beneficial fleet without waiting for one to be learned: upgrade the fleet, keep the light frozen. RL-H was trained with σ 0.5 cars everywhere.

**Design.** Eval only, through `CITY_eval4_sigma.py` with `--guard always`.
- Lights: ACT and RL-H_0..3, all frozen.
- Fleet (the agent half): σ ∈ {0.5 (= always-SUMO), 0.3, 0}.
- Traffic: SELECT 100–104.
- 75 episodes, directory 049l.

**Readings** (crossed bootstrap light-seed × traffic, 2000 draws, rng 0; one-sided 95 %):

| # | Reading |
|---|---|
| SL-1 | The fleet benefit under the learned light: σ 0.3 − σ 0.5 under RL-H on agent TL and agent fuel %. "Benefit kept" iff both uppers < 0. **Prediction: kept.** |
| SL-2 | Compatibility interaction: [σ 0.3 − σ 0.5 under RL-H] − [the same under ACT], on city TL, agent TL, human TL and agent fuel %. The ACT term has no light seed and is broadcast. Seen from the light side, the same number is the change in the light-upgrade gain (RL-H − ACT) when the fleet upgrades. **Prediction: |interaction| on city TL < 0.5 s/veh (CI inside ±0.5).** If not, a learned light trained on σ 0.5 cars is partner-specific to the driver model. |
| SL-3 | (descriptive) the same with σ 0. |

**What it is not.** No learned fleet is involved, so this is not the two-learned-population claim. It is the frozen-learned-light × beneficial-fleet-upgrade cell of the 2×2.

**Order.** Spool job 049c, after 049b.
* B6-SL freeze (09:17): 049c 8f70402436e9; CITY_b6sl_report a8e94dba322912e2
* B6-SL disclosure: one smoke seen before the run (RL-H_1, σ 0.3, traffic 100, 600 s): city TL 18.98, agent 17.81; plus the pipeline smoke below (600 s, seed 100, scratch).
* B6-SL reporter fixed before the run (09:17): bootstrap shape (4, len(SEL)) instead of a hard-coded 5 (the pipeline smoke crashed on 1 seed); new hash 0fe0080a1e6f7979
* C-28 validity check (09:18): every σ arm and Z-sig0 has 0 teleports and 0 unfinished trips on both panels, so the agent fuel sums cover the same vehicles.

## B6-R5: replication of the recipe R5h (registered 09:39, AFTER the B6-H results; R5h was selected post hoc from ONE seed)

**Why.** In B6-H, R5h_t0 passed B6-1 and was beyond the σ-family. R5h_t1 failed. Under the user's rule 3 ("a pass on one seed only selects a candidate; replication on new policy seeds"), the recipe is replicated. A one-seed pass is not a claim.

**Recipe.** R5h = trainer v7 (`CITY_fleet_train_v7.py`, frozen 09:14), reward v3, actions release, horizon trip, 480 episodes, against ACT, γ 0.97. Unchanged.

**New policy seeds.** DQN 213, 313, 413, 513 (names L-ACT-R5h_t2..t5).

**Fresh traffic 410–419.** Generated now with the SAME randomTrips configuration as 400–409 (`grid4.net.xml`, fringe-factor 10, period 2.0, min-distance 300, vehicle-class passenger, seed s, end 3600, then duarouter). Never used for anything.

**Evaluation** (eval4 / eval4_sigma, under ACT, 410–419):
- the 4 new fleets;
- always-SUMO;
- the σ-family σ ∈ {0, 0.1, 0.2, 0.3, 0.4};
- R5h_t0 / t1, descriptive only.

**Verdict** ("R5h is a beneficial learned fleet"), all of:

| # | Condition |
|---|---|
| R5-1 | POOLED over the 4 new seeds (crossed bootstrap fleet-seed × traffic, 4 × 10, 2000 draws, rng 0; one-sided 95 %): agent fuel superiority (upper < 0), agent TL NI (upper < +0.5), human-vehicle TL NI (upper < +0.5). |
| R5-2 | POOLED S-2: for every σ, fuel upper < 0 or TL upper < 0 vs SUMO_σ. |
| R5-3 | EVERY new seed: teleports / run ≤ always-SUMO + 1 and unfinished ≤ always-SUMO. |

Reported beside the verdict:
- per-seed B6-1 verdicts and the number of passing seeds;
- city TL;
- Z-4c (vs Z-sig0).

**Readings:**

| Outcome | Reading |
|---|---|
| Confirmed | R5h becomes F* (FUEL-beneficial, beyond the σ-family) for the fleet-upgrade-under-frozen-light study. A-L* with this F* needs its own registration (the 05:47 Branch-P endpoints, benefit = fuel per B6-1) before it runs. |
| Not confirmed | The R5h_t0 pass is seed-specific. Step 4 closes: no beneficial learned fleet in this observation space. |

**Order.** Spool job 050r: generate traffic → train 4 (4 lanes) → evaluate → report `CITY_b6r5_report.py`, written before the run.
* Fresh traffic 410–419 generated 09:40 (randomTrips config verified: regenerating seed 400 in scratch reproduced rou_s400.xml's body byte-identically).
* B6-R5 freeze (09:40): 050r 2b4344d341bf; CITY_b6r5_report 8b5f45a4564fce90; trainer v7 180c83fb6e502e4e (unchanged)

## B6-R5-P: A-L* with F* = R5h (registered 09:44, BEFORE the B6-R5 verdict; runs only if 050r prints "VERDICT: R5h CONFIRMED")

Branch P (registered 05:47), with benefit = FUEL as in B6-1 and fleet seeds = the four replication seeds t2..t5. Lights ACT and RL-H_0..3, frozen. Guards {none, fallback, clip, green+oos}; the support comes from L-ACT:0, because the v7 fleets store no τ support (eval5).

| Stage / # | Rule |
|---|---|
| SELECT 100–104 | The guard with the lowest point agent-fuel % vs always-SUMO under RL-H is CHOSEN. |
| AP-1 (SELECT) | Regression of the fuel benefit under the learned light: [fuel %(F* vs always-SUMO \| RL-H) − (same \| ACT)], crossed CI lower > 0 ⇒ "the benefit shrinks". |
| VALIDATION 200–209 | Under RL-H_0..3: F* × {chosen, none} + always-SUMO + σ-family under the same light. |
| AP-2 | Chosen guard: agent fuel superiority (upper < 0) and agent TL NI (upper < +0.5) vs always-SUMO, same light. |
| AP-3 | Human-vehicle TL NI (upper < +0.5). |
| AP-4 | S-2 under RL-H: beyond the σ-family under the same light. |

Crossed bootstrap light-seed × fleet-seed × traffic, 2000 draws, rng 0. σ arms are shared across fleet seeds.

**Readings:**

| Outcome | Reading |
|---|---|
| AP-2 to AP-4 all SUPPORTED | "The learned fleet's fuel benefit survives the light upgrade". Together with C-30, the light-upgrade × fleet cell is closed for this pair. |
| AP-2 fails with the plain fleet but holds with a guard | The guard is the repair (car-side reaction fix). |
| AP-1 SUPPORTED and AP-2 fails | Compatibility problem confirmed, for a fleet that is beneficial for real. This is the setting the adapter / handoff work (060 / 095, on hold) was waiting for. |

**Files:** job `051p` 9bb52cd56cc9; `CITY_alstar_r5.py` ca94a5a5e219dcd4.

**Disclosure:** a 600 s smoke of the DEVELOPMENT fleet R5h_t0 under RL-H_0, traffic 100, was seen (city TL: fallback 22.79, clip 24.65, green+oos 23.58). It was a plumbing check. t0 is not in A-L*.
### B6-R5 result (10:01): NOT CONFIRMED (R5-1 and R5-3 fail; R5-2 holds through fuel alone). 051p exited at its gate. Step 4 closed (ledger C-31).

## B6-SL-V: confirmation of C-30 on VALIDATION traffic (registered 10:02, before any σ-fleet run on 200–209)

Same arms, same readings (SL-1, SL-2, SL-3) and the same reporter as B6-SL, on traffic 200–209 (10 seeds).
- **Not reused:** 200–209 was used earlier only for L4 / A-L validation with LEARNED fleets. No σ arm has been run on it.
- **Registered verdict for T4:** "confirmed" iff SL-1 (benefit kept) and SL-2 (|interaction| on city TL inside ±0.5) both hold on 200–209.
- **Reporter:** `CITY_b6sl_report.py` reads directory 049l and traffic SEL. Rather than editing the frozen file, a 6-line wrapper `CITY_b6sl_report_val.py` sets D = 049v and SEL = 200–209 and calls `main()`.
- **Job:** 052v.
* B6-SL-V freeze (10:02): 052v e946e3a6b02d; CITY_b6sl_report_val a40d057546491e2b; CITY_b6sl_report 0fe0080a1e6f7979 (unchanged)

## B6-AC: an AUTOMATED (non-learned) fleet under the frozen learned light (registered 10:05, before any B6-AC run)

**Why.** T4 (C-30 / C-32) used a mild upgrade (σ 0.5 → 0.3). A qualitative fleet upgrade is automation. SUMO's built-in ACC car-following model (`carFollowModel="ACC"`, default parameters) stands in for an ACC-equipped fleet. Same cells as T4: the fleet upgrades, the learned light stays frozen.

**Route variants.** Generator `CITY_make_route_variant.py`. The agent vehicles (exact membership: `_stable_u(seed, vid) < 0.5`) get a new vType; everything else is byte-identical.
- **ctrl:** vType `v_agent` = a copy of `v_passenger`. Identity check.
- **acc:** vType `v_acc`, vClass passenger, `carFollowModel="ACC"`.

**Wrapper.** `CITY_eval4_route.py --route-variant V` patches `Q7.ROU` and runs eval4 with `--fleet L-ACT:0 --guard always`. SUMO drives every agent decision with the variant's model; the release call is a no-op for model choice.

**Panels.**
- Lights ACT and RL-H_0..3.
- SELECT 100–104 (development, shown first).
- VALIDATION 200–209 (the verdict).

**Readings:**

| # | Reading |
|---|---|
| AC-0 | Self-check: ctrl ≡ always-SUMO (abs diff < 1e-9 in agent / human / city TL and agent fuel, every seed, every light). If it fails, the B6-AC report is void. |
| AC-1 | (descriptive) ACC fleet − always-SUMO under ACT and under RL-H: agent / human / city TL, agent fuel %, teleports, unfinished. |
| AC-2 | Compatibility on VALIDATION: the city-TL interaction [(acc − base) \| RL-H] − [(acc − base) \| ACT], crossed light-seed × traffic. "Compatible" iff the CI is inside ±0.5. **Prediction: compatible**, by analogy with T4; uncertain, because ACC is a larger change. |
| AC-3 | (descriptive) light gain RL-H − ACT with the ACC fleet vs with SUMO cars. |

Jobs 053a (SELECT) and 053b (VALIDATION).
* B6-AC disclosure: 600 s smoke on traffic 100 seen before the run. ctrl ≡ always-SUMO under ACT and RL-H_1. acc: ACT city 22.55 vs 22.87; RL-H_1 18.67 vs 19.92.
* B6-AC: the pipeline smoke (600 s, traffic 100, all 15 arms) report was seen: AC-0 PASS; city interaction −0.66 on that single smoke seed.
* B6-AC freeze (10:06): 053 99e1063dd16d; CITY_make_route_variant b4558ca105f06f2e; CITY_eval4_route 025fbeb0af57e073; CITY_b6ac_report a228c6eba3f8ddef; route variants written 10:05 for 100–104, 200–209

## B6-G: do T4 / T5 hold for other learned lights? (registered 10:10, before any run on these lights with σ / ACC fleets)

**Lights** (frozen):
- RL-C50_0..3: the RL-H weights with a forced switch at 50 s;
- RL-J_0..3: the same DQN retrained with the LEARNED fleet L-ACT present at ρ 0.5 (Q7 protocol). Its training partner was a learned fleet, not SUMO cars.

ACT is the reference, with rows reused from 049v / 053v (the same evaluator and traffic; always-SUMO is bit-identical across directories, C-27).

**Fleet upgrades:** σ 0.5 → 0.3 (`CITY_eval4_sigma`) and SUMO cars → ACC (`CITY_eval4_route`). Comparator always-SUMO under the same light.

**Traffic:** VALIDATION 200–209. Directory 054.

**Readings:**

| # | Reading |
|---|---|
| G-1 | No harm, per family and upgrade: city-TL interaction [(upgrade − always-SUMO) \| L] − [(upgrade − always-SUMO) \| ACT], crossed light-seed × traffic. "No harm" iff the one-sided 95 % upper < +0.5. |
| G-2 | (descriptive) the light gain L − ACT with each fleet. |

**Prediction:** no harm for both families and both upgrades. RL-J was trained with a different (learned) partner, so it is the more likely place to break.

Job 054.
* B6-G freeze (10:10): 054 84003f69f153; CITY_b6g_report fb16105fdc8cfb0e

## Corrections after the user's audit CITY_B6_FINAL_AND_SPAT_AUDIT (12:05; registered verdicts unchanged; ledger C-37)

- **Z-4 / Z-4c wording.** "Perfect driver" is replaced by "SUMO Krauss without imperfection (σ = 0)". The registered rule is otherwise unchanged.
- **S-2.** The definition stays as registered: per σ, TL upper < 0 OR fuel upper < 0, for every σ. Its FAILURE label is corrected from "within (dominated by some σ)" to "not established beyond the tested σ-family". Dominance needs the two-axis test (`CITY_s2_classify_v2.py`). The OR of one-sided tests is not an overall 5 % test, so S-2 is descriptive. Later rounds fix fuel as primary with a TL constraint, or use simultaneous bounds.
- **B6-H "trip" horizon.** Read it as **chained approaches**. Every signalised approach of a trip is chained; the exit link, the episode cut and teleport gaps are not costed (measured: 0.98 terminals / trip).
- **C-29b.** Only the logged `mean_r` fails to separate the seeds.
- **Reading of the B6 program.** "Not confirmed in the settings tried" replaces any "impossible in this observation space". The cause is not isolated.
