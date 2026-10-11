# DRAFT protocol: bounded SPaT feasibility pilot (Steps 1–2 of the user's audit CITY_B6_FINAL_AND_SPAT_AUDIT §5) — written 04/10/2026 12:10, NOT RUN

**Status.** Design only. Nothing in this file runs until the user authorises it. Jobs 060 / 070 / 095 stay on hold. Proposal steps S2 / S3 (light upgrade, commitment) are not opened.

## Question

Can a learned fleet be beneficial under the registered criterion?

| Criterion | Requirement |
|---|---|
| fuel superiority vs always-SUMO | yes |
| agent TL margin | +0.5 |
| human-vehicle TL margin | +0.5 |
| teleports | no increase |
| σ-family | not dominated by any σ (strict two-axis test) |

If so, does it USE movement-specific SPaT? That is measured with the SAME recipe, with and without SPaT.

**Not asked here:**
- whether SPaT is necessary in general;
- anything about learned or adaptive lights (Step 3);
- any repair method (Step 4).

## What is already checked (12:09, no training)

- **Movement-specific SPaT** (\`scripts/CITY_spat_feature.py\`): for the vehicle's own link index from \`getNextTLS\`, the time-to-green and the time-to-end-of-green are taken from the STATIC program.
- **Validity:** \`valid = False\` for any non-static program or held phase (LightRL's 1e5). The values are then 0. The feature never passes 1e5 to a car.
- **Trace check** (\`scripts/CITY_spat_trace_check.py\`, FT, traffic 100, 1800 s): the first run found every prediction off by exactly +1 s (39 522 / 39 522), so the check can fail. With the declared convention \`OBS = 1\` (the new state is first OBSERVED one step after \`getNextSwitch\`), 40 476 / 40 476 predictions are exact.
- **ACT:** 30 873 / 30 873 agent-seconds are "unavailable" by design. A causal forecast for adaptive lights is a separate, later design.

## Light

FT, the grid4 static programs: 42 s green, 3 s yellow, 90 s cycle. SPaT is exact there (trace-checked). This is the setting of Jayawardana & Wu 2022 (fixed time).

## Fleet recipe (one recipe; the two arms differ ONLY in the SPaT inputs)

The source is the published recipe of Jayawardana & Wu 2022, arXiv 2204.12561. No code is released, so this is a port from the paper. Deviations are declared, and each applies to both arms.

| Element | Paper | Pilot (both arms) | Why |
|---|---|---|---|
| observation | own speed / position, signal phase one-hot, leader and follower speed / position, time remaining in the current phase | own speed, distance to stop line, own-movement state one-hot (G / y / r), leader speed and gap, follower speed and gap (100 m), **[ttg, ttr, valid]** | movement-specific SPaT (audit §3.2) |
| no-SPaT arm | — | [ttg, ttr, valid] = [0, 0, 0] (same input width) | clean information ablation |
| action | continuous accel ∈ [−1.5, 1] m/s², 0.5 s steps | continuous accel ∈ [−3, 2.6] m/s², 1 s steps, applied as setSpeed(v + a), clipped to [0, v_allowed] | the paper's +1 cannot launch like SUMO's 2.6 (M1 pitfall); the repo step is 1 s |
| reward | 4-branch phase-averaged reward on VT-CPFM fuel, normalised (δ = 0.01) | **option A (recommended):** per-agent realised cost c = fuel_rate/1000·κ + (1 − v/v_allowed), κ fixed before training, summed over the chained approaches with per-trip return logged. **Option B:** the paper's 4-branch reward per light-phase with normalisers calibrated on SELECT-free traffic (0–7) BEFORE training | the paper's thresholds are in VT-CPFM units; SUMO uses HBEFA-type emissions, so a literal port is not faithful. B is closer to the paper, A to the repo's checked v3 conventions |
| algorithm | TRPO, CTDE, 64 × 64 tanh, γ 0.99, batch 55 000, 3 000 iterations | PPO (clip 0.2, GAE λ 0.95), shared parameters, decentralised critic on the own observation, 64 × 64 tanh, γ 0.99 per second, lr 3e-4 | no TRPO in the repo; PPO is the standard substitute; declared |
| budget | about 165 M agent-steps | fixed before training: 1 000 episodes × about 12 000 agent-steps ≈ 12 M per run | compute bound; declared as a limitation |
| checkpoint | — | the LAST checkpoint; no selection by training reward | C-29b lesson |

**Conventions** (the counters required by \`FLEET_MDP_CONVENTIONS_V6_V7_20261004.md\`):
- a teleport gap drops the bridging transition;
- arrival is terminal with cost 0;
- the exit link after the last signal is not controlled and not costed (declared);
- the episode cut is a truncation with value bootstrap;
- separate counters for exception / invalid / empty-edge zeros and gaps;
- per-trip return, fuel and TL are logged beside \`mean_r\`.

A reward trace check like 021 / 034 runs before training and must PASS.

## Arms (pilot, SELECT 100–104, FT)

1. always-SUMO (σ 0.5).
2. The σ-family σ ∈ {0, 0.1, 0.2, 0.3, 0.4}; σ* is the σ with the lowest agent fuel among those with TL ≤ always-SUMO, chosen on SELECT.
3. ACC (SUMO model).
4. **GLOSA-SPaT:** a non-learned eco-controller with the SAME SPaT. When the link is red and ttg is valid, it commands v = min(v_allowed, d / ttg); otherwise it releases to SUMO.
5. learned-noSPaT, policy seeds 13, 113.
6. learned-SPaT, policy seeds 13, 113.

## Endpoints

| # | Endpoint |
|---|---|
| P-1 | Per fleet: B6-1 (registered criteria) and the strict σ-dominance label. |
| P-2 | Information effect (descriptive in the pilot): learned-SPaT − learned-noSPaT, paired by policy seed, on agent fuel % and agent TL. |
| P-3 | (descriptive) learned-SPaT vs GLOSA-SPaT. |

**Pilot gate to Step 2.** At least one learned-SPaT seed passes B6-1 AND is not dominated by any σ. Otherwise the SPaT branch STOPS and the reading is: *"with this recipe and budget, no learned fleet met the criterion even with exact SPaT"*.

## Step 2 (only if the gate passes): confirmation

- 4 NEW policy seeds per learned arm, and fresh traffic 420–429 (generated with the verified randomTrips config).
- The pooled recipe verdict as in B6-R5: B6-1 pooled, plus not dominated pooled, plus teleports on every seed.
- The information effect pooled with a CI.
- "SPaT used" iff SPaT − noSPaT agent fuel upper < 0, or TL upper < 0, with the other NI.

## Compute estimate

- Grid4 FT episodes take about 2–5 s of SUMO with about 12 k agent-steps.
- PPO adds about 1–2 s per episode.
- 1 000 episodes is about 1.5–2 h per run. Four runs in parallel take about 2 h.
- Evaluation takes minutes.

## Infrastructure still to build after authorisation

| File | Content |
|---|---|
| \`CITY_fleet_train_v8_ppo.py\` | PPO, continuous actions, the conventions and counters above, SPaT / noSPaT inputs |
| \`CITY_v8_trace_check.py\` | the reward / terminal / gap trace check |
| \`CITY_eval6.py\` | eval4 plus continuous-action fleets and the GLOSA-SPaT controller |

## Stop rules and wording

- If the gate fails, the SPaT branch stops.
- No claim that SPaT is necessary in general.
- No light-upgrade experiment until a fleet is confirmed.
- A 1e5 or held-phase value is never given to a car.

## Amendment R1 (12:25, after review SPAT_PILOT_REVIEW_20261004; the user chose reward A and a bounded pilot). Frozen BEFORE any FT comparator run

**Recipe identity.** This is a "PPO eco-driving pilot inspired by the Jayawardana–Wu setting". It is NOT a reproduction:
- TRPO → PPO;
- CTDE → local critic;
- a new reward, a new action range, dt 1 s, SUMO fuel.

Source correction: the paper's observation uses a time-to-green signal feature. This file's earlier wording "time remaining in the current phase" is the paraphrase returned by the reading tool, kept here as such.

**Observation, both arms (14 numbers).**
- dist / 200;
- v / 14;
- own-movement one-hot G / y / r;
- **phase age `getSpentDuration` / 60**, kept in BOTH arms;
- leader gap / 100 and leader speed / 14 (none → 1, v_allowed / 14);
- follower gap / 100 and follower speed / 14 (none → 1, 0);
- [ttg / 90, ttr / 90, valid].

The no-SPaT arm gets [0, 0, 0]; this is the ONLY difference between the arms.

What the actor knows: its own movement state and the phase age of its light. It does not get the phase ID or the program. Under FT the program is fixed (42 / 3 / 42 / 3), so remaining time is partly inferable from the age. In the other approach's yellow, "red + age < 3" is ambiguous between two remaining times, so SPaT is not fully redundant. A SPaT gain may still be partly a representation effect.

**Reward A.** cost = max(0, 1 − v / v_allowed) + κ · fuel_rate[mg/s] / 1000 with **κ = 0.5** (the v3 weight; one weight tried, not an optimum), read at the next decision second; reward = −cost. Both arms are identical.

**Primary endpoint: agent FUEL, with TL constraints. Margins frozen now.**

| # | Requirement |
|---|---|
| (a) B6-1 vs always-SUMO | fuel % upper < 0; agent TL upper < +0.5 s/veh; human TL upper < +0.5; teleports / run ≤ always-SUMO + 1; unfinished ≤ always-SUMO |
| (b) vs σ* | fuel % upper < 0; agent TL vs σ* upper < +0.5; human TL vs σ* upper < +0.5 |
| (c) SPaT vs no-SPaT (same recipe) | fuel % upper < 0; agent TL upper < +0.5 |

All are one-sided 95 %. Confirmation pooling: crossed bootstrap fleet-seed × traffic, 4 × 10, 2000 draws, rng 0. No "fuel OR TL" rule.

**σ* rule, frozen now, BEFORE any FT σ run.** Among σ ∈ {0, 0.1, 0.2, 0.3, 0.4, 0.5}, evaluated under FT on SELECT 100–104: σ* = the σ with the lowest point agent fuel % vs always-SUMO among those whose point agent TL ≤ always-SUMO's and whose human TL upper is < +0.5. If none qualifies, σ* = 0.5. σ* is never re-chosen on test traffic.

**Pilot gate.** At least one learned seed, of EITHER arm, passes (a) on SELECT → Step 2 confirms BOTH arms on 4 new policy seeds (213, 313, 413, 513) and fresh traffic 420–429. The three-state σ labels and the (b) / (c) point estimates are descriptive in the pilot.

**Readings at confirmation:**
- (a) holds, (b) fails → beneficial vs the default, not shown better than the strong baseline.
- (a) and (b) hold, (c) fails → a good fleet, no shown SPaT gain.

**GLOSA arm.** It is named a "simple heuristic GLOSA" (v = min(v_allowed, d / ttg) on red with valid SPaT, else release to SUMO). It is not a reproduction of a published algorithm and not the strongest eco-driving baseline.

**Class statement.** Continuous acceleration up to +2.6 m/s² does NOT make the class contain SUMO; no such claim is made. There is no identity test for it.

**Comparator job 057** (launched now; it does not depend on any learned result):
- under FT: always-SUMO, the σ-family {0, 0.1, 0.2, 0.3, 0.4} and ACC (+ ctrl identity);
- on SELECT 100–104 and on fresh traffic 420–429, generated now with the verified randomTrips config.
* 057 freeze (12:25): 1de7f9611821. Pre-run smoke on traffic 100, FT, 600 s, seen: ctrl ≡ always-SUMO (TL 51.17); σ0.3 agent TL 46.71 vs 50.49.

## Amendment R2 (12:27): the reward is B (the user's revised choice); A is an optional comparator only if budget remains. Frozen BEFORE any calibration or training

**Source, verified in the PDF** (Eq. 9–10, Table III, arXiv 2204.12561).

The four branches:
- R1 = μ1 if any vehicle stops at the start of an approach;
- R2 = μ2 + μ3·exp(v̄) if f̄ ≤ δ and s̄ = 0;
- R3 = μ4 + μ5·exp(v̄) + μ6·s̄ if f̄ ≤ δ and s̄ > 0;
- R4 = μ7 + μ8·exp(μ9·f̄) + μ10·exp(v̄) + μ11·s̄ otherwise.

Table III: μ1 −100, μ2 −5, μ3 5, μ4 −5, μ5 5, μ6 −10, μ7 −7, μ8 −3, μ9 1000, μ10 4, μ11 −10, δ 0.01.

The reward is per traffic-signal phase and fleet-based. f̄, v̄ and s̄ are the per-vehicle, per-phase averages of fuel, speed and stopped vehicles, "normalised". The paper gives no min / max values.

**Units decision (frozen).** f̄ is the mean fuel rate per vehicle-second over the phase, **in litres / s**:
- SUMO `getFuelConsumption` [mg/s] ÷ 745 000 (gasoline 0.745 kg/L);
- reason: this is the only reading under which the printed coefficients are numerically sane (VT-CPFM α0 = 0.00078 L/s idle; μ9 = 1000 then gives exp(1000·f̄) ≈ e^0.8 … e^10 over idle to f̄ = δ). A min-max scale to [0, 1] would make exp(1000·f̄) overflow;
- **numerical guard:** the exponent 1000·f̄ is capped at 30, and the number of capped phases is logged. It is not expected to bind; if it binds in more than 1 % of calibration phases, that is reported as a failed port.

The other averages:
- v̄ = the mean over vehicle-seconds of v / speed limit (min 0, max = limit);
- s̄ = stopped vehicle-seconds / present vehicle-seconds over the phase (stopped: v < 0.1 m/s).

**Group (frozen).**
- For each light and each program phase interval (each green and each yellow), the group is ALL vehicles (agents and SUMO cars) within 200 m upstream of that light on its incoming lanes, present in that interval. Including the SUMO cars is a fleet-based reward that sees the harm to other vehicles (the R5h failure mode).
- "Stops at the start of an approach": some vehicle in the group has v < 0.1 m/s while its distance to the stop line is ≥ (approach length − 10 m).
- **Empty group:** no reward.
- **Credit:** each agent that decided on that light's approach during the interval receives the phase reward at its LAST decision inside the interval. All its other decisions get 0.
- Reward scale: B as printed (R2 ∈ [0, 8.6], R1 = −100), with no other rescaling. PPO normalises advantages per batch.

**Calibration, frozen rule** (traffic 0–7, training seeds only, FT, before SELECT / TEST): always-SUMO, σ 0.3 SUMO, and the uniform-random continuous policy of the pilot action class. For each, log the R1–R4 activation shares, the reward distribution, the capped share, f̄ / v̄ / s̄ quantiles and the empty-group share.
- **Degenerate** if, under the random policy, one branch has ≥ 99 % of non-empty phases, or every branch except one has 0 %.
- If degenerate, B is NOT trained in this round. The finding is reported and the user is asked. No retuning of μ.
- If the fuel branch R4 is never active under any calibration policy, B is reported as **"fuel enters only through the δ threshold"** and still trained. This may be the paper's own regime.

**Arms (unchanged otherwise):** B + SPaT and B + no-SPaT. Same recipe, phase age, seeds 13 / 113, same budget. Endpoints and gates as in Amendment R1. The fleet is scored on fuel, TL, other vehicles and the σ* / GLOSA baselines; **a higher reward is never counted as success.**
* R2 correction (12:30, before any training): the observation has **13** numbers (2 + 3 + 1 + 2 + 2 + 3), not 14; Amendment R1's count was an arithmetic slip, and the listed components are unchanged.
* 058 freeze (12:31): 8b97b036d221; CITY_v8_calibrate_B 14d1acd395c8b0a7; CITY_fleet_v8 cad3ac2300b184a7. Pre-run smoke disclosed: random, traffic 0, 300 s: R1 24, R2 21, R3 139, R4 0; max f 0.00162 L/s.
* σ* (12:31, frozen rule, FT, SELECT 100–104): **σ* = 0.3** (agent fuel −2.20 %, agent TL −2.52, human TL upper +0.08). ctrl ≡ always-SUMO PASS on 057s and 057c. Table in `research/city_sim/spat_pilot_20261004_sigma_star.txt`. The 420–429 rows were computed and printed in the same call. They are not used for any choice.

## Amendment R3 (12:35): calibration result, budget, and parallel training. Frozen before any pilot training

**Calibration** (job 058, `spat_pilot_20261004/calib/SUMMARY.txt`). B is not degenerate. Random policy: R1 0.30, R2 0.02, R3 0.68, R4 0. always-SUMO and σ 0.3: R1 0.07, R2 0.08, R3 0.85. **R4 is never active** under any policy (max f̄ 0.0036–0.0041 L/s ≪ δ = 0.01), and nothing is capped. Registered reading: **fuel enters B only through the δ threshold**, so B acts as a speed (exp v̄) plus stop-penalty (s̄, R1) reward in this port. B is trained as registered. Fuel is still the primary ENDPOINT.

**Checks before training:**
- `CITY_v8_check.py` PASS: segments, log-prob, squash, the command passed to SUMO, GAE vs a naive recursion, Eq. 9–10, credit reconstruction, arm inputs, the gap path. Deliberate corruptions of GAE and of the reward are caught.
- `CITY_spat_trace_check.py` PASS.

**Throughput** (smoke, 3 episodes × 3600 s, untrained policy): about 9 s per episode (about 6 s SUMO + PPO), about 230 000 agent-decisions per episode.

**Budget, frozen:** **600 episodes per run** ≈ 1.4e8 agent-steps, the same order as the paper's 1.65e8.

**Runs (all reward B, light FT)**, 12 in parallel (`xargs -P 12`), resumable:

| Use | Arms | DQN seeds |
|---|---|---|
| Pilot | B-SPaT, B-noSPaT | 13, 113 |
| Confirmation (trained NOW to save time) | B-SPaT, B-noSPaT | 213, 313, 413, 513 |

The confirmation fleets are evaluated on 420–429 **only if** the pilot gate (Amendment R1) passes on SELECT. Otherwise they are archived unevaluated. Their training cannot see SELECT or test traffic (training traffic 0–7 only).

Reward A is not run in this round (machine capacity). It is optional as registered.
* 059 freeze (12:35): 8d9879e5c22c; CITY_fleet_v8 b01cf2734a75a610 (final: only the .item() logging fix since the smoke); CITY_fleet_train_v8_ppo e0d18375d137edb8; CITY_v8_check 9285763eec84b1ba; CITY_spat_feature f4628194fdcdf4f3
* Scheduling (12:36): 12 runs in parallel ran each process at about 55 % CPU (episode 0 was 3.1× slower than the smoke on identical decisions). The 8 confirmation trainers (s213–s513) are PAUSED with SIGSTOP (not killed; resumable as is). The 4 pilot runs continue at full speed. A background waiter sends SIGCONT when the 4 pilot fleets are saved. No change to any run's configuration.
* Evaluation code frozen (12:38, before any learned evaluation): CITY_eval6 5c66c4e836174985; CITY_spatp_report b6e5280cc7d52774; RUN_spatp_eval.sh 9a1fe97cdee34a73. eval6 smoke (a 3-episode smoke fleet, GLOSA and always-SUMO, traffic 100, 600 s) showed the plumbing works; those numbers are not evidence.
* Scheduling (13:44): 4 of the 8 paused confirmation trainers (s213, s313, both arms) RESUMED (SIGCONT) to use idle cores. s413 / s513 stay paused.
* eval6 extended (13:58), append-only: a new fleet spec IC:GLOSA for the D2 control. P: and GLOSA are byte-identical in behaviour. New hash b908725061abfa12 (the frozen hash at 12:38 was 5c66c4e836174985).

## Amendment R4 (14:02): ONE fix chosen from the diagnostics (ledger C-39, C-40, C-41); reward B pilot kept running as registered

**Evaluation bug found by the v9 identity check (C-41).** `CarPPO` in evaluation mode never sent the exit release. It is fixed for evaluation only, and training behaviour is byte-identical (the v8 check numbers are unchanged). The contaminated D1 / D2 rows are archived in `legacy/` and re-run.

**Diagnosis behind the fix:**
- B is gameable by crawling (C-40);
- PPO from scratch never reaches always-SUMO on B, even on TRAIN (C-39);
- the continuous class CAN represent a near-good controller (IC-GLOSA: fuel −6.7 %, agent TL −0.5, but human TL +2.4 and 4.2 teleports / run; C-40).

**Recipe v9** (`CITY_fleet_v9.py`, `CITY_fleet_train_v9_ppo.py`):
- **Action:** the residual a = clip(a_IC + 1.5·tanh(u)) on the in-class base controller. The last layer is zero-initialised, so episode 0 is exactly the base controller (identity K1 PASS, bit-identical).
- **Reward "A-group":** −mean over vehicle-seconds of [(1 − v / v_lane)⁺ + 0.5 · fuel_mg / 1000] over ALL vehicles in each light-phase group, credited as in B. There is no threshold, so crawling pays delay, and SUMO cars are included.
- Everything else is v8: observation with SPaT on, PPO hyper-parameters, conventions.
- There is no no-SPaT arm: the base uses SPaT. The SPaT ablation is not part of v9.

**Predictions (registered before training):**

| # | Prediction |
|---|---|
| P1 | Episode 0 ≡ base controller. Verified (K1). |
| P2 | If the objective and the learner work from a good start, the A-group interval reward on TRAIN rises above the base's within the budget, and human TL falls below the base's while fuel stays within +1 % of the base. |
| P3 | If PPO DEGRADES the group reward from the base start, the learner / credit is the blocker independently of initialisation and objective. |

**Budget:** 400 episodes, FT, TRAIN 0–7.
- Pilot seeds 13, 113.
- Confirmation seeds 213, 313, 413, 513, trained in parallel and evaluated only if the gate passes.

**Endpoints on SELECT 100–104** (pilot) and **420–429** (confirmation, pooled):

| # | Requirement |
|---|---|
| (a) B6-1 vs always-SUMO | as in R1 |
| (b) vs σ* = 0.3 | as in R1 |
| **(d) vs the base controller** (learning must add value) | human TL superiority (upper < 0), agent fuel NI (upper < +1 %), agent TL NI (upper < +0.5) |

**Gate:** at least one pilot seed passes (a) on SELECT. Then confirmation is evaluated.

**Readings:**

| Outcome | Reading |
|---|---|
| (a) and (b) hold, (d) fails | the learned residual adds nothing over the heuristic |
| (a), (b) and (d) hold | the first candidate for M1 |
* v9 launch (14:02): 6 runs (seeds 13, 113, 213, 313, 413, 513), 400 episodes, nohup outside the spool (the spool is held by job 059). Hashes: CITY_fleet_v9 6c89c4dc55c59e76; CITY_fleet_train_v9_ppo 632e6f3402bf23c3; CITY_fleet_v8 (eval fix) 5633e75859666874; CITY_v9_check PASS.
* v9 evaluation frozen (14:03, before any v9 evaluation): CITY_v9_report 5586e4c8eb586eee; RUN_v9_eval.sh 81f80e5c6d70d9b6; CITY_eval6 9bdcabe651e37cb1
* Scheduling (14:04): all 8 B confirmation trainers are now PAUSED (SIGSTOP; pids in fleets/PAUSED_PIDS.txt and PAUSED2_PIDS.txt). They are resumed only if the B pilot gate passes; otherwise they are left unevaluated, which is the registered reading. CPU goes to the 4 B pilot runs (registered, kept) and the 6 v9 runs (Amendment R4).

## Amendment R5 (14:10): v10 = v9 with ONE change, DENSE per-agent credit. Launched in parallel because v9 is flat at about 40 episodes

**Observation behind it** (v9 logs, about 40 episodes, 6 seeds): the interval reward is flat (−0.7964 → −0.7951), ratio deviation is about 0.03 and the value loss is about 0.004. One group-average reward per agent per phase interval gives a per-decision signal that is small relative to noise. This is the credit suspect named in the guide.

**Change.** The reward of the decision at t, read at t+1 for the same car, is −[(1 − v_i / v_allowed)⁺ + 0.5 · fuel_i / 1000 + 1 · (1 − v_follower / v_allowed)⁺], with the immediate follower within 100 m and no threshold. Base controller, action, observation, PPO, budget (400 episodes), seeds and endpoints ((a), (b), (d) vs the base) are identical to v9.

**Smoke:** 99.7 % of decisions get a reward; GAE equals the naive recursion. K1 identity holds by inheritance (same action path).

**Predictions:**

| # | Prediction |
|---|---|
| P5-1 | If credit was the blocker, the per-decision training reward moves within 100 episodes and the ratio deviation exceeds v9's. |
| P5-2 | The evaluated agent TL and human TL improve vs the base within budget. |
| P5-3 | If v10 is ALSO flat, the blocker is the optimiser / learner, not credit. |

**Scheduling:**
- v9 confirmation seeds (213, 313, 413, 513) are PAUSED (SIGSTOP). They resume only if the v9 pilot gate passes.
- v10 runs pilot seeds 13, 113 and confirmation seeds 213, 313 now.
- v10 confirmation seeds 413, 513 start when cores free up.
* v10 launch (14:10): CITY_fleet_v10 cd4f8dfea357baf9; CITY_fleet_train_v10_ppo 0f96e60aa879e702
* v10 evaluation frozen (14:10, before any v10 evaluation): CITY_v9v10_report e2555976d5d0ab5e; RUN_v10_eval.sh 5d28eaf83a78dd8e

## Amendment R6 (14:18): a learned fleet by derivative-free policy search on the DEPLOYMENT objective (parallel branch; motivated by D1: B does not encode the TL constraints, and by D2: PPO credit / learning is the blocker)

**Class.** GLOSA with 3 learned parameters θ = (b, v_lo, d_act) (`scripts/CITY_es_glosa.py`):
- on non-green with valid SPaT within d_act of the stop line: v = clip(d / (ttg + b), v_lo, v_allowed);
- otherwise release to SUMO;
- bounds b ∈ [0, 6] s, v_lo ∈ [0, 8] m/s, d_act ∈ [30, 200] m.

θ0 = (0, 0, 200) is the simple heuristic GLOSA. Identity check: θ0 is bit-identical to GLOSA on traffic 0 (TL 54.62, fuel 89 786).

**Objective, on TRAIN traffic only (FT).** J = agent fuel % vs always-SUMO + 5 %/(s/veh) · [(ΔTL_agent)⁺ + (ΔTL_human)⁺]. Fuel is primary, and TL increases are penalised directly. This is a constrained-optimisation surrogate: no reward shaping, no credit assignment.

**Search.** 24 Latin-hypercube candidates (θ0 included) on traffic {0..3}, then 12 rounds of (1 + 4) local search scored on {0..3} ∪ {4..7}, with common random numbers.

**Seeds:**
- search seed 1 = pilot;
- search seeds 2–5 = confirmation, each yielding its own θ*.

**Endpoints:**

| Stage | Requirement |
|---|---|
| Pilot (SELECT 100–104) | (a) vs always-SUMO and (b) vs σ* as in R1, plus **(d′) vs θ0**: agent TL superiority (upper < 0) AND fuel NI (upper < +1 %). Learning must add value over the heuristic, which fails (b) on TL by +1.46 s/veh (D1). |
| Gate | the pilot θ* passes (a). |
| Confirmation (420–429, pooled over the 4 search seeds) | (a), (b), (d′) |

**Predictions:**

| # | Prediction |
|---|---|
| P6-1 | The search finds J(θ*) < J(θ0) on TRAIN. |
| P6-2 | θ* passes (a) and (b) on SELECT. |
| P6-3 | If (b) fails, this 3-parameter family cannot match σ* on TL, and a richer class is needed. |

This is a learned policy (black-box policy search) in a deliberately small, interpretable class. It is not RL eco-driving and is not claimed as such.
* R6 launch (14:18): CITY_es_glosa 0e664db8066addab; CITY_eval6 (+ES spec, append-only) 65c1ed2cbb15237f
* R6 evaluation frozen (14:19, before any R6 evaluation): CITY_es_report f860569e86ef65f7; RUN_es_eval.sh 3ddf3f726e6aabd1

## Amendment R7 (14:55): the same GLOSA family on the σ\* base driver (one change: the base driver; registered before any R7 run)

**Motivation (C-43).** R6 failed (b) on agent TL by +1.84 s/veh, and the search found no GLOSA parameter that closes the gap. In R6, and in every GLOSA-type fleet so far, the agent car is driven by SUMO Krauss at the default σ = 0.5 whenever it is released (outside d_act, on green, or without valid SPaT). σ\* drives at 0.3 throughout. No GLOSA parameter touches the released driver.

**Hypothesis H7.** The (b) TL failure comes from the base driver, not from the SPaT-informed approach control.

**The one change.** Each agent car gets `setImperfection(v, σ*)`, with σ\* = 0.3 (frozen earlier on SELECT), at departure. This is exactly the σ-family mechanism (CITY_eval4_sigma). Everything else is identical: membership, SPaT feature, the GLOSA rule, release, search code and bounds.

The search objective keeps its definition **relative to the fleet's own base driver**:

J = fuel % vs σ\* + 5 · [(ΔTL_agent vs σ\*)⁺ + (ΔTL_human vs σ\*)⁺].

In R6 the base driver was σ = 0.5, which is always-SUMO.

**Arms:**
- **R7a (fixed rule, no learning; diagnostic and the "GLOSA with the same information" baseline on the strong base).** GLOSA∘σ\* = θ0 on the σ\* base. Evaluated on SELECT 100–104 and on traffic 420–429. Nothing is selected on 420–429.
- **R7b (learned).** The R6 search (same code via `ES.search`; J replaced as above), search seeds 1–5:
  - pilot is seed 1 on SELECT: (a) vs always-SUMO; (b) vs σ\*; (d′) vs GLOSA∘σ\*, i.e. agent TL superiority AND fuel NI +1 %;
  - gate is (a);
  - confirmation is 420–429, pooled over seeds 2–5, with (a), (b) and (d′).

**Identity checks (must be able to fail; exit 1):**
- K7-1: base σ 0.3 with a never-firing θ = (0, 0, −1) equals the eval4_sigma σ 0.3 rows on traffic 0 (5400 s): city / agent / human TL, agent fuel and teleports.
- K7-2: base σ 0.5 with GLOSA equals the plain eval6 GLOSA rows on traffic 0.

**Predictions:**

| # | Prediction |
|---|---|
| P7-1 | GLOSA∘σ\* vs σ\*: fuel upper < 0 and agent TL upper < +0.5, i.e. (b) passes. If it fails on TL, H7 is rejected: GLOSA's approach control itself costs TL against σ\*. |
| P7-2 | GLOSA∘σ\* passes (a) on 420–429. |
| P7-3 | From the flat R6 landscape: the R7b search returns θ ≈ θ0, so (d′) fails. If so, learning adds nothing in this class, M1 is not reached by R7b, and GLOSA∘σ\* is reported as the strong same-information baseline that any learned fleet must beat. |

**Status.** R7a is a baseline/diagnostic, not an M1 claim (nothing is learned).
* R7 checks (14:57): `sbase/check/sbase_check.txt` **PASS**. K7-1, K7-2 and K7-3 are bit-identical. The traffic-0 smoke (GLOSA∘σ\* vs σ\* fuel −7.62 %, TL −0.32) is not an endpoint.
* R7 launch and evaluation frozen (14:58, before any R7 evaluation):

  | File | SHA-256 prefix |
  |---|---|
  | CITY_eval6_sbase | 5e5fc087a5807e3f |
  | CITY_es_glosa_sbase | b1b6aa1e98783542 |
  | CITY_sbase_check | c0cdd565f923f3f8 |
  | CITY_sbase_report | b1fbcfdec1e74bdc |
  | RUN_sbase_eval.sh | 151f277ab33fab88 |
  | sbase/RUN_sbase_search.sh | ad6f35e98f73435b |

## Amendment R8 (15:04): lane-aware release (one change; registered before any R8 run; motivated by the C-44 teleport diagnostic)

**Diagnostic (`sbase/diag_tele/`, seeds 420 / 424 / 425 with the σ\* base, and 425 with the 0.5 base).** All 8 fleet-caused teleports are the same event. Two AGENT cars stand side by side at the stop line (position = lane length), on adjacent lanes, each on the wrong lane: best-lanes offset +1 / −1 and no continuation. The link is green and the last command was a release. They wait 300 s and teleport as a pair. This is a lane-swap deadlock. The plain-GLOSA run on 425 shows the same pairs at the same times.

**Hypothesis H8.** Commanded speeds suppress SUMO's strategic and cooperative speed adaptation for lane changes. Two agents abreast receive the same v = d / ttg (same d, same ttg), so they stay in lockstep and cannot swap lanes before the lane end.

**The one change.** The GLOSA rule commands a speed only when the vehicle is on a lane that continues on its route: on the current lane, `getBestLanes` offset == 0. Otherwise it releases to SUMO. Everything else is the R7a rule, GLOSA∘σ\*. Fleet name: **GLOSA-L∘σ\***.

**Identity check (KL).** With the lane condition switched off, the new class equals GLOSA∘σ\* bit-for-bit on traffic 0 (the K7-3 row).

**Traffic.** 420–429 and SELECT were inspected in the diagnostic, so they are development traffic for R8. Confirmation uses FRESH traffic **430–449** (20 seeds, for power; generated after this registration with the verified randomTrips config; generator re-verified at 15:03: rou_s420 is reproduced byte-identically). 300–319 stay reserved for the program's final confirmation.

**Predictions:**

| # | Prediction |
|---|---|
| P8-1 (mechanism, development seeds 100 / 420 / 424 / 425 / 426) | Fleet teleports drop to 0 on every one of these seeds (they were 1–4). |
| P8-2 (430–449) | GLOSA-L∘σ\* passes (b) vs σ\*: fuel upper < 0, agent TL upper < +0.5, human TL upper < +0.5. It also passes (a) vs always-SUMO, with teleports ≤ always-SUMO + 1. |
| P8-3 | Fuel vs σ\* stays ≤ −6 % (point). |

Reported beside these, descriptively: plain GLOSA-L (0.5 base) and GLOSA∘σ\* (without lane awareness) on the same traffic.

**Status.** This is a fixed rule, not an M1 claim (nothing is learned). If P8-2 holds, GLOSA-L∘σ\* is the strong same-information baseline that a learned fleet must beat. The lane-aware release then becomes a candidate fix for the learned fleets' action interface, to be registered separately with its own prediction.
* R8 traffic 430–449 generated at 15:05 (1 800 vehicles each). KL check (15:07) **PASS**, bit-identical. The traffic-0 smoke of the active rule (fuel +3.2 % vs GLOSA∘σ\*) is not an endpoint.
* R8 launch and evaluation frozen (before any R8 evaluation): CITY_glosa_lane 96f74363be9e9245; CITY_eval6_lane f581ad00b69db930; CITY_lane_check 07d8385787b0ac00; CITY_lane_report 8e61904562387717; RUN_lane_eval.sh 4372d54217b6cdb0;

## Amendment R9 (15:12): a LEARNED fleet that must beat GLOSA-L∘σ\* — 4-parameter policy search (registered before any R9 run)

**Motivation (C-46).** GLOSA-L∘σ\* passes (a) and (b) on fresh traffic, but lane-aware release costs about 2.8 points of fuel against GLOSA∘σ\*. It releases on the whole approach whenever a lane change is needed, while the deadlocks happen at the lane end.

**Class: GLOSA-LD∘σ\*, θ = (b, v_lo, d_act, d_lc).** It is GLOSA-L∘σ\*, except that a car on a lane that does not continue is released only when dist < d_lc; farther from the stop line it is still commanded. Bounds:
- b ∈ [0, 6];
- v_lo ∈ [0, 8];
- d_act ∈ [30, 200];
- d_lc ∈ [0, 200].

θ_L = (0, 0, 200, 200) is GLOSA-L∘σ\*, and (0, 0, 200, 0) is GLOSA∘σ\*.

**Identity checks (exit 1):**
- KLD-1: θ_L equals the GLOSAL:0.3 rows on traffic 0.
- KLD-2: (0, 0, 200, 0) equals the GLOSA∘σ\* rows on traffic 0.

**Objective, on TRAIN 0–7 only.** J = fuel % vs σ\* + 5 · [(ΔTL_agent vs σ\*)⁺ + (ΔTL_human vs σ\*)⁺]. This is the R7b objective; deadlock costs enter through TL.

**Search.** The R6 procedure generalised to 4 dimensions: 24 LHS candidates on {0..3} with θ_L included, then 12 rounds of (1 + 4) local search on {0..3} ∪ {4..7}, steps of 15 % of the range. Search seeds 1 (pilot) and 2–5 (confirmation).

**Endpoints:**

| Stage | Requirement |
|---|---|
| Pilot (SELECT 100–104) | (a) vs always-SUMO; (b) vs σ\*; **(d″) vs GLOSA-L∘σ\***: fuel superiority (upper < 0) AND agent TL NI (upper < +0.5) AND human TL NI (upper < +0.5) AND teleports ≤ base + 1. |
| Gate | the pilot passes (a) AND (d″). Unlike R6 / R7b, the gate includes (d″), because (a) alone is now met by the fixed rule and says nothing about learning. |
| Confirmation (FRESH traffic 450–469, 20 seeds, generated after this registration; pooled over search seeds 2–5) | (a), (b), (d″); per-seed (d″). |

**M1 claim rule.** A learned fleet worth deploying requires (a), (b) and (d″) on the confirmation, i.e. learning adds value over the best same-information rule.

**Predictions:**

| # | Prediction |
|---|---|
| P9-1 | d_lc\* < 200 on at least 3 of 5 search seeds: the search trades part of the lane-aware release back for fuel. |
| P9-2 | The confirmation passes (d″): fuel gain over GLOSA-L∘σ\* with TL NI. |
| P9-3 (risk) | Teleports reappear at small d_lc; the TL penalty in J should keep d_lc away from 0. |
* R9 traffic 450–469 generated at 15:12, after registration. KLD-1…3 check (15:14) **PASS**, bit-identical.
* R9 launch and evaluation frozen (before any R9 evaluation): CITY_glosa_lane_d.py 3295a2bbefb1b260; CITY_eval6_lane2.py 5b65ee1dec079db6; CITY_lane_d_check.py 0c17be23b93877be; CITY_lane_d_report.py 92446b0ddcb24cb9; RUN_lane_d_eval.sh 2ed06c07f467bb16; RUN_lane_d_search.sh 5da5c29d5779af79;

## Amendment R10 (15:24): PPO residual on the confirmed rule GLOSA-L∘σ\* (fleet v11; registered before any training run)

**Why.** R9 asks whether policy search adds value over the confirmed rule; R10 asks the same of RL. Every earlier PPO fleet (B, v9, v10) ran on the interface with the C-45 deadlock and on the σ 0.5 base driver. R10 starts from the confirmed rule, so the question is only whether RL adds value on top of it.

**Fleet v11** (`scripts/CITY_fleet_v11.py`; trainer `CITY_fleet_train_v11_ppo.py`, derived from the frozen v10 trainer by swapping the class):
- The σ\* base driver.
- The policy acts only where GLOSA-L∘σ\* commands; everywhere else it releases exactly as the rule does.
- Speed residual: cmd = clip(v_rule + 3·tanh(u), 0, v_allowed). Zero-initialised actor (V9.NetR, log-std −1), so the deterministic policy at episode 0 IS the rule.
- Dense per-agent cost (v10 dense_cost: own delay share + 0.5·fuel/1000 + follower delay share) every second, credited to the car's latest decision, including the post-release seconds.
- Segment = zone visit; terminal on exit or arrival; truncated on teleport or episode end.
- Observation (13, SPaT on), PPO, GAE and scales as v8.
- 400 episodes, 3600 s, TRAIN 0–7 in rotation; the last checkpoint is the result.

**Checks (exit 1).**
- K10-1 identity: zero-init deterministic fleet ≡ GLOSAL:0.3 on traffic 0.
- K10-2 training smoke: segments, log-prob, command range, GAE equals the naive recursion, dense credit present, no fleet teleports in the smoke.

**Seeds.** Pilot 13 / 113; confirmation 213 / 313 / 413 / 513, launched together with the pilot (CPU is free; their evaluation is gated).

**Endpoints (as R9):**

| Stage | Requirement |
|---|---|
| Pilot (SELECT 100–104), per seed | (a) vs always-SUMO; (b) vs σ\*; (d″) vs GLOSA-L∘σ\*: fuel upper < 0, agent TL upper < +0.5, human TL upper < +0.5, teleports ≤ base + 1. |
| Gate | ≥ 1 pilot seed passes (a) AND (d″). |
| Confirmation (FRESH 450–469, pooled seeds 213–513) | (a), (b), (d″); per-seed (d″). |

**M1 rule.** (a), (b) and (d″) on the confirmation.

**Predictions:**

| # | Prediction |
|---|---|
| P10-1 | Training teleports stay ≤ 1 per episode, i.e. the interface fix carries over to a stochastic learner. |
| P10-2 | The same-traffic-seed mean reward per decision rises over training (descriptive). |
| P10-3 | Pilot (d″) passes for at least one seed. Prior: low-to-moderate; v9 / v10 learned little from a base controller. |
* R10 checks (15:25): `fleets_v11/check/v11_check.txt` **PASS**. K10-1 is bit-identical to GLOSAL:0.3. K10-2: 11 379 decisions, 0 teleports, GAE equals the naive recursion. The 2-episode smoke trainer ran (0 teleports).
* R10 launch and evaluation frozen (before any R10 training or evaluation): CITY_fleet_v11.py 5205f39256e1c0f4; CITY_fleet_train_v11_ppo.py 65aef1a613c9d96d; CITY_eval6_v11.py 242e2a2e6a4fa103; CITY_v11_check.py c00cb226f404c492; CITY_v11_report.py b45bec31703bd265; RUN_v11_eval.sh 6c92da59c3077084; RUN_v11.sh f2c98bca7778a060;
