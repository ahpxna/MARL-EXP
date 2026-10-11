# PROTOCOL WAVE 10: a corrected DC-Ada port, and the cause of the second-network failure (registered 05/10 ~20:15, before any wave-10 code was run)

**Why (the user, 20:0x):** "chạy lại DCA3 cho đúng rồi so sánh lại đi, tiếp tục tìm nguyên nhân ko generalize dc trên spider hay các map khác".

**Context (C-143):**
- DCA2's tuning compared quarter-horizon candidates against full-horizon references, zeroed the LayerNorm scales, and omitted the author's output bound. It is void as a DC-Ada comparison.
- W8-1 D2 used the forecaster's raw event-head predictions (first 20 000 rows), not the served answers. Its 21.5 s is not comparable with grid4, and the cause of the spider failure is not established.

**Common rules:** as waves 6–9 (PYTHONHASHSEED 0, OMP 1, the queue with the 15 GB guard, smoke first, strict reports checking teleports and unfinished trips; crossed bootstrap, `CITY_wave2_report_v2` draws, B 2000).

## W10-1 DCA3: the corrected DC-Ada port, matched budget and 4× budget

**Code:** `scripts/CITY_dca3_run.py` and `scripts/CITY_w7_dca3_tune.py`, written by the independent audit; I reviewed them at 20:05.
- **Horizon:** references and candidates both pass through the DCA3 wrapper, so DCA3_END = 1350 s applies to both, asserted per rollout.
- **Initialisation:** the author's TransformationLayer, i.e. zero linear layers and LayerNorm weight 1, which gives the exact identity.
- **Output:** `nan_to_num` and a [−10, 10] bound.
- **Search:** robots in sorted order; M 5, σ 0.05, τ 0, step 1; common random numbers per round (the round's TUNE seed).
- **Budget:** 176 truncated rollouts including the references, i.e. 176 × 1350 s = 44 × 5400 s, TSI's grid budget.
- **Tuning setting (as DCA2):** lights t4–t8 with the TSI-2 providers, development fleet L11_s13, TUNE 660–663 (the budget reaches the first two seeds).

**Arms:**
- **DCA3**, budget 176 (registered).
- **DCA3x4**, budget 704 (secondary, descriptive): DC-Ada given four times TSI's light-side budget.

**Confirmation** on **fresh grid4 traffic 840–859**, generated after a non-existence check:
- lights t4–t8 × fleets s213–s513 × 20;
- arms R, TSI2 (TSI-2 per-light configuration), DCA3, DCA3x4, all through `CITY_f1a1_run.py`, the DCA arms through the DCA3 wrapper at full horizon.

**Self-check KW10-1:** the DCA3 wrapper with the initial (identity) parameters reproduces the plain service-only row (HYB) bit for bit on one cell (t4, s213, seed 840).

**Decisions (one-sided α 0.05):**
- **(a)** DCA3 meets every M3 limit vs R.
- **(b)** Ordering TSI2 vs DCA3 on agent fuel and agent TL, with the rule of W7-2 (b):
  - "TSI better" iff both uppers ≤ 0 with one < 0;
  - "DCA3 better" iff both lowers ≥ 0 with one > 0;
  - otherwise "no ordering".
- **(c)** Secondary: the same for DCA3x4.

## W10-2 Served-answer forecast accounting, with publication vs shadow (replaces W8-1 D2)

**Logger:** `scripts/CITY_w10_run.py`, installed at run time; no evaluator is edited.
- It wraps the `spat` attribute of every fleet module, so it records exactly what the fleet receives: time, light, link, ttg, ttr, valid. It covers every query of the full episode.
- The phase trace comes from `--record`.
- **Realized targets:** time to the first second at which the link's movement is green (ttg), and to the first second at which it is no longer green (ttr), from the trace and the program's link states.

**Modes:**
- **SERVE:** the provider's answer is delivered and logged.
- **SHADOW:** the provider is called and logged, but the fleet receives `valid = False`, so it drives as σ*.

**Self-check KW10-2 (the matcher must be able to fail):** under FT with the fleet's own program SPaT (exact by construction, C-38), the logged answers must equal the realized targets on every valid query, for one declared offset convention c ∈ {−1, 0, +1}. That c is then fixed for every other arm. If no c gives 0 mismatches on both networks, W10-2 is VOID.

**Runs:**

| Network | Lights | Fleet | Traffic | Arms |
|---|---|---|---|---|
| grid4 | t4, t5 (TSI-2 configuration) | s213 | TUNE 660, 661 | SHADOW, HYB (service), TSI |
| spider | RLK11, RLK111 (attempt-1 configuration) | rule fleet GLOSAL:0.3 | TUNE 1100, 1101 | SHADOW, HYBK, TSIK |
| both | (exactness self-check) | | | FT_EXACT (the fleet's own program SPaT under FT) |

**Readings (descriptive):**
- MAE, bias and the share > 5 s by network and arm.
- Inherent error = SHADOW.
- Performative shift Δ_pub = HYB − SHADOW (and TSI − SHADOW).

**Registered interpretation:**
- If the spider SHADOW error is grid4-like (within 2 × grid4's) but Δ_pub is much larger (≥ 3 × grid4's), the spider failure is a **performative** (publication-induced) forecast shift.
- If SHADOW itself is ≥ 3 × grid4's, the spider light is **inherently less forecastable** from these features.
- Otherwise: not attributed by forecast error.

## W10-3 Following vehicles held back by commanded agents (single-lane hypothesis)

**Hypothesis:** on spider and rand3 every edge has one lane, so a human driver behind an eco-gliding agent cannot overtake (grid4 has two lanes).

**Measure:** in the W10-2 runs, every second, for each agent whose speed is held below its SUMO speed (getSpeedWithoutTraCI − getSpeed > 0.5 m/s), take its follower within 50 m (getFollower). If that follower is a human vehicle, count one **held human-second** and add its speed deficit to its allowed speed.

**Readings (descriptive):**
- Held human-seconds per commanded agent-second, and per run, by network and arm.
- The human TL change of the arm vs SHADOW (σ* driving).

**Registered interpretation:** "single-lane holding" is supported iff the spider rate is ≥ 3 × grid4's AND spider's human TL rises under the service while grid4's falls.

## W10-4 Spider with two lanes (single-factor test), registered here and implemented after W10-1…3

`netgenerate --spider`, same arms, circles and spacing as spider, `--default.lanenumber 2`, all junctions TLS.
- Same demand rule (period 2.0) and the same rule fleet.
- New RLK lights (2 seeds, 120 episodes), the spider TSI pipeline from scratch, and a confirmation on fresh traffic.
- **Decision:** TSI meets every M3 limit vs R on spider-2L (α 0.05).
- **Reading:**
  - PASS ⇒ the lane count (overtaking and capacity) is a sufficient cause of the spider failure under this pipeline.
  - FAIL ⇒ it is not.
- The details (traffic seeds, the FT program of the 2-lane build, the job) are registered in an amendment before its code runs.

## W10-2b on rand3

After 073 NET3 completes, W10-2/3 are repeated on rand3 with its lights and providers (SHADOW / HYB / TSI, 2 lights × 1 fleet × TUNE 660–661).

## Queue

| Job | Content |
|---|---|
| 072e_W10_DCA3.sh | tuning ×2 budgets, confirmation, report |
| 072f_W10_DIAG.sh | W10-2 + W10-3 on grid4 and spider |

- Both are queued before 073 NET3, which stays last among the registered networks.
- W10-4 and W10-2b are added by amendment.
- **Directories:** `research/city_sim/w10_20261005/{dca3,diag}/`.

## Amendment A1 (20:2x, from the 072f smoke only; no full W10 run had started)

- **Measure change:** `getSpeedWithoutTraCI` equals `getSpeed` in this SUMO build (max difference 0.0 over 13 648 agent-seconds). The W10-3 "held" condition is therefore redefined as **the agent's last `setSpeed` command is below its allowed speed by more than 0.5 m/s**. Commands are recorded by wrapping `libsumo.vehicle.setSpeed` with a pass-through; the smoke time losses are unchanged bit for bit.
- **Fix:** the fleet object is now captured at run time, because `CITY_eval6_v11` rebinds `E4.load_fleet` at import.
- **Smoke result:** KW10-2 PASS on both networks (offset c = 0 for ttg and ttr, 100 % exact).

## Amendment A2 (20:3x): W10-4 spider-2L details, registered before any W10-4 code ran

**Network** `research/city_sim/net/spider2l.net.xml`:
- **Command:** `netgenerate --spider --spider.arm-number 6 --spider.circle-number 3 --spider.space-radius 150 --spider.omit-center true --default.lanenumber 2 --default.junctions.type traffic_light --tls.left-green.time 0` (SUMO 1.27.1).
- **Why `--tls.left-green.time 0`:** without it, SUMO adds 6-s protected-left phases at three junctions.
- **Same as spider:** geometry, 60 edges, 18 signals; 12 of the 18 signals keep their exact program durations.
- **Disclosed confound:** SUMO's signal generation turns the six inner-ring signals B1–B6, which have three greens (27 / 3 s) on the 1-lane build, into two greens (42 / 3 s) on the 2-lane build.
  - W8-1 D4 placed the agents' time cost in the **two-green** signals, so this by-product removes signals that were not the located source of the harm.
  - The single factor is therefore "lane count (overtaking, capacity), plus the inner-ring phase structure".

**Demand** `research/city_sim/demand/spider2l/p2.0/`, the spider rule (randomTrips, period 2.0 s, fringe 10, min distance 300 m):
- TRAIN 0–7, DEV 100–104, TUNE 1100–1103, confirmation 1110–1129;
- generated by the job after a non-existence check.
- Doubling the lanes also lowers congestion at the same demand, which is reported.

**Pipeline:** the spider recipe unchanged, through `scripts/CITY_sp2l_run.py` (the spider path patch, re-pointed).
1. RLK lights: seeds 11 and 111, 120 episodes, `CITY_m4g_train_light.py`.
2. Precondition P1: RLK vs FT city TL on DEV 100–104, SUMO drivers; the learned light is beneficial iff the upper < 0.
3. Precondition P2: rule fleet GLOSAL:0.3 vs σ* under FT on DEV 100–104, i.e. there is a fuel benefit to protect.
4. Open-loop table from σ* traces (TRAIN 0–7), then the closed-loop table (rule fleet on fck q 0.5, TRAIN 0–7).
5. N2K logs (fk q 0.1, TRAIN 0–7), fit, and KS-1 parity.
6. Tuning on TUNE 1100–1103 with the attempt-1 grid {(0,0), (1,0), (2,0), (1,0.25), (1.5,0.25), (1,0.5), (2,0.5)} and the registered rule.
7. Confirmation on 1110–1129: arms R, TSIK, HYBK, ADPK × lights 11 / 111 × the rule fleet.

**Decision (α 0.05, crossed bootstrap over light × traffic):** SPIDER-2L PASS iff TSIK meets every M3 limit vs R.
- If P1 or P2 fails, the decision is still computed but labelled conditional.

**Job:** 072g_W10_SP2L.sh, after 072f and before nothing else registered (073 is already running).

## Amendment A3 (20:4x, after the W10-2 / W10-3 / W10-2b and NET3 results were read; registered before any W10-5 / W10-6 code ran): two repairs aimed at the diagnosed causes

### W10-5 Spider attempt 4: a forecaster refit on logs collected with the service published

**Target:** the performative shift (W10-2 spider: +7.8 s; greens +50 %).

**Procedure:**
- With the attempt-1 configuration published (TSIK: N2K model `sptsi_20261005/model/n2k_sp<k>.pt` and the attempt-1 adapter (2, 0.5) / (1, 0.5)), log the N2K features on TRAIN 0–7 for each light.
- Refit N2K on these logs: `CITY_n2k.py fit`, one iteration of repeated retraining.
- KS-1 parity on the refit model.

**Arms** on fresh spider traffic **1170–1189** (generated after a non-existence check, spider rule), lights 11 / 111 × the rule fleet:
- R;
- TSIK1: the refit model, with the attempt-1 adapter unchanged, so that only the forecaster changes;
- HYBK1: the refit service alone.

**Decision:** the fourth attempt on spider, so **α = 0.00625**, and the chain bound over the four attempts is 0.09375 (Theorem 4). SPIDER ATTEMPT 4 PASS iff TSIK1 meets every M3 limit vs R.

**Secondary, descriptive:** publication shift and MAE of the refit forecaster (W10-2 matcher) on TUNE 1100–1101.

### W10-6 rand3 attempt 2: an extended adapter grid

**Target:** on rand3 no registered grid point qualified on 4 of 5 lights, and every choice sat at the upper edge (C-147).

**Grid:** A ∈ {2, 3, 4, 6} × B ∈ {0.5, 1, 2}. The registered rule is unchanged; TUNE 660–663; NET3 lights, fleets and providers unchanged.

**Confirmation** on fresh rand3 traffic **720–739** (NET3 rule, period 5.0, generated after a non-existence check):
- lights t21–t25 × fleets s213–s513 × 20;
- arms R and TSI-X (the new choice).

**Decision:** the second attempt on rand3, so **α = 0.025** (chain bound 0.075). RAND3 ATTEMPT 2 PASS iff TSI-X meets every M3 limit vs R.

### Reading

W10-2b classified rand3 as inherently less forecastable, so the registered expectation for W10-6 is a FAIL if forecast error dominates. A PASS would mean the light-side weight, not the forecast, was binding.

**Jobs:** 075_W10_SP4.sh and 076_W10_N3B.sh, queued after 072g.
