# PROTOCOL: two-population wave 2, spool jobs 030–090

Written 04/10/2026, 04:58–05:00 EDT (wake 3). Every job below was written before it ran.

**Scope.** Program `research/papers/audits/TWO_POPULATION_EXPERIMENT_PROGRAM_20261004.md`. Results that existed when this was written: C-12 (B1/B1b), C-13 (V1), C-14 (B4F), C-15 (B3-X). The L4 panel was running and unread.

**Evaluator.** `scripts/CITY_eval2.py`.

**Common settings.**
- PYTHONHASHSEED=0 and OMP_NUM_THREADS=1. OMP=1 reproduced the h0 rows bit for bit.
- Seeds: SELECT 100–104; TEST 200–209 (same generator).
- One spool, run sequentially, 4 lanes per job.

## Evaluator self-checks (smoke 04:52–04:57, scratchpad)

| Check | Result |
|---|---|
| ACT × L-ACT_0 | = h0 row, TL 24.3052… |
| ACTP (grid4.net + actuated program file) | = ACT bit for bit |
| `q:0:0` adapter | = raw RL-J_0 h0 row |
| Open-loop replay of a recorded RL-H_0 × L-ACT_0 run with the same fleet | Reproduces TL, agent, human, fuel and discharge exactly (50.92…). Required two fixes found by this check: the index offset, and letting yellows advance on the program timer. |
| `green+oos` | = `CITY_xplay_guard`'s result (23.27) |
| Handoff ACTP → RL-H_0 at 1800 s | Runs: 43.25 plain, 24.34 with `green+oos` (one seed, disclosed) |
| MaxPressure | Runs (human, 23.04) |

* CITY_eval2.py 33ff123f94635857 (frozen for jobs 030–090)

## 030: F1 evaluation (endpoints U-1, U-2, U-3, V3-2 in `PROTOCOL_CITY_FLEET_UPGRADE_20261004.md`)

**Pairs.** P-J_0, P-J_1 (L0 = RL-J_t, F0 = L-ACT_t); P-C_0, P-C_1 (L0 = SIM-halt_k light, F0 = SIM-halt_k fleet).

**Fleets:** F0, FTv1, FTv2, NEWv2, human. Each is evaluated under L0 and under ACT, on SELECT and on TEST. 40 configs.

**V3:**
- L-ACT-v2_t0 and L-ACT-v2_t1 under ACT and RL-H_0..3, SELECT;
- V3-1, measured with `CITY_cmd_realized`'s logic on U: fleets (ACT, seeds 100–101).

## 040: F3, open-loop discharge diagnostic (reaction, without the light's feedback)

**Recordings** (`--record`):
- RL-H_t (t = 0..3) with human traffic;
- ACT with human traffic;
- each L0 with its F0.

All on SELECT seeds.

**Replays** (`--replay-dir --discharge`):

| Recorded run | Fleets replayed |
|---|---|
| RL-H_t and ACT | human, L-ACT_0..3, L-RLH_0 |
| L0 / F0 | F0, FTv1, FTv2, NEWv2, human |

**Self-check D-0.** Replaying a recording with the recording's own fleet reproduces its TL exactly (every recording). If this fails, job 040 is invalid.

**Metric.** Discharge rate = vehicles leaving the served incoming lanes per green second, plus start-up delay.

| | Prediction | Supported iff |
|---|---|---|
| D-1 (A-L) | Under replayed RL-H_t sequences, L-ACT_0's discharge rate is ≥ 5 % below human traffic's, while L-ACT_3's is within ±5 % | Seed means over t and SELECT. Phantom braking costs discharge for the fragile fleet only. |
| D-2 (A-F) | Under replayed L0 sequences, every qualifying F1's discharge rate is within ±5 % of F0's | The asymmetry, reaction side |
| D-3 (reported) | Discharge under the replayed ACT sequence for all fleets; start-up delays | — |

## 050: P2, mid-run handoff on TEST traffic 200–209

**Light-only upgrade.** ACTP → RL-H_t at t = 1800 s, fleet L-ACT_t′, guard ∈ {none, fallback, green+oos}. 48 configs.

**Simultaneous upgrade.** ACTP → RL-H_t together with L-ACT_t → L-RLH_t at 1800 s. 16 configs.

**Fleet-only upgrade.** L-ACT_t′ → L-RLH_t′ under ACTP. 4 configs.

**No-swap baselines.** ACTP × L-ACT_t′ × {none, green+oos}. 8 configs.

**Endpoint window.** Trips departing in [1800, 5400): the depart-window time loss, trip-weighted over the 1800, 2700, 3600 and 4500 windows.

| | Prediction | Supported iff |
|---|---|---|
| H-1 | A plain light-only upgrade raises window city TL over the no-swap plain baseline | ≥ 10/16 cells |
| H-2 | With `green+oos` active from t = 0, the light-only upgrade lowers window city TL below BOTH no-swap baselines (plain, guarded) | ≥ 12/16 cells. The upgrade benefit survives the transition with a fleet-side compatibility mode. |
| H-3 (reported) | Simultaneous vs light-only vs fleet-only; worst 900 s window; teleports | — |

## 060: F2, observation adapters at the frozen light (A-F, cell i)

All 4 pairs × {F0, FTv1, FTv2, NEWv2} × adapters {raw, q:0.5:0, q:1:0, q:1:0.5, q:1:1} on SELECT. 80 configs.

| | Statement | Rule |
|---|---|---|
| A-1 | Applies only to (pair, F1) where U-2 found harm (human TL up > 0.5) | The SELECT-best adapter, chosen with F0's human TL change ≤ +0.5 under it, recovers ≥ 50 % of the harm on TEST (run as job 065 if needed) |
| A-2 (reported) | Adapter effect on every pair / fleet | Shows whether the halting feature matters at all for these lights |

## 070: DC-Ada baseline (A-F cell i)

Script `CITY_dcada_tune.py`, written after this protocol and queued with its own freeze line. It is conditional on A-1 having a harmed pair. Otherwise it runs on P-J_0 / FTv2 as a reported comparator.

## 080: L3, guards on other fleets

Lights {ACT, MP, RL-H_0..3} × fleets {L-RLH_0..3, SIM-halt_0..3 fleets, L-FT_0..1} × guard {none, green+oos}, SELECT. 120 configs.

| | Prediction | Supported iff |
|---|---|---|
| G-L3 | `green+oos` does not harm robust fleets | For L-RLH_t under RL-H_0..3: agent TL change ≤ +1.0 s/veh in ≥ 14/16 cells |
| G-L3b (reported) | Effect on co-trained and FT fleets, and under MaxPressure | — |

## 090: published light baseline

MaxPressure × all 25 B3-X fleets (and human), SELECT. 26 configs. Reported. The light gain vs ACT with humans tells whether our learned lights beat a published classic.

## Amendment W1 (05:00, before job 040 runs): D-0 per recording

Replay forces only the light's own decisions and lets yellows advance on the program timer. Under a LEARNED light every green → yellow switch is a controller action, so replay is exact; this was verified for RL-H_0 × L-ACT_0.

Under ACT, gap-out ends greens inside the simulation step, so the forced yellow lags by 1 s. Therefore:
- D-0 is evaluated per recording.
- A recording that fails D-0 (expected: rec_ACT) is labelled "approximate (1-s lag)". It enters only the reported D-3, never D-1 or D-2.
- D-1 uses rec_RLH0..3; D-2 uses rec_RJ0, RJ1, SH0, SH1.

## Spool order and dry run (05:00)

Jobs, run sequentially by `scripts/RUN_spool_20261004.sh`:

| Job | Contents |
|---|---|
| 010 | L4 (own protocol) |
| 020 | F0 trainings |
| 030 | 90 configs |
| 040 | 59 configs |
| 050 | 76 configs |
| 060 | 80 configs |
| 080 | 120 configs |
| 090 | 25 configs |

Each job file's config generator was dry-run and the counts match the protocol.

* SPOOL_eval2_run.sh (helper; hash below)
* SPOOL_eval2_run.sh c1e3f93ca0033db4; job files: 030_F1_eval 8dc743e4a762; 040_F3_discharge 7e223acf454d; 050_P2_handoff 34fd78fc8f20; 060_F2_adapters e9f7a64bd570; 080_L3_guards 9a30ac0b92d5; 090_MP_baseline 18fedcb2d889; 
* CITY_dcada_tune.py a45b240304011e8b; 070_DCADA 047f888942e9 (tuner budget 8 rounds x (1 + 4) = 40 rollouts of 3600 s on training seeds 0-7, sigma 0.1, tau 0.2 s/veh; F1 = FTv2 of each pair)
* Amendment W2 (05:03, before job 070 ran): the 070 smoke check gave TL 25.08 at theta = 0 and 27.9 / 33.8 / 43.2 for three sigma = 0.1 candidates (seed 0). sigma 0.1 is far outside the local region of this light's inputs (b = 0.1 shifts h/10 by one vehicle and the phase one-hots), so job 070 uses sigma = 0.03, same budget (8 rounds x (1 + 4)). 070_DCADA new sha 269a4ffc241c.
* CITY_wave2_report.py 22bcffd23a06d7c5, CITY_green_guard_report.py 7a0431c31680b1dc (written before any row of their jobs)

## Amendment W3 (05:18, the user's pre-launch audit Addendum W-A..W-E; jobs 030–090 put on HOLD at 05:13 before any of them ran)

**1. Evaluator version 3.** `scripts/CITY_eval3.py` (sha ee59fd841a192ac6) replaces `CITY_eval2` for every held job. `CITY_eval2` is kept unchanged as the smoke version. Smoke self-checks (scratchpad, 05:1x):

| Check | Result |
|---|---|
| `none` | = h0 |
| `always` guard | = the all-human run, bit for bit. **The always-SUMO baseline IS the human-only run of the same light / seed, with the same membership and demand.** |
| Replay trace | phases, spentDuration and the action digest are equal at every second (not only TL) |
| Hot swap | `setProgram` did NOT keep the phase (3/16 lights; all spent reset). It is replaced by a **phase-boundary handoff**: each light switches just before its own next phase change, with the next phase set explicitly. 16/16 lights switched to the intended phase by t = 1803. No-swap = ACT. |

**2. Job 050 endpoint (W-A).**
- The registered endpoint, trip-weighted city TL of trips departing in [1800, 5400), is computed per episode from stored COUNT and SUM: Σ sum / Σ count.
- Added and reported separately, each never substituted for the other:
  - the cohort PRESENT on the road at the swap time;
  - the system delay increment per 900 s window over all vehicles present (`--delay-trace`).
- Rows from `CITY_eval2` are not used for 050.

**3. Splits (W-B).**
- Traffic 200–209 are renamed **VALIDATION**: development, read to choose methods.
- A new **CONFIRMATION** panel is reserved, to be built only after the method is frozen:
  - traffic seeds 300–319 (never generated or used; the demand registry has 0–7, 100–104, 200–209 only);
  - fresh policy seeds for BOTH populations, indices 4–8, never trained.
- Policy indices 0–3 are development partners: they were all seen in Q7b / B1 / B3-X / B4F / L4.
- L4's GG-2T keeps its registered verdict as the first use of 200–209.
- Every report prints SELECT and VALIDATION separately; no pooled CI.

**4. Reward-v2 correctness (W-C).** V3-1 (command-avoidance ≤ 0.2) is demoted to a behavioural diagnostic. Correctness is checked by trace: `scripts/CITY_v2_trace_check.py` (sha aff52c9229407382), with CarRLv2 unchanged and transition ownership read from CarRLv2's own setSpeed order.
- Smoke (900 s, random commands, ACT and RL-H_0): 61 491 + 61 255 non-terminal transitions match −(1 + 0.05a² + IDLE·[v_{t+1} < 0.1]); 509 + 524 terminal transitions match; 0 bad, 0 unattributed.
- Job 021 runs it for 5400 s with FT (teleports) and RL-H_0, so that the teleport, arrival and truncation paths are exercised. Each is counted separately.
- The behavioural diagnostic will use `CITY_cmd_realized_v2`: exact commands via setSpeed, and an idle-only realized cost that keeps the commanded acceleration term.

**5. Comparators (W-E, audit item 4).**
- always-SUMO = the human-only runs (verified identity).
- Matched-rate random override: job 055, guard `random:P` with P = the B4F fallback release share (0.046) and the L4 green+oos share (0.45), under RL-H_t × L-ACT_t′, SELECT.
- The fixed green guard is L4's `green` arm.

**6. Inference (audit items 2–3).**
- Cross-play cells are not independent. Uncertainty uses a crossed bootstrap over light-seed × fleet-seed × traffic-seed, with the SAME draws for every arm.
- Matched-pair estimands keep the pairs.
- "No harm" is non-inferiority: the upper CI bound of the harm must be < the pre-set margin.
- Reporter v2 is written before any verdict of the held jobs is read. B4F / L4 get a NEW analysis version; their registered verdicts are kept unchanged.

**7. Wording (W-E).** The conclusion is "in the panel tried, the car-side fallback helped clearly; τ clipping did not". NOT "observation repair does not work". If reward v2 removes most of the hazard, the story follows that result (reward bug), not compatibility.
* Amendment W3 job files (05:19): 021_v2_trace 33c00ea80c36; 030_F1_eval 5f72302dcf3b; 040_F3_discharge ce54d9011009; 055_random_override b7f415113bae; 060_F2_adapters 11074e25ca8a; 070_DCADA c1036035fe0d; 080_L3_guards 4de7077831ed; 090_MP_baseline b83ceb72e9dc; 095_P2_handoff f95dab5f5ace;  CITY_cmd_realized_v2 27c2733299cf55e4 (smoke ACT x L-ACT_0 900 s: avoided 0.999, idle-only cost gap 10.2 %); SPOOL_eval3_run 79eaedb7d5bc8368. Order: 021, 030, 040, 055, 060, 070, 080, 090, then 050 renamed 095 (runs last).
* CITY_wave2_report_v2.py 616b46043d5c6a4b (written 05:20 before any held job's row)

## Note on job 070 fidelity (05:45, audit Addendum W-E) — the job is HELD

`CITY_dcada_tune.py` is an ADAPTED port of DC-Ada, not a faithful reproduction.

**Kept from DC-Ada:**
- accept / reject random search;
- common random numbers within a round;
- the margin τ;
- the step α·σ·ε;
- reward-only updates.

**Changed:**

| Aspect | DC-Ada | This port |
|---|---|---|
| Transform | latent transform | affine o·e^s + b on the light's 7 inputs (14 parameters) |
| Rollouts | truncated candidate rollouts | full 3600 s rollouts on training demand seeds |
| Budget unit | environment steps | rollouts |
| Scope | per-robot adaptation | one shared transform for every light |
| σ | — | 0.03 (W2), set from one smoke check |

When the job runs, its tuning budget (40 rollouts) is reported next to the q_θ grid's selection budget, and to every other arm's.
