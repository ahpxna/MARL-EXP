# PROTOCOL W21: does the closed loop survive field-matched drivers and a real street map? (registered 15/10/2026, 14:06 EDT, before any W21 code ran)

**User decision (15/10, after the novelty review C-243):** "chạy arm forecast-alone so với no-SPaT của W20 trong thế giới W17; chạy cùng
cặp đó trên Midtown với một họ đèn có input ngưỡng."

**Why.** The paper's novel claim is a mechanism. SPaT-following gliders leave a learned signal's stop-thresholded inputs, the signal
lengthens its greens, and the forecast alone costs the fleet's vehicles time. That mechanism was measured only with Krauss human drivers
on grid4 (W19 C-228, W20 C-230). Two gaps remain:
- W17 (field-matched drivers) stopped before any SPaT arm, because the fleet showed no fuel benefit (D17-1 not shown).
- The Midtown transfer (MT-E) used B2D lights, which have no stop-thresholded input.

So we have not tested whether the loop occurs with realistic drivers, or on a real street map (`research/papers/audits/NOVELTY_REVIEW_TSI_20261015.md` §4).

**Seen before registration:**
- W17 stage 1 (`w17_20261008/fresh5/m1/report_m1.txt`):
  - fleet against humans under FT: −1.10 % (HBEFA4), −0.31 % (PHEMlight5);
  - light gate −33.7 s/veh;
  - R − OFF = 0 exactly: the fleet's base driver is the W17 human.
- W19 / W20 reports.
- MT-E / MT-F rows and reports.
- No W21 row exists.

**Sources at registration** (committed at 98d0c8993, unchanged; sha256 prefixes):

| File | sha256 |
|---|---|
| CITY_w17_world | 2c8731bb0872 |
| CITY_w20_run | 4bfd1e0baca9 |
| CITY_w20_bench | 3d5689232bf6 |
| CITY_w19_run | 8bbf091785fb |
| CITY_w19_obs | 382d7bd9ba56 |
| CITY_w19_train_light | 7766baac2d4d |
| CITY_w20_train_light | b7575c47ed66 |
| CITY_w19_prep | 056362dbc0f4 |
| DEMO_midtown | d1deddc045d2 |
| CITY_eval_n4 | f68333a82f03 |
| CITY_eval_f1 | 3b09b5aa39f4 |
| CITY_w9_run | c0253f1fd09e |
| CITY_w13_modes | 04c2d0ea0e1f |

No existing file is edited. New files are the two job scripts and `scripts/CITY_w21_report.py`.

## W21-A: the W20 pair in the field-matched world

**World.** `scripts/CITY_w17_world.py`: every car follows the W17-0 joint IDM. KW17-0 reads back the vehicle type in every process, and the job counts these lines.

**Lights.** Five families, five lights each:
- AH (k 34–38);
- SRL (84–88);
- RDQ (89–93);
- RMP (94–98);
- RWV (99–103, the threshold-free control).

All are trained **in this world** by the W19 / W20 trainers:
- the RL-H recipe, unchanged: double DQN, 120 episodes, TRAIN seeds 0–7, SUMO cars only;
- the DQN seed by slot, as in W19 / W20, so each slot has the same seed as its Krauss-world twin.

They go into `w21_20261015/w17/lights` (W19_LIGHTS = W20_LIGHTS = that directory). Checks:
- KW21-T: family, episodes, seed and input dimension of every checkpoint.
- The world is in force: a KW17-0 line in every training log.

The W17 lights t29–t33 are not used: their recipe is the same, but their seeds follow the other convention.

**Fleets.** The W17 FRESH5 fleets s2213, s2313, s2413, s2513. They were trained in this world under FT with exact program SPaT, and are frozen.

**Forecaster per light.** The FRESH3 recipe of W20 step 4, run in this world:
1. 8 all-human traces (TRAIN 0–7).
2. Open-loop table.
3. Closed-loop c2 prep: development fleet L11_s13 at q 0.5, as registered for W17-4; `CITY_w19_prep.py` under `CITY_w20_run.py`.
4. Feature logs with the development fleet on c2 at q 0.1.
5. N2 fit.

Checks:
- KF-3 (16 lights, 8 files);
- KW20-P (family in force in every prep; the widened net equals the family net);
- KW20-1 (independent recomputation of the observation, first light of each W20 family);
- KF-2 (offline–online parity, first light of each family).

Degenerate rule, as in W20: if a light's traces never complete one of its greens, its whole family is excluded.

**Traffic.** Fresh seeds 1420–1439. They are generated with W17's randomTrips command after a non-existence check. The wrapper creates their W17 copies.

**Arms** (HBEFA4; time losses are identical under any emission model, so PHEMlight5 is not run):
- **R**: no SPaT. The fleet drives as its base driver.
- **SV**: the forecast alone (hybrid provider, q 0.1, `CITY_eval_n4.py`), with the fuel-by-mode logger.

Gate rows:
- OFF: FT, all human.
- GATE: each light, all human.

**Precondition G21-A0** (per family; exclusion rule registered now). The family's lights beat FT in this world: GATE − OFF city time loss, upper bound < 0 at 95 %. A family that fails is reported and excluded from D21-A1. If RWV fails, D21-A1 is not computable, and only SV − R is reported.

**D21-A1[f]**, for f ∈ {AH, SRL, RDQ, RMP}, at α = 0.05/4 each:
- statistic: DiD of the agents' time loss, (SV − R)_f − (SV − R)_RWV;
- decision: SHOWN if the lower bound > 0;
- meaning: with field-matched drivers, publication harms the stop-thresholded representation more than the threshold-free control.
- bootstrap: lights resampled per family; fleets and traffic shared; B = 2000.

**Descriptive** (95 %):
- SV − R per family: fuel (HBEFA4), city / agent / human time loss, teleports, unfinished;
- mean green and served-lane halting under R and SV;
- whether the RWV control meets every limit;
- the W20 Krauss magnitudes alongside. This is not a paired comparison: the world, lights and fleets differ.

**Reading, fixed now.**
- SHOWN for a family: the loop is not an artefact of Krauss drivers for that family.
- NOT SHOWN: reported as "not shown with field-matched drivers and these fleets", never as "absent". The mechanism probes (green lengthening, served-lane halting) say whether the fleet still glides enough to leave the halting counts. In this world the fleet saves only about 1 %.

## W21-B: the pair on the full Midtown map with a stop-thresholded family

**Setting.** Exactly MT-E:
- `scripts/DEMO_midtown.py` → `CITY_w9_run.py none` → `CITY_w20_run.py`;
- MT_NET = midtown_full, MT_BASE = actrest: the 511 two-green signals are learned, the 56 multi-phase junctions run actuated programs;
- Krauss drivers;
- random demand p075, test days 0–4;
- W20_CREEP = 3, set as in MT-E but unused (no TSI-G arm).

**Threshold family: AH.** W19 lights t34–t38: grid4-trained, RL-H halting-count observation, 7 inputs, so it transfers to any two-green signal. Two library families were not chosen:
- SRL (19 inputs) and RDQ (40 inputs) are built per lane for grid4's 8 incoming lanes, so they cannot be applied at Midtown intersections.
- RMP (3 inputs, W20 t94–t98) is the **registered fallback**.

**Control: B2D.** W19 lights t59–t63; MT-E's family; position-binned observation, no stop-thresholded input.

**Fleets.** FRESH3 s1413–s1713, at a 50 % share.

**Forecaster.** Each light's W19 (or W20, for RMP) grid forecaster, adapted by DEMO_midtown as in MT-E: average identity, and the c2 table rebuilt on the Midtown programs.

**Arms:**
- R (`CITY_eval_f1.py --spat-arm none`) and SV (`CITY_eval_n4.py --n4 0.1:hyb:…`), for both families;
- for AH also LGar (lights alone, all human);
- ACT (SUMO actuated, all human), for the gate.

**Self-check KW21-B1** (reproduction of MT-E with the current code). The re-run B2D SV rows must equal MT-E's MTF_BGar rows, and ACT must equal MTF_ACT. Compared fields: time losses, fuel, waiting, teleports, unfinished, action digest. A mismatch is reported (with the source hashes of both); it does not stop the job.

**Gate G21-B0: the threshold family runs Midtown without gridlock.**
- Condition: the family's LGar has ≤ 20 teleports and ≤ 20 unfinished trips per run.
  - For reference, MT-E had 5.4 and 0.5; the gridlocked arms had 235–284 and 293–309.
- LGar − ACT city time loss is reported descriptively.
- If AH fails, RMP is run with the same arms and the same gate.
- If both fail, we report and stop.

**D21-B1** (α = 0.05):
- statistic: DiD of the agents' time loss, (SV − R)_thr − (SV − R)_B2D;
- decision: SHOWN if the lower bound > 0;
- bootstrap: crossed; lights resampled per family; fleets and days shared; B = 2000.

**Descriptive:**
- SV − R per family: fuel, city / agent / human time loss, teleports, unfinished;
- mean green and served-lane halting under R and SV.

**Reading.** As in W21-A, with two caveats:
- there are only 5 days of random demand;
- the multi-phase junctions stay actuated.

## Jobs

**Scripts:**
- `research/queue_night_20261005`-style job scripts `scripts/RUN_w21a_w17.sh` and `scripts/RUN_w21b_midtown.sh`, with an end-to-end smoke mode (SMOKE = 1) that writes into `w21_20261015/smoke_*` and goes through the report.
- Report: `scripts/CITY_w21_report.py`.

**Execution:**
- Both full jobs run in the user's terminal with nohup and logs.
- Lanes: A 6, B 3, concurrent.
- Disk guard 15 GB.
- PYTHONHASHSEED = 0, OMP_NUM_THREADS = 1.
- Smoke results are not evidence.

## Amendment W21-C (15/10/2026, 19:06 EDT, before any W21-C code ran): where does the Midtown time cost come from?

**User (15/10):** "chẩn đoán Midtown, kiểm cái ứng viên là forecaster grid chuyển sang Midtown bằng 'identity trung bình'".

**Seen before writing:**
- W21-B (C-246):
  - forecast alone costs the fleet's vehicles +9.54 s/veh (AH) and +8.49 s/veh (B2D) against R;
  - DiD not shown;
  - greens +3.2 % / +1.4 %.
- Post-hoc row comparison, made 19:0x from saved rows. On B2D t60–t63 (t59's refit learned congestion, MT-F), the forecaster refit on the full map, which has each light's own identity, costs agents +8.24 s/veh [+4.99, +11.69] against MTW_R. The grid forecaster with average identity costs +6.17 [+1.86, +10.14] on the same lights. So the average-identity candidate is **not supported** as the main cause. A refit changes both the identity and the training logs, so the two are not separated.

**Design** (descriptive; MT-E setting as W21-B; fleet s1413; days 0–4; the W10 tooling run unchanged under `DEMO_midtown.py`):
- **C1, forecast accounting on served answers.** `CITY_w10_run.py serve | shadow` around the SV command, with the phase trace recorded (`--record`). Arms:
  - SERVEg / SHADOWg: grid forecaster, AH t34–t38 and B2D t59–t63;
  - SERVEr / SHADOWr: refit forecaster, B2D t60–t63.
  - The matcher is CITY_w10_diag's `match`, with the AI lights' static-program link states of `midtown_full.net.xml`.
- **Self-checks:**
  - KW21-C0 (as KW10-2): under FT the fleet's own program SPaT equals the realized target plus one offset per field, on every valid uncensored query (600-s run, day 0). If it fails, the accounting is VOID.
  - KW21-C1: SHADOW rows equal MTW_R rows (time losses, fuel, counts, action digest). The shadow is the R dynamics plus logging.
- **C2, following exposure.** W10-3's held human-seconds per commanded agent-second, from the same rows.
- **C3, oracle on a fixed schedule.** R's recorded schedule (the SHADOWg trace) is replayed with (a) σ\*: SIG, `CITY_eval_f1.py --spat-arm none --replay-dir`; and (b) exact future timing: ORC, `CITY_m3_headroom.py --replay-dir`. Both use the PL fleet.
  - KH-1 (SIG reproduces SHADOWg / R) is checked on the first light-day. If it fails, C3 is skipped and reported.

**Readings fixed now:**
- **R1, forecast quality.** Compare shadow MAE on Midtown with W10's 3.77 s (grid4), 7.33 s (spider) and 15.34 s (rand3).
- **R2, performative shift.** SERVE − SHADOW MAE for AH and for B2D. A shift much larger for AH points to the threshold loop; similar shifts point to forecast error common to both families.
- **R3, refit vs grid forecaster.** Shadow and served MAE on B2D t60–t63.
- **R4, following exposure.** Compare with W10's 0.057 (grid4), 0.286 (spider) and 0.050 (rand3).
- **R5, information vs glide.** On R's own schedule:
  - If ORC − SIG agent time loss is not below 0, even exact timing makes this fleet's glide cost time on Midtown, and the cost is in the fleet's behaviour on this network, not in the forecast.
  - If ORC saves time while the forecast costs it, the cost is in the forecast's information.

## Amendment W21-D (15/10/2026, 20:5x EDT, before any W21-D code ran): is the Midtown time cost the published quantile on long greens?

**Seen (W21-C):**
- On Midtown the grid forecaster's shadow MAE is 22–24 s (grid4 3.77). Almost all of it is time-to-red: MAE 42 s, bias about −21 s (red announced early); time-to-green MAE is 3–8 s.
- Publication lowers the error (shift −1.3 / −4.6 s), so there is no performative growth.
- A more accurate refit forecaster (MAE 11.6 vs 16.7 s) did not lower the agents' time cost.
- Mean greens under R are 55–58 s, against about 15 s on grid4.
- C3 (oracle replay) was skipped: KH-1 failed.

**Hypothesis:** the published 0.1 quantile, chosen on grid4, announces red far too early on Midtown's long greens. Gliding vehicles then give up greens they could have caught, which trades the fleet's time for fuel.

**Design:**
- Arm SERVEg50: as SERVEg, but publishing the median (`--n4 0.5:hyb:…`).
- Grid forecaster; AH t34–t38 and B2D t59–t63; fleet s1413; days 0–4.
- Served-answer logging and traces as in W21-C.
- Compared on the same cells with SHADOWg (= R, KW21-C1) and SERVEg (q 0.1).

**Readings (descriptive):**
- **Supported** if both hold for both families:
  - SERVEg50 − SHADOWg agent time loss is below SERVEg − SHADOWg, by more than half of the latter;
  - the time-to-red bias shrinks.
- **Rejected** if the time cost does not fall.

## Amendments W21-E and W21-F (16/10/2026, before any W21-E / W21-F code ran)

**User (16/10):** "còn thí nghiệm nào chạy nốt hết đi".

**Seen before writing:**
- W21-A: D21-A1 shown for AH, SRL and RMP; not shown for RDQ. Forecast alone saves no fuel in the W17 world.
- W21-B / W21-C (Midtown).
- F1-4 at Salt Lake (C-216): TG − R +1.11 s/veh, HARM − R +1.29 s/veh (C-245). No forecast-alone arm was run there.

### W21-E: the repairs in the field-matched world

**Setting:**
- W21-A's world, lights (k 34–38, 84–103), fleets, forecasters, traffic (1420–1439) and R / SV rows are reused unchanged.
- The TSI-G site parameter CREEP is recalibrated on all-human logs **in this world**, using TRAIN 0–7 and the W20 rule.
- The calibration script `scripts/CITY_w21_twin_calib_w17.py` is a copy of `CITY_w20_twin_calib.py`. Each spawned worker imports `scripts.CITY_w17_world`, because spawned workers do not inherit the wrapper, and must print a KW17-0 line.

**Checks:**
- KW20-2: TSI-G with an empty fleet equals raw (AH t34, RDQ t89).
- KW20-3: twin fidelity, descriptive (AH t34).

**Arms:**
- BIS (TSI-G) for every light × fleet.
- TG (TSI's default adapter (1, 0.25) with the q 0.1 hybrid) for AH.

**Decisions:**
- **D21-E1[f]**, f ∈ {AH, SRL, RDQ, RMP}, at α = 0.05/4: BIS − R meets every limit. The limits are agent fuel upper < 0 (HBEFA4), time-loss uppers < +0.5, teleports ≤ R + 0.1, unfinished ≤ R.
- **D21-E2[f]** (secondary, same α): BIS − R meets the time limits alone, i.e. fuel is not required. This is registered because the forecast alone saves no fuel in this world (W21-A).
- **Descriptive:** BIS − SV; TG − R (AH); the RWV control.

### W21-F: the forecast alone on recorded Salt Lake demand

**Setting:** F1-4 exactly — 400S & 200W, RLW t11, fleets s13 / s113, the 20 CONF days, HBEFA4, fuel-by-mode logger. The F1-4 provider files (`tsi/prov`, `tsi/model`) are copied unchanged from git into `w21_20261015/saltlake/`.

**Arms:**
- SV: the four-green forecaster at q 0.1, with no adapter (`--light RLW`).
- R: rerun.

**Check KW21-F1:** the rerun R rows equal F1-4's R rows.

**Descriptive readings, compared on the same cells with F1-4's TG and HARM:**
- SV − R agent time loss;
- greens and served-lane halting, SV vs R.

The stop-threshold loop is **indicated** at this site if all of these hold:
- SV − R costs agents more time than TG − R;
- greens lengthen under SV;
- served-lane halting falls under SV.

The site has no threshold-free control, so the reading is descriptive.

## Amendments W21-G and W21-H (16/10/2026, before any W21-G / W21-H code ran): fleet response to long uncertain greens vs the map's geometry

**User (16/10):** "design exp để cho chạy luôn đi". Separate the two remaining candidates for the Midtown time cost:
- (i) the grid-trained fleet's response to long, uncertain greens;
- (ii) the map's geometry.

**Seen:**
- W21-C: KH-1 failed.
- W21-D: the median raised the cost.
- Cause of the KH-1 failure, found in the code (`CITY_eval4.run`, `--replay` branch): replay bypasses `build_light`, so the MT_BASE = actrest additional file is not loaded. The 56 multi-phase junctions then run static programs while their recorded phases came from actuated ones.

### W21-G: the oracle on a validated replay

**Wrapper `scripts/CITY_w21_mt_replay.py`:**
- In replay it appends the actrest additional file to the SUMO command, so the same programs are active as when recorded.
- Replay then forces every recorded signal's phase each second (CITY_eval4.Replay, unchanged).

**Schedules** (W21-C traces; fleet s1413; days 0–4; AH t34–t38, B2D t59–t63):
- R's: SHADOWg;
- the forecast run's: SERVEg.

**Arms on each schedule:**
- SIG: the PL fleet with no SPaT (`CITY_eval_f1.py --spat-arm none --replay-dir`);
- ORC: the PL fleet with the exact future timing of the replayed schedule (`CITY_m3_headroom.py --replay-dir`).

**Checks:**
- KH-1: SIG on R's schedule reproduces SHADOWg (time losses, fuel, counts, action digest) on every light-day. It is checked on the first light-day before the rest runs. If that light-day fails, C3 stays skipped.
- KH-1 is reported for all light-days.

**Readings (descriptive):**
- **R5.** On R's schedule, ORC − SIG agent time loss:
  - lower bound > 0, or interval containing 0 with point ≥ 0: even exact timing does not save the fleet time on this map, so the cost lies in its glide on this network, not in the forecast's information;
  - upper bound < 0 while SV − R > 0: the cost lies in the forecast's information.
- **Decomposition.** SV − R = (SIG on SERVEg's schedule − SIG on R's), the schedule effect, plus (SV − SIG on SERVEg's schedule), the information effect. ORC − SIG on SERVEg's schedule is reported alongside.

### W21-H: the same map with grid-length greens

**Setting:**
- MT_MAX_G = 20 s caps every learned green (Amendment MT-D's mechanism; forced switch). Grid4 greens average about 15 s.
- The SPaT provider is told the cap (MT_SPAT_CAP = 20, in the new wrapper):
  - time-to-red answers on a green are bounded by 20 − time in green;
  - time-to-green answers during the other green are bounded by that remaining time plus the 3-s yellow and the 1-s offset.

**Arms** (AH t34–t38, B2D t59–t63, fleet s1413, days 0–4):
- LGc: all human, capped;
- Rc: fleet without SPaT, capped;
- SVc: the grid forecaster at q 0.1, capped and cap-aware.

**Reading (descriptive):**
- If SVc − Rc agent time loss is below half of SV − R (uncapped, same lights, fleet and days, W21-C/D), long greens drive the cost.
- Otherwise the geometry, or another property of the map, does.
- LGc − ACT and Rc − R report what the cap costs the signals.
