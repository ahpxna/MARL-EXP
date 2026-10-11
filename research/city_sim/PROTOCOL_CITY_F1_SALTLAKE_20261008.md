# PROTOCOL F1: TSI on recorded demand at two Salt Lake City corridors (registered 08/10/2026, 05:16, before any F1 code ran)

**User request** (08/10): "Có, viết protocol và xếp hàng" (yes, write the protocol and queue it), answering whether F1 should run (field-data survey, `research/papers/audits/FIELD_DATA_SURVEY_20261008.md`). Queue position: after jobs 095 and 096.

**Seen before registration:**
- The RESCO scenario files and the RESCO code `utils/csv_to_flo.py`.
- Weekday 16:00–17:00 mean movement volumes for 2023 (computed for this design):

| Signal | Total veh/h (sd) | Largest left turn |
|---|---|---|
| 7241 | 2,937 (377) | 149 veh/h |
| 7242 | 2,673 (674) | 476 veh/h |
| 7142 | 3,823 (1,328) | 340 veh/h |

- 7243 was not summarised: its file has 9 columns.
- No simulation has been run on these networks by us.

**Why it matters.** This is the first test of TSI on recorded demand: 5-min movement counts from two real Salt Lake City corridors, each with two adjacent signals, for every day of 2023. It answers the reviewer objection "synthetic networks only" for demand and geometry. It does not answer it for signals or fleets, which remain learned in simulation.

**Known risk.** On RESCO cologne8 the grid4 light recipe was worse than fixed time and the attempt stopped at the light gate (C-35, C-36). F1 has the same gate.

## F1-0 Port (code and self-checks; no decision)

**Networks:** `saltlake2_400sX200w` (signals 7241 at A3, 7242 at B3) and `saltlake2_stateXuniversity` (7243 at A3, 7142 at B3), with RESCO's geometry and lane closures unchanged.

**Programs** (new `tlLogic` built into a copied net with `netconvert --tllogic-files`; RESCO's files are not edited):
- Four greens per signal, built from RESCO's own phase states: EW left (RESCO phase pair 4), EW through and right (3), NS left (8), NS through and right (7), in lead-left order.
- Each green is followed by a 3-s yellow (each G/g that turns r becomes y) and a 1-s all-red.
- Right turn on red is as in RESCO ('s').
- Fixed time (FT): Webster cycle and splits from the training-day mean 16:00–17:00 volumes, critical lane-group flow per phase, saturation flow 1,800 veh/h/lane, lost time 4 s per phase. The cycle is capped to [60, 150] s and computed once from training days only.

**Demand:**
- RESCO's `generate_flow_from_csv`, unchanged, imported, including its between-signal adjustment.
- Window 15:55–17:00: 300 s warm-up, then a 3,600-s scored hour, the grid4 episode length.
- `random` seeded with the day index.
- Vehicle IDs are replaced in departure order by deterministic IDs `v<day>_<k>`, because RESCO uses uuid4 and fleet membership hashes the vehicle ID.
- Counts at the stop line are treated as demand. This is RESCO's assumption, stated as a limitation.

**Days.** 2023 weekdays, excluding RESCO's listed missing-data intervals; day index = day of year.

| Role | Days |
|---|---|
| TRAIN | weekdays Jan 9 – Apr 28 |
| TUNE | May 1–4 |
| DEV (gates) | 10 weekdays from Jun 5 |
| CONF (confirmation) | 20 weekdays: every third weekday from Sep 5, in order. **Not generated until the confirmation stage**; non-existence is checked. |

**Pipeline.**
- A runner `CITY_sl_run.py` points the grid4 stack at the network and the per-day routes (as `CITY_m4s_run.py` does for spider).
- Lights: `CITY_lightk.LightRLK` (keep / advance over the four greens; any K).
- Forecaster: `CITY_n2k.py` is fixed to K ∈ {2, 3}. A K-general copy `CITY_n2k4.py` gives r and the relative-position features length 4 and replaces the K == 3 flag by a K one-hot.
  - **KSL-4:** on spider rows (K ≤ 3) the copy's predictions are compared with N2K's on the same checkpoints. The features differ by construction, so the check is that `fit` → `parity` (KS-1) passes for the copy on the spider TRAIN logs; the K = 4 parity is checked on Salt Lake logs.

**Self-checks:**
- **KSL-1:** for each day, generated vehicles per route and 5-min interval equal what RESCO's own function produces with the same seed (identity), and the totals equal the CSV totals net of the between-signal adjustment (reported).
- **KSL-2:** FT on 3 DEV days gives 0 teleports and 0 unfinished trips by the end of the warm-up plus hour plus 600 s.
- **KSL-3:** every RESCO movement is green in exactly one of the four greens; yellows are 3 s and all-reds 1 s.

## F1-1 Light gate (registered, α = 0.05)

**Training.** LightRLK DQN, the RL-H recipe of grid4: Q7 observation width, halting reward, DT_L 5, MIN_G 5, 120 episodes, seeds 11 and 12 per network, on TRAIN days, no fleet (SUMO cars).

**G1:** RL − FT city time loss on the 10 DEV days, crossed bootstrap over light seed and day, one-sided 95% upper < 0 on both networks.
- If G1 fails on a network, that network stops (registered negative, like cologne8).
- One retry is allowed with 240 episodes, at α 0.025.

## F1-2 M1: a fleet worth deploying under FT (registered, α = 0.05)

**Training.** PPO fleet, the R10 recipe: 400 episodes, fleet seeds 13 and 113, the paper's fleet share, FT signals with the exact FT SPaT, TRAIN days.

**Decision M1-SL** (TUNE days for selection; DEV days as confirmation, since they are not used for fleet training):
- the fleet saves agent fuel against SUMO cars (upper < 0) under HBEFA4 and PHEMlight5;
- every M3 time-loss limit holds;
- teleports and unfinished trips are not higher.

If M1-SL fails, F1 stops: there is no benefit to protect.

## F1-3 M2 and F1-4 TSI (registered, α = 0.05; run only if F1-1 and F1-2 pass on a network)

**M2-SL (descriptive plus registered):** with the learned light and the old FT program served as SPaT, does the fleet lose its benefit? Same comparison as the paper's M2.

**TSI calibration.** As grid4, with the K = 4 forecaster:
- 8 TRAIN episodes per stage for the forecaster (table c2, N2K4, fit, KS-1 parity);
- adapter and quantile: the fixed default TG = (1, 0.25, 0.1) (no tuning, W15-1);
- rule R15-U on TUNE over the wave-13 grid with q ∈ {0.1, 0.5} (TU).

**Arms on the 20 CONF days** (light seeds × fleet seeds × days, crossed bootstrap B 2000, both emission models on the same trajectories): R (no SPaT), TG, TU.

**Decisions:**
- **D-F1a:** TG meets every M3 limit and saves agent fuel under both emission models.
- **D-F1b (descriptive):** TU − TG.
- **D-F1c (descriptive):** TG − R under IDM. Run only if F4 finds IDM closer to Peachtree than Krauss (protocol FIELD A1).

## Compute and queue

- Each stage is a separate job in `research/queue_night_20261005/pending`, written only after the previous stage's report.
- Job 097 (F1-0 plus F1-1) is queued after 096. F1-2 onward are written after G1.
- Disk guard as usual. Smoke-test every job first.

## Amendment A1 (08/10, 05:22; before any F1 code ran)

**Seen since registration:** nothing new about F1. (W15-6 selection lines and F4 calibration starts were seen; they are unrelated.)

1. **No warm-up.** An episode is 16:00–17:00, starting from an empty network and scoring every trip, exactly as the grid4 episodes. The pipeline has no warm-up exclusion, and adding one would make F1 differ from every other panel.
2. **Overlaps in the program.** Movements green in two consecutive greens (protected → permissive left) stay green through the transition. Only links that lose green get the yellow and all-red.
3. **Webster inputs:**
   - per-route mean vehicles per hour on TRAIN days, from the generated routes;
   - critical flow ratio per green = max over the served (route, link) pairs of volume / (1,800 × green lanes of that movement);
   - Y is capped at 0.9;
   - each green gets at least 5 s.

## Amendment A2 (08/10, 09:13; after the job-097 smoke, before any real F1-1 run)

**Seen:** the smoke of job 097 (2-episode lights, 3 DEV days).
- Webster FT city time loss: 43.6 / 84.8 / 49.0 s/veh at 400S and 66.3 / 156.9 / 69.5 at State & University (days 156 / 157 / 158).
- Day 157 has about twice the vehicles of its neighbours.
- At State & University A3, the Webster split was [34, 11, 5, 5] s. Rule A1-3 takes a per-phase maximum over routes, and that misreads lane groups when a movement is green in two consecutive greens. Example: westbound through on B3A3 lane 2 is green in RESCO's "protected left" phase and in the "all green" phase.

**Change: the FT baseline is tuned by simulation.**
- Start from the Webster durations.
- Coordinate descent per signal and green: ±5 s, green in [5, 60] s, cycle free.
- Objective: mean city time loss over 8 TRAIN days (every 10th TRAIN day, starting at the first), all SUMO cars.
- Accept a step if it improves the objective by more than 0.1 s/veh; at most 4 passes.

**Uses of the tuned FT:**
- It is G1's baseline and F1-2's "old" program.
- It replaces Webster in `saltlake_<site>.net.xml`. The Webster nets are kept as `saltlake_<site>_webster.net.xml`.

**Rationale:** a tuned fixed-time plan is the fair stand-in for the existing coordinated plan, and it makes the light gate harder, not easier.

## Amendment A3 / A4 (08/10, 10:06): F1-B registered, and a port bug that invalidates the two G1 attempts

**F1-B (user decision 08/10: "F1-B: đèn học 4 pha cho Salt Lake").** A light that observes every green: `CITY_lightw.LightRLW`.
- Inputs: halting and vehicle counts on each of the four greens, the current green one-hot, and spent time (13 inputs).
- Unchanged: keep / advance, the halting reward, DT_L 5, MIN_G 5, the Q7 DQN (13 → 64 → 64 → 2).
- Trainer `CITY_sl_train_lightw.py`, runner `CITY_sl_runw.py` (spec `RLW:`).
- 240 episodes, seeds 11 and 12, TRAIN days.

**Port bug (demonstrated).** The F1-B smoke tripped `assert k <= 4` with k = 8.
- In the A1 programs, the yellow and all-red after a green whose links all continue into the next green repeated that green's state. That happens for EW protected left → EW all green, and for NS protected left → NS all green.
- `CITY_lightk.NetInfoK` counts any phase with G/g and no 'y' as a green. Each signal therefore had 8 "greens", including two 3-s and two 1-s pseudo-transitions that a keep / advance light can hold indefinitely.
- **Consequence:**
  - The G1 results of jobs 097 and 097r (C-202, C-203) test a light that could freeze a transition. They are an implementation artifact, not a valid test of the light recipe, and are relabelled as such.
  - The FT rows are unaffected as a fixed-time plan: the repeated states only lengthened those greens by 4 s.

**Fix (A4, in `CITY_sl_build.programs`):**
- A transition in which no link loses green is dropped, and its 4 s are added to the green. The fixed-time state sequence is then identical second by second.
- Kept transitions must have an all-red with no G/g.
- **KSL-3b:** NetInfoK finds exactly 4 greens per signal.
- The old nets are kept as `saltlake_<site>_v1.net.xml`.
- **KSL-5:** FT on the first 3 DEV days with the new net reproduces the v1 FT rows (time loss, n, fuel identical).

**Gate, re-run on the corrected programs** (job 099, both sites, same DEV days; FT is the tuned plan, unchanged). The two invalid attempts are kept in the α chain (conservative):

| Attempt | Design | α |
|---|---|---|
| 3 | RLK, the grid4 recipe, 120 episodes | 0.0125 |
| 4 | RLW, the F1-B wide light, 240 episodes | 0.00625 |

A site passes if either attempt passes at its level. Stages F1-2 onward follow as registered, with the passing light.

## Amendment A5 (08/10, 19:13): F1-3 / F1-4 at 400S & 200W (M1-SL shown, C-212)

**Seen:** G1 (RLW passes at 400S), M1-SL (−9.40 / −10.24%). No TSI or M2 run on Salt Lake.

**Code (no file edited):**
- `CITY_n2k4.py`: a copy of CITY_n2k generalised to K ≤ 4 (r one-hot of length 4, K one-hot, positions 0..3, the runner's net, any day ids).
- `CITY_lightw.LightRLWQ`: the TSI demand adapter on all four greens' halting inputs.
- `CITY_sl_runw4.py`: replaces CITY_n2k's functions by N2K4's before the evaluator imports them; spec `RLWQ:`; `SL_Q` sets the published quantile, since `CITY_m4s_tsi_eval` fixes 0.5.

**Calibration** (spider TSI chain, with K = 4; RLW light seed 11 = `gateW/lights/RLW_400sX200w_11.pt`):
1. Open-loop forecast-K table from the RLW light's traces with all SUMO cars on the first 8 TRAIN days (`FK.fit_k`).
2. Closed-loop table: the development fleet drives on the open-loop table (q 0.5) on the same 8 days; traces → `fit_k`.
   - The development fleet is the rule fleet GLOSAL:0.3, as in the spider TSI chain. The deployed fleets s13 / s113 are not used for calibration.
3. N2K4 feature logs (closed-loop table, q 0.1, development fleet), the same 8 days; fit; **KS-1** parity; **KS-2** provider counters.

**Tuning** (TUNE days 121–124, development fleet; HBEFA4 and PHEMlight5 via CITY_w9_run em:):
- Arms: R (no SPaT) and the grid (A, B) ∈ {(1,0), (1.5,0), (2,0), (1,0.25), (1.5,0.25), (2,0.25), (1,0.5), (1.5,0.5), (2,0.5)} × q ∈ {0.1, 0.5}.
- **TU:** rule R15-U on this grid. The state-dependent quantile is not available on the K path and is not used.
- **TG:** the default (1, 0.25, 0.1), fixed.

**M2-SL** (CONF days, deployed fleets):
- OFF (humans) under RLW;
- R, the fleet without SPaT (identical to OFF by construction; reported);
- HARM, the fleet given the **old FT program** as SPaT while RLW runs: a forecast-K table fitted on FT traces, q 0.5.
- Descriptive: HARM − OFF.

**Confirmation:**
- CONF days: 20 weekdays, every third weekday from 5 Sep 2023, generated now after the non-existence check.
- Fleets s13 / s113; RLW seed 11 (the passing light; seed 12 reported descriptively if time allows).
- Arms R, TG, TU × HBEFA4 / PHEMlight5.
- **D-F1a:** TG meets every M3 limit against R and saves agent fuel under both models (α 0.05).
- **D-F1b (descriptive):** TU − TG.
