# PROTOCOL FIELD: field-data checks F2, F3t, F4 (registered 08/10/2026, 04:58, before any analysis code ran)

**User request** (08/10):
- "tìm dữ liệu thực địa đi" (find field data).
- After the survey (`FIELD_DATA_SURVEY_20261008.md`): download all; F3 (the Hamburg API) waits until the machine is cleaned. F1 (Salt Lake) is registered separately in `research/city_sim/PROTOCOL_CITY_F1_SALTLAKE_20261008.md`.

**Data:** in `research/field_data/` (`README.md` there holds the sources, licences and sha256). Downloaded 08/10, 04:53–04:54.

**Before this protocol, only the following was seen** (data inventory, no analysis):
- VED column names; in one 200k-row chunk, Fuel Rate filled on 1.2% of rows and MAF on 82%.
- The VED inventory script was running.
- Peachtree: file list, the signal-change CSV header, and the Int_ID / Movement code counts.
- Tampa: message counts per RSU and the timing keys used. minEndTime appears in every message, maxEndTime in about 5% of the first 20,000 messages, likelyTime in none.
- No model was compared with any measurement.

**Scope.** These are descriptive validity checks of the model components used by the paper. None tests TSI in the field. Their results are reported whatever their direction. They do not change any registered decision of the paper. They are added as external-validity evidence or as limitations.

## F2: emission models against measured fuel (VED)

**Data:**
- VED ICE vehicles only (static table, Vehicle Type = ICE), Ann Arbor, Nov 2017 – Nov 2018.
- **Primary measurement:** the OBD Fuel Rate PID (L/h), on vehicles where the inventory shows it.
- **Secondary measurement:** MAF-derived fuel = MAF / 14.7 × (1 + (STFT + LTFT)/100) [g/s], with density 745 g/L.
  - This estimator cannot see deceleration fuel cut-off (air still flows while no fuel is injected), so it overstates fuel exactly on glides.
  - A masked variant sets fuel to 0 when a < −0.3 m/s², v > 15 km/h and absolute load < 20%. **The mask is a heuristic and is labelled as such.**
- If fewer than 5 ICE vehicles with ≥ 200 km of Fuel Rate exist, the primary analysis is reported as underpowered and the MAF variants become the main (labelled) result.

**Preprocessing:**
1. Per trip, sort by timestamp and resample to 1 Hz: speed is interpolated linearly, fuel is integrated.
2. Drop trips shorter than 2 km.
3. Drop seconds with gaps over 3 s; a gap ends the segment.

**Events**, defined deterministically on the 1 Hz speed:

| Event | Definition |
|---|---|
| approach | a local speed minimum v_min < 15 km/h, preceded within 30 s by v ≥ 30 km/h; window from −30 s to +30 s around the minimum |
| stop | approach with v_min < 2 km/h |
| roll (glide-through) | approach with 2 ≤ v_min < 15 km/h |
| cruise | 60-s windows with every speed in [30, 70] km/h and |a| < 0.5 m/s² |

Approach events are matched on entry speed (5 km/h bins) and duration.

**Models:**
- SUMO 1.27.1 `emissionsDrivingCycle` with `--compute-a` on each segment's 1 Hz speed, slope 0.
- Classes as in the paper: HBEFA4/PC_petrol_Euro-4 and PHEMlight5/PC_EU4_G.
- Sensitivity classes: HBEFA4/PC_petrol_Euro-6ab and PHEMlight5/PC_EU6_G.

**Per-vehicle scale:** k(v, m) = measured / model fuel on that vehicle's cruise windows. This removes engine size, weight and auxiliaries. Event comparisons use k × model.

**Statistics** (bootstrap clustered by vehicle, B = 2000, 95%):
- **S1.** The relative error (k·model − measured)/measured, per model and event class; median and mean.
- **S2.** The re-acceleration premium. R = mean fuel of roll events / mean fuel of stop events, on matched pairs, measured and per model. Report R_meas − R_model for each model, and which model is closer: the CI of |R_meas − R_H4| − |R_meas − R_P5| must exclude 0.
- **S3.** The W13 mechanism. In simulation, PHEMlight5 charged TSI's extra re-accelerations after glides more than HBEFA4 did, and that reversed the saving (W9-3, W13-1). The question is whether measured roll − stop fuel per event (matched) is nearer the HBEFA4 value or the PHEMlight5 value.

**Reading:**
- The model closer on S2 and S3 is the better guide for the paper's fuel claims on this event type.
- If PHEMlight5 is closer, the paper must weight its PHEMlight5 results higher. The quantile revision keeps a saving under PHEMlight5, so the claim survives.
- If HBEFA4 is closer, the original design's reversal is less alarming.

**Self-checks:**
- **KF2-1:** emissionsDrivingCycle on a constant-speed synthetic trace equals the per-second SUMO simulation value for the same class and speed (within 1%).
- **KF2-2:** the sum of 1 Hz resampled fuel equals the raw integral (within 1%).
- **KF2-3:** the event extraction is deterministic (same counts on two runs).

**Smoke:** one week of data, 5 vehicles.

## F3t: what a deployed SPaT broadcast says, and how early it is (Tampa)

**Data:**
- 82,392 SAE J2735 SPaT messages from the THEA RSUs thea5, thea22 and thea40, 2021-03-16, 00:00–00:59 (one night hour).
- Fields: eventState and timing (minEndTime; maxEndTime rarely; likelyTime never seen).

**Steps:**
1. **Units.** Determine whether minEndTime is a relative count (s or 0.1 s) or a J2735 TimeMark (0.1 s within the hour). Check whether, within a phase, consecutive messages decrease in step with the message time.
2. **Reconstruction.** Per (RSU, signalGroup), rebuild the state timeline and the realized remaining time to the next state change for each message.

**Statistics:**
- **T1.** The share of messages with realized ≥ announced minEndTime, i.e. the empirical quantile level of minEndTime, per state (red, green, yellow).
- **T2.** The distribution of realized − announced (median, 90th percentile).
- **T3.** The shares of messages carrying maxEndTime and likelyTime.

**Reading:**
- The paper's revision publishes the forecaster's 0.1 quantile. A deployed actuated signal that publishes minEndTime publishes a lower bound, the q → 0 extreme.
- T1 tells how conservative the field broadcast actually is.
- **Caveats:** this is one night hour on three RSUs; it says nothing about learned signals or peak traffic.

**Self-check KF3-1:** across the reconstructed fixed-length yellow intervals, the realized yellow durations are constant per signal group, within 0.2 s.

## F4: car-following near signals, Krauss vs IDM (NGSIM Peachtree, Atlanta)

**Data:**
- Peachtree St, two 15-min windows (12:45–13:00 and 16:00–16:15, 2006).
- 0.1-s trajectories with Preceding IDs; Int_ID 1–5, Movement 1 = through.
- Signal-change logs (begin of green, yellow and red for left and through, per approach) for 10th, 11th, 12th and 14th Street. The text says these frame numbers are on the trajectory Frame_ID clock; this is checked in KF4-1.

**Preprocessing:**
- Through movements only.
- Smooth positions with a symmetric exponential moving average (Thiemann et al. 2008, 1-s position window), then recompute speed and acceleration.

**Pairs:**
- Follower and leader on the same lane.
- Both present for at least 15 s.
- Gap < 80 m and no lane change in the window.
- Split 60/40 into train and test by a hash of the follower ID.

**Models** (open loop: the follower is simulated from the measured leader trajectory and the initial state):

| Model | Form | Defaults | Calibrated parameters |
|---|---|---|---|
| SUMO Krauss | deterministic core: v_safe = v_l + (g − v_l τ)/((v + v_l)/(2b) + τ); v' = min(v + a·dt, v_safe, v_max) | SUMO's (accel 2.6, decel 4.5, τ 1.0, minGap 2.5); dawdling σ is set to 0 for calibration and reported | a, b, τ, minGap |
| SUMO IDM | δ 4 | SUMO's (accel 2.6, decel 4.5, τ 1.0, minGap 2.5) | a, b, T, s0, v0 |

Calibration minimises the pooled spacing NRMSE on the train pairs (scipy, Nelder–Mead from the defaults plus 5 seeded starts).

**Statistics:**
- **C1.** Test spacing NRMSE for the four variants (default and calibrated, per model), with a bootstrap by follower.
- **C2.** First vehicles approaching a red with no leader within 80 m: deceleration-onset distance and peak deceleration. Compare with a single SUMO vehicle approaching the same red at the same entry speed under each model (defaults and calibrated).

**Reading:**
- If IDM fits better (lower test NRMSE, CI excluding 0), the paper states that its IDM results are the more realistic stress test.
- The next step would then be a separately registered re-run of the key confirmations with the calibrated model. That re-run is not part of this protocol.

**Self-checks:**
- **KF4-1:** red and green intervals from the signal log line up with observed stop and go: the first vehicle's stop at the stop line falls within a red.
- **KF4-2:** the model implementations reproduce SUMO. A single-lane SUMO run with a scripted leader gives the same follower trajectory as the Python implementation (max |Δx| < 0.5 m over 60 s) for both models with σ = 0.

## Order and reporting

1. Each analysis gets a smoke run first.
2. Results go to `research/field_data/results/` and to ledger rows.
3. A paper section, "Field data checks", follows only after all three have reported.

## Amendment A1 (08/10, 05:02; before any F4 analysis code ran)

**Seen since registration:** the F3t result only. F2 and F4 have not been analysed.

1. **F4 simulation.** Followers are simulated by SUMO itself, not by a Python reimplementation.
   - Setup: libsumo, step 0.1 s, σ = 0. Each pair runs on its own straight single-lane edge (3 km). The leader is scripted with speedMode 0 and `setSpeed` to its smoothed measured speed. The follower starts at its measured gap and speed. All pairs of a set run in one simulation.
   - **KF4-2 is replaced by KF4-2':** the scripted leader's simulated position follows its measured position with RMS < 0.5 m per pair. Pairs failing it are dropped and counted.
   - Reason: this removes any mismatch between an implementation and SUMO's actual Krauss / IDM.
2. **F4 pair filter, added.** Exclude windows in which the follower slows below 1 m/s while its gap exceeds 25 m. Such a stop is for the signal, not the leader. Windows are cut to at most 30 s.
3. **F4 C2.** Free approaches to a stop (no leader within 80 m, deceleration from ≥ 8 m/s to < 0.5 m/s), measured relative to the stop position. Statistics: deceleration-onset distance, time and peak deceleration. They are compared with one SUMO vehicle approaching a red at the same entry speed (defaults and calibrated). KF4-1 is kept as a data check of the signal logs.
4. **Calibration:** Nelder–Mead on bounded, transformed parameters, starting from SUMO's defaults plus 5 seeded random starts (seed 0–4), at most 150 evaluations each. Bounds:
   - Krauss: accel [0.5, 5], decel [1, 9], τ [0.3, 3], minGap [0.5, 5].
   - IDM: the same bounds plus maxSpeed v0 [8, 25] m/s.

## Amendment A2 (08/10, 05:09; before any F2 analysis code ran)

**Seen since A1:**
- The VED inventory: 264 ICE vehicles. The Fuel Rate PID exists on 1 vehicle only (a 6.7 L diesel, 13.5 km). MAF covers more than half the rows on 196 ICE vehicles (73,924 km); fuel trims are on 90% of the rows.
- A five-row test of `emissionsDrivingCycle`: at v = 0, a = 0, HBEFA4/PC_petrol_Euro-4 gives 493 mg/s and PHEMlight5/PC_EU4_G gives 238 mg/s. Both give 0 at 10.5 m/s and a = −1 m/s².
- F4 has been smoke-tested only. No F2 data has been compared with any model.

**Changes:**
1. **Measurement.** As registered, Fuel Rate is underpowered (one vehicle), so the MAF variants are the labelled main result.
   - The no-mask variant is an *upper* bound on glide fuel: deceleration fuel cut-off is invisible to MAF.
   - The masked variant is a *lower* bound.
   - A conclusion is called robust only if both variants agree.
2. **Model fuel by lookup table.**
   - One `emissionsDrivingCycle` run per class on a grid: v 0–40 m/s in steps of 0.1, and a −6 to +5 m/s² in steps of 0.05, with the acceleration supplied and slope 0.
   - Per-second model fuel is the bilinear interpolation in that table, with a from the central difference of the 1 Hz speed.
   - **KF2-1 (extended):** on 3 real 1 Hz trips, the table total equals a direct `emissionsDrivingCycle` run with the same accelerations, within 1%.
3. **Statistic S0, added: the idle-to-cruise ratio.** MAF is reliable at idle because fuel injection is active.
   - Idle seconds: v = 0 and |a| < 0.1 in runs of at least 5 s.
   - Measured ratio = mean idle fuel / mean fuel on the vehicle's cruise seconds. The model ratio uses the same seconds.
   - The ratio is scale-free. It tests which model prices waiting at a red correctly, which bears directly on the stop-vs-glide trade-off.
   - Statistics: median of per-vehicle log ratios (measured / model), with a vehicle bootstrap.

## Amendment A3, F3 (08/10, 09:46; before any Hamburg observation was downloaded beyond API discovery)

**User decision (08/10):** the Hamburg sample may now be downloaded. The disk has been cleaned to 16 GB free.

**Seen.** Discovery queries only:
- Endpoint: `https://tld.iot.hamburg.de/v1.1` (the priobike study's `.env`).
- One connection (Thing 353_12) has five datastreams: cycle_second, detector_car (percent), primary_signal, a second detector, signal_program.
- primary_signal codes, inferred from one sequence 4 → 3 → 2 → 1 of 1 s, 17 s and 3 s: 1 red, 2 amber, 3 green, 4 red-amber.
- About 4,050 state changes per day per connection. The earliest observation on or after 2026-09-01 is 2026-09-30 21:59 UTC.

**F3: a state-conditioned quantile forecaster on real adaptive signals.**

**Sample (deterministic):**
- Traffic-light systems (trafficLightsID) in ascending order. Take the first 8 that have at least 4 connections whose laneType contains "KFZ" (cars) and each a detector_car datastream with observations.
- For every such connection, download primary_signal and detector_car observations for 2026-10-01 00:00 to 2026-10-08 00:00 UTC (7 days).
- One request at a time, a 0.2-s pause, saved as gzip CSV under `research/field_data/hamburg/`.
- **Size cap 300 MB.** Stop and report if it is reached.

**Targets (1-Hz grid per connection):**
- During red (1): seconds to the next green (3).
- During green: seconds to the next amber or red.
- Seconds whose target is not observed (data gaps over 60 s) are censored and dropped.

**Features:**
- state one-hot;
- time in state;
- the last three completed green and red durations of the connection;
- detector occupancy, mean over the last 10 s and the last 60 s;
- hour of day (sin, cos) and weekday;
- system one-hot.

**Model.** The paper's forecaster architecture (`CITY_n2_fit.QNet`, MLP 64-64, quantiles 0.1 and 0.5, pinball loss, 40 epochs). Train on Oct 1–5, test on Oct 6–7. 10% of training seconds are used for early stopping.

**Baselines:**
- (B1) the same phase's last completed duration minus the elapsed time;
- (B2) per connection and state, the empirical 0.1 / 0.5 quantile of the remaining duration given the elapsed time (1-s bins, training days).

**Statistics** (test days; bootstrap clustered by connection-day, B 2000):
- **H1.** Coverage P(realized < predicted q) for q = 0.1 and 0.5, per state. Nominal: 0.10 and 0.50.
- **H2.** MAE of the 0.5 quantile, against B1 and B2.
- **H3.** The unsafe-early share on green: P(realized time to red < announced) for the published q0.1, compared with Tampa's minEndTime (F3t: about 12%).

**Reading.** If the forecaster trained on five days of field logs keeps its nominal coverage on held-out days, the fleet-side half of TSI (a calibrated low quantile) is implementable from field logs. A large miscalibration means the published quantile must be recalibrated online.

**Caveats.** The signals are actuated or adaptive but not learned. There is no closed loop: no fleet reacts to the forecast. Hamburg only.

## Amendment A3b (08/10, 09:57; after the downloader smoke, before the full download)

**Seen:** the smoke (1 system, 1 day). System 1005 was the first to qualify, with 18 connections. Response volume was 12.6 MB for one system-day, so 8 systems × 7 days would be about 560 MB, above the approved 300 MB.

**Change:**
- The first **4** qualifying systems.
- At most **6** connections each: the first 6 qualifying connections in API order.
- 7 days, unchanged.
- Expected volume about 120 MB; the cap of 300 MB is kept.

Nothing else changes.

## Amendment A4 (08/10, 19:10): F4b, joint calibration for W17

Registered in `research/city_sim/PROTOCOL_CITY_WAVE17_20261008.md`, section W17-0. It uses F4's pairs, smoothing and SUMO harness unchanged.
