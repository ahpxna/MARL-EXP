# PROTOCOL MT — does the best grid4 configuration still work on the full Midtown Manhattan map? (written 10/10/2026 22:55 EDT, before any Midtown run of these arms)

User 10/10 22:4x: "cho chạy trên map nyc mahattan thật lúc trc mà bị kẹt đi, map gốc ko bị cắt" and "lấy cái config tối ưu nhất này cho chạy trên map đó thì còn tối ưu ko?"

## What exists before this run
- No measured Midtown experiment exists.
- On 03/10 three live viewers ran the Q7 grid4 checkpoints on Midtown (one seed, about 8 minutes, demo only):
  - ACT + L-ACT: 24.9 km/h.
  - RL-H + L-ACT: 9.0 km/h, starting to jam.
  - RL-C50 + L-ACT: 22.8 km/h.
- An earlier viewer, FT with 100 % human drivers at 6 000 veh/h, gridlocked within the hour.

## Setup
- **Network:** `research/city_sim/net/midtown.net.xml`, the full OSM extract (40.7415–40.7690 N, 73.9541–73.9982 W; 248 signals). Its static programs were guessed by netconvert; they are not NYC signal plans. `midtown_actuated.net.xml` is used for ACT.
- **Demand:** `midtown_p075_s{seed}.rou.xml` (randomTrips, period 0.75 s = 4 800 veh/h for 1 h, fringe-factor 5, min-distance 400 m). Seed 0 exists. Seeds 1 and 2 are generated with the same command and `--seed 1` / `--seed 2`.
- **Wrapper:** `scripts/DEMO_midtown.py` re-points `Q7.NET_S`, `Q7.NET_A` and `Q7.ROU`. Nothing is retrained.
- **Forecast transfer, the only change:**
  - a Midtown light gets the average grid4 identity in the N2 model;
  - the yellow-branch c2 table is rebuilt on the Midtown programs with grid4's pooled green-duration samples.
- **Arms:** the same evaluator commands as the grid4 demo (`demo/data/*.json`, seed 1400). The horizon is 5 400 s, with demand stopping at 3 600 s.
  - **FT:** `CITY_eval6_v11.py --light FT --fleet L-ACT:0 --guard always`. Every agent is released to SUMO, so all cars are human-driven.
  - **ACT:** the same command with `--light ACT`. This is the netconvert actuated program.
  - **BEST:** `CITY_eval_n4.py --n4 0.1:hyb:<w19 prov_rlh59_cl.json>:<w19 n2_k59.pt> --light RL-H:59 --fleet PL:<L11_s1413_fleet.pt>`. These are the B2D light, the PPO fleet at ρ 0.5 and the hybrid forecast.
  - **LIGHT-ONLY:** the RL-H:59 light with every agent released (`--guard always`).
- **Metrics** (tripinfo, all vehicles): mean time loss, fuel, unfinished vehicles and teleports. Teleports are SUMO's jam detector: a car stuck for 300 s is removed.

## Questions (fixed now; descriptive, three traffic seeds, no inferential claim)
- **MT-1:** does BEST beat FT on Midtown in time loss and in fuel?
- **MT-2:** does BEST keep its grid4 ranking against ACT and LIGHT-ONLY?
- **MT-3, the jam check:** teleports and unfinished vehicles per arm.

A "no" on any question is reported as found. The grid4 result is not changed by it. Midtown is out of the training distribution for every checkpoint.

## Order
1. Smoke: 600 s, seed 0, FT and BEST. Check the identity counter, the hybrid counter, teleports and runtime.
2. Full: 5 400 s, seeds 0–2, four arms.
3. Demo recording: `DEMO_record.py`, FT and BEST, seed 0, for the page.

## Amendment MT-A1 (10/10 23:0x, after the smoke, before any full run)
Smoke (600 s, seed 0, `midtown_transfer_20261010/smoke/`) with the learned light on every NetInfo light:

| Arm | TL (s) | Halt | Teleports |
|---|---|---|---|
| FT | 156.4 | 149 | 0 |
| ACT | 92.0 | 45 | 3 |
| LIGHT | 95.0 | 31 | 7 |
| BEST | 104.7 | 27 | 12 |

The teleport log (`tele_*.json`) puts every RL-caused teleport at a three-green light:
- the three greens are the avenue, a protected left, and the cross street;
- NetInfo's first two greens both serve the avenue, so the light never observes the cross street and starves it;
- the three ACT teleports are at unsignalised OSM junctions.

**Change:** `DEMO_midtown.py` keeps only the two-green lights under the learned controller (`MT_TWO_GREEN=1`, 224 of 248). The 10 three-green and 14 one-green lights keep their static program, and the forecast is 'unavailable' there. FT and ACT are unaffected.

The unadapted smoke is kept as the record that the checkpoint does not transfer verbatim.

Re-smoke (`smoke_a1/`):

| Arm | TL (s) | Halt | Fuel | Teleports |
|---|---|---|---|---|
| FT | 156.4 | 145 | 184.0 kg | 0 |
| LIGHT | 74.2 | 27 | 174.2 kg | 0 |
| BEST | 78.4 | 20 | 170.5 kg | 0 |

For BEST, the forecast answered 72 924 queries. 25 504 of them came from the yellow branch. The N2 model ran 25 008 feature evaluations, all with the average identity, because no Midtown light has a grid4 identity.

## Results (10/10 23:03; `midtown_transfer_20261010/full/MT_{FT,ACT,LIGHT,BEST}.json`, all COMPLETE, 0 unfinished in LIGHT)
Each cell gives seeds 0 / 1 / 2.

| Arm | Time loss (s) | Mean | Fuel (g/trip) | Teleports |
|---|---|---|---|---|
| FT | 283.7 / 285.8 / 299.7 | 289.7 | 316.5 / 317.7 / 326.5 | 0 / 0 / 1 |
| ACT | 223.7 / 132.4 / 117.4 | 157.8 | 292.1 / 247.8 / 242.4 | 121 / 28 / 2 |
| LIGHT | 98.4 / 97.0 / 99.8 | 98.4 | 225.3 / 225.1 / 228.2 | 7 / 9 / 8 |
| BEST | 99.4 / 148.6 / 103.4 | 117.1 | 218.1 / 243.0 / 222.8 | 5 / 89 / 14 |

- **MT-1 holds.** BEST beats FT on every seed: time loss −60 % and fuel −29 % (3-seed means).
- **MT-2 fails in part.**
  - BEST beats ACT.
  - BEST does **not** beat LIGHT. LIGHT is better in mean time loss (98.4 vs 117.1) and equal in fuel (226 vs 228 g).
  - On seed 0, BEST has the lowest fuel (218 vs 225 g) and equal time loss.
  - The grid4 ranking (lights + fleet + forecast first) does not carry over to Midtown as a whole.
- **MT-3, jam check.** `diag/tele_{best,light}_s1.json` traces the jams:
  - BEST seed 1: all 89 teleports are human vehicles, and none is an agent. They cluster at the unsignalised / priority OSM junctions 561042199, 100522479 and 3977886253 and the signals next to them (561042198, 42446488). ACT jammed at the same junctions on seed 0.
  - LIGHT seed 1: its 9 teleports sit at 3977886253.
  - The jams are a network hotspot that the fleet's changed flow pattern triggers on seed 1. It is not a fleet-vehicle deadlock.
- **Demo:** `demo/data/mt_{today,best,light}.json` (seed 0, minutes 25–30). Each recording reproduces its full-run row exactly: FT 283.69, BEST 99.41, LIGHT 98.40.

## Amendment MT-A2 (10/10 23:1x, after the MT results, before any run with the new baseline)
The user asked whether "Today" is realistic. It is not. "Today" (FT) is netconvert's guessed plan for all 248 signals: a 90 s cycle, an even avenue / street split (42/42 or 39/39 s), and offset 0, so there is no coordination.

Manhattan practice, from secondary sources found by web search 10/10:
- signals are pre-timed;
- cycles are about 90 s, with 90–150 s reported in a West Side study;
- avenues get the larger share of green;
- the one-way avenues are coordinated for progression at about 25–30 mph, and Third Avenue was retimed to 15 mph in 2025.

**New baseline FT-NYC** (`scripts/MT_nyc_timing.py`, `nyc_timing/nyc.add.xml`), built with SUMO's own tools on TRAINING traffic seed 10 only:
- `tlsCycleAdaptation.py` (Webster, existing cycle) green ratios, rescaled so every cycle is exactly 90 s, minimum green 10 s;
- all original yellow and red durations and the phase structure are kept;
- `tlsCoordinator.py` green-wave offsets, taken modulo 90.

Checks: all 248 signals pass (same states, same non-green durations, 90 s cycles); 247 have a non-zero offset.

`MT_BASE=nyc` makes this plan the active program for every arm except ACT. Under a learned light it is the plan of the lights the AI does not control.

| Smoke (600 s, seed 0) | TL (s) | Halt |
|---|---|---|
| FT-NYC | 107.2 | 87 |
| FT (OSM plan) | 156.4 | 145 |
| BEST, NYC base | 76.9 | — |

FT-NYC is a much stronger baseline.

Full runs: `full_nyc/MTN_{FT,LIGHT,BEST}` on seeds 0–2. The demo recordings go to `demo/data/mtn_*.json`. The OSM-plan results above are kept, relabelled "netconvert default plan".

## MT-A2 result (23:15; `full_nyc/`)
Each cell gives seeds 0 / 1 / 2.

| Arm (NYC base) | Time loss (s) | Mean | Teleports |
|---|---|---|---|
| FT-NYC | 304.1 / 300.6 / 320.8 | 308.5 | 87 / 138 / 72 |
| LIGHT | 95.0 / 94.2 / 112.6 | 100.6 | 7 / 7 / 38 |
| BEST | 100.7 / 97.3 / 127.1 | 108.3 | 16 / 4 / 65 |

The NYC-style plan holds fewer cars stopped early in the run, but over the hour it is WORSE than netconvert's plan (308.5 vs 289.7) and it jams. The demand is random-OD (randomTrips), not avenue-dominated as in Manhattan, so the coordinated avenue progression it was tuned for does not match the flows.

Decision: the conservative baseline is the one with the lower delay, the netconvert plan (`MT_BASE=osm`). It stays "Today", and FT-NYC is reported as a sensitivity row. A realistic plan needs realistic demand (NYC counts / trip data; downloads need the user's permission).

## Amendment MT-A3 (10/10 23:1x): retraining on Midtown, recipe fixed before any training
User: "cho có 2 tab để chiếu cả 2 results của train trên cái cũ và train trên cái map thật ... có đang ít seed quá r bị local max ko?"

- **Base plan:** osm for training and test. Learned light control on two-green lights only (MT-A1).
- **Training traffic:** Midtown seeds 10–17 (same randomTrips command), in rotation. `Q7.TRAIN_SEEDS` is set by the wrapper.
- **Lights:**
  - `CITY_w19_train_light.py`, family B2D, k = 59–63, which are the same five DQN seeds as the grid lights RL-H_t59–63;
  - 120 episodes, the last checkpoint is the result;
  - output `retrain/lights/RL-H_t{k}.pt`, evaluated through `W19_LIGHTS=retrain/lights`.
- **Fleets:**
  - `CITY_fleet_train_v11_ppo.py --spat on`, seeds 1413 / 1513 / 1613 / 1713 (the grid fleets' seeds);
  - 200 episodes (grid: 400; time budget), under FT with exact SPaT, as on grid, in the staged-upgrade order;
  - the last checkpoint is the result;
  - output `retrain/fleets/MT{seed}_fleet.pt`.
- **Forecasts for the Midtown lights:** the W19 pipeline (job 104a steps 1–4: traces → open-loop fit → closed-loop c2 prep with the DEV fleet → N2 collect → N2 fit), on training traffic only.
- **Test:** traffic days 0–4 (seeds 3 and 4 generated now with the same command), never used in training or tuning. Arms:
  - FT;
  - LIGHT-grid t59–63 and BEST-grid (5 lights × 4 grid fleets): the zero-shot tab;
  - LIGHT-MT t59–63 and BEST-MT (5 Midtown lights × 4 Midtown fleets): the retrained tab.
- **Statistics:** every seed is reported, with no selection. Per-seed points plus means. Bootstrap over lights × fleets × days.
- **"Local max" check:** the spread across the five DQN seeds and four PPO seeds, and the learning curves of every seed.

## MT-A3 first light result and Amendment MT-A4 (11/10 01:1x, before any MT-A4 training)

**First test of a Midtown-retrained light (LIGHT-MT t59, day 0):**
- time loss 128.05 s and 207 teleports. The grid-trained t59, transferred, had 98.40 s and 7 teleports.
- Training reward rose from −0.09 to −0.028 on all five seeds, but training teleports did not fall: 9–21 per episode early, 11–18 late. The pattern is the same on every seed, so it is not a seed-count effect.
- Teleport log (`diag/tele_LM59_s0.json`): 164 of 207 teleports sit at approaches of lights the AI controls. 42 sit at the priority junction 3977886253. None is an agent.

**Reading (hypothesis, not isolated):** the light starves approaches until SUMO teleports the stuck cars away. That removes those cars from the −D/10 reward (only vehicles on served lanes count), so long starvation is not paid for. On the grid this could not happen: 0 teleports in training.

**MT-A4:** retrain the five lights (B2D k59–63, same seeds, 120 episodes, same traffic 10–17, last checkpoint) with SUMO teleports disabled in training only (`MT_TTT=-1`). Stuck cars then stay and keep costing reward. This is the only change. Test protocol unchanged (`--time-to-teleport 300`, days 0–4).
- Output: `retrain/lights_a4/`.
- The MT-A3 lights stay as the record of the failed recipe.
- Risk: whole-network gridlock in exploration episodes. Reported if seen: unfinished vehicles at episode end, and mean reward.

## Amendment MT-A5 (11/10 02:0x): shared + local lights with a gate, registered before any training
User 11/10: "cho policy riêng và cho thêm policy cục bộ của mỗi đèn ... cân nhắc input ... policy nào là quan trọng hơn", then "code tất cả đi, ... bỏ vào queue".

**Trainer:** `scripts/CITY_mt_train_light_moe.py` (networks in `scripts/CITY_mt_moe_net.py`). The recipe is the W19 loop, unchanged:
- B2D observation and reward, k = 59–63 with the grid lights' DQN seeds;
- 120 episodes on Midtown training traffic 10–17;
- ε from 1 to 0.05 over the first 60 % of episodes;
- 200 double-DQN Huber steps per episode, Adam 1e-3, soft target 0.01, replay 200 000;
- the last checkpoint is the result;
- teleports off in training (MT-A4), base plan osm, two-green lights only (MT-A1).

**Arms (all five seeds each):**

| Arm | Network | Index input |
|---|---|---|
| A4 | shared, from scratch (`CITY_w19_train_light.py`) | no |
| ft | shared, warm-started from the grid light t\<k\>, all weights trained | no |
| lg | grid shared FROZEN + g(s, i)·local_i(s) | yes |
| ln | grid shared frozen + local_i(s) (g = 1) | yes |
| lo | local_i(s) only, per-light 64-64, from scratch | yes |

- local_i is a per-light 32-unit MLP whose last layer starts at zero.
- The gate g = sigmoid(MLP([s, emb_i])) is learned by the same RL loss.
- Index input: `MT_LIGHT_INDEX=1` appends the light's position in sorted NetInfo ids to its observation, in training and evaluation.

**Self-check KMT5 (PASS, before queueing):** lg and ln with 0 training episodes, evaluated through the unchanged evaluator (600 s smoke, seed 0), reproduce the transferred grid light exactly: TL 74.16, halt 26.7, 0 teleports, the same as `smoke_a1` MT_LIGHT. This shows the index plumbing and the identity start are correct.

**Test:**
- days 0–4, teleports at 300 s as in every other test;
- `eval5/MTR_{A4,A5ft,A5lg,A5ln,A5lo}_t<k>`, compared with ACT, FT and LIGHT-grid (`MTR_LG_t*`) on the same days;
- no selection: every seed is reported;
- the lg gate's mean value per episode is logged.

**Fleet job:** the four Midtown fleets (`retrain/fleets/MT<seed>_fleet.pt`, MT-A3) on days 0–4, with the grid fleets on the same days:
- under FT with exact SPaT;
- with the grid lights t59–63 and the adapted forecast.

**Not queued:** a forecast refit for the Midtown-trained lights (the W19 forecast pipeline). Without it, BEST with Midtown lights cannot be run.

**Queue:** `research/queue_mt_20261011/`, runner `scripts/RUN_spool_mt_20261011.sh`. Jobs run one at a time, each with 5 lanes. The report is `scripts/MT_report.py` → `midtown_transfer_20261010/report_mt.txt`.

## Amendment MT-A6 (11/10 02:5x): SPaT forecasters fitted on Midtown, registered before any of these runs
**Purpose:** "lights + fleet" arms whose forecast is fitted on Midtown training traffic (10–17) instead of the grid forecast adapted to Midtown (average identity, pooled table).

**Pipeline:** `scripts/RUN_mt_forecast.sh`. It runs the W19 forecaster recipe of job 104a unchanged: traces σ 0.3 → open-loop table → closed-loop c2 prep with the DEV fleet (8 × 3600 s) → N2 logs → N2 fit (pinball, q 0.1 / 0.5).

**Three Midtown fixes:**
1. The table fit (`CITY_spat_forecast.fit`, also used by the prep and the N2 fit) skips signals outside NetInfo. Traces carry all 248 signals; the AI controls 224. The patch is in `DEMO_midtown.py` and is identical when every id is known. The open-loop step calls the module fit through `scripts/MT_spat_fit.py`.
2. `CITY_n2_fit.py` hard-codes files s0–5 / s6–7. A folder of symlinks maps s\<i\> → the real Midtown logs s\<10+i\>; the logs keep their true names.
3. `DEMO_midtown.py`'s c2 table keeps per-light samples for Midtown ids. A grid provenance has none, so earlier runs are unchanged.

**Checks:**
- **Smoke:** the whole pipeline ran on the grid light t59. Open-loop fit 224 lights; prep provenance 180 lights (one 300 s episode); N2 fitted.
- **KMT6:** the evaluator ran with that Midtown-fitted forecast, grid t59 + grid fleet s1413, 600 s smoke. `avg_identity` = 0 (every light has its own id), TL 75.48 (78.43 with the adapted grid forecast).

**Arms** (queue jobs 308–309), days 0–4:
- **MTR_BGF:** grid lights + grid fleets, forecast re-fitted on Midtown. No AI is retrained; this is the interface-only arm.
- **MTR_BMM_a4:** A4 lights + Midtown fleets, their own forecast.
- **MTR_BMM_ft:** A5-ft lights + Midtown fleets, their own forecast.

The gated / per-light arms (lg, ln, lo) cannot enter the closed-loop prep, which widens a Sequential net. Their forecasters would need a port of `CITY_m3_core.widen`; this is not done.

## Results so far (11/10 03:34; `scripts/MT_report.py`, test days 0–4, paired with the transferred grid light, same k and day, bootstrap over 25 pairs)

| Arm | TL (s) | Stop (s) | Fuel (g) | Teleports / run | TL − LIGHT-grid |
|---|---|---|---|---|---|
| LIGHT-grid (transferred) | 109.8 | 45.4 | 232.1 | 19.3 | — |
| MT-A3, teleports on in training | 128.4 | 68.0 | 240.6 | 153.2 | +18.60 [+4.96, +31.67] |
| A4, from scratch, teleports off | 111.3 | 50.6 | 232.3 | 57.2 | +1.56 [−11.03, +13.59] |
| A5-ft, fine-tuned from the grid light | 104.2 | 44.0 | 228.9 | 43.4 | −5.60 [−18.11, +6.22] |

A4 per seed: 123 / 103 / 109 / 123 / 98. A5-ft per seed: 111 / 98 / 94 / 101 / 118.

- **A4 vs A3:** turning teleports off in training removes the A3 failure, consistent with the starvation-until-teleport reading.
- **A5-ft:** the best mean so far, but the interval covers 0, so it is not an established improvement.
- **The lg gate** starts at about 0.85–0.89 and drifts to 0.66–0.81 by the last episode.

**Midtown fleets (MT-A3), training finished 03:33:**
- All four checkpoints were saved.
- Their own training reward fell over 200 episodes: mean of the first 10 episodes −2.28 to −2.30, last 10 −2.35 to −2.46.
- Teleports ran at 6–9 per episode (teleports on).
- Job 306 tests them against the grid fleets.

## MT-A5 results, all light arms (11/10 05:0x; days 0–4, 25 runs each, paired with LIGHT-grid on the same k and day)

| Arm | TL (s) | Unfinished / run | Teleports / run | TL − LIGHT-grid |
|---|---|---|---|---|
| ft, shared fine-tuned | 104.2 | 0.6 | 43.4 | −5.60 [−18.11, +6.22] |
| A4, shared from scratch | 111.3 | 7.5 | 57.2 | +1.56 [−11.03, +13.59] |
| ln, grid shared + local, no gate | 141.4 | 49.5 | 94.2 | +31.61 [+3.17, +80.05] |
| lg, grid shared + gated local | 163.5 | 75.8 | 143.6 | +53.78 [+15.29, +116.74] |
| lo, local only | 224.7 | 151.4 | 230.2 | +114.94 [+31.55, +205.85] |

Per seed:
- lg: 118 / 184 / 125 / 103 / 288.
- ln: 104 / 245 / 133 / 111 / 115.
- lo: 111 / 113 / 121 / 656 / 123.

**Training was alike for every arm.** The mean reward of the last 10 episodes was −0.030 to −0.048 in all arms, and training teleports were 0–4 per seed over 120 episodes (teleports off).

**Reading:**
- The per-light parts generalise badly to new traffic days. Some seeds gridlock (unfinished vehicles), and the gate learned by the RL loss (it ended at 0.65–0.78) does not switch them off where they are unreliable.
- The cause is consistent with too little data per light: about 230 sampled transitions per light per episode.
- The shared policy, fine-tuned or transferred, generalises best. No arm significantly beats the transferred grid light.
- The registered question "does a gated local policy help?" is answered **no** for this recipe. A count- or uncertainty-based gate (proposed alternatives 2 and 3) was not tested.

**Fleets (job 306, partial), day 0–4 means under FT:**

| Arm | TL (s) | Fuel (g) |
|---|---|---|
| FT alone | 293.8 | 322.7 |
| FT + grid fleet | 302.6 | 309.0 |
| FT + Midtown fleet | 320.7 | 321.9 |

The Midtown-trained fleet is worse than the grid fleet. This matches its falling training reward.

**Demo:** the Manhattan tab gains "AI signals: learned on the grid → fine-tuned on Manhattan" (cards −5 % / −3 % / −1 %, footnote: not established). The clip, under the fixed rule (day 3, t59), is a day it lost: 107 → 119 s.

## Planned MT-B (11/10 06:0x): realistic Midtown demand from NYC open data (written before any build or run)
**Data** (`research/city_sim/data/nyc_open_20261011/`, README with sha256):
- TLC yellow-cab trips, June 2026;
- the TLC taxi zones;
- NYC DOT Automated Traffic Volume Counts (57 340 rows on 113 segments inside the map).

**Step 1 (done, 06:0x).**
- `derived/edge_zone.json`: all 736 passenger edges of the net fall in 15 Manhattan taxi zones (point-in-polygon of each edge's midpoint).
- `derived/taxi_od_weekday_hourly.json`: weekday mean trips per hour for each zone pair inside those zones, over 22 weekdays. The peak is 1 530/h at 18:00; the trough is 51/h at 03:00.

**Plan (not yet built):**
1. **Demand classes:**
   - internal trips shaped by the taxi OD (zone → zone, the zone's edges chosen at random);
   - plus through-traffic between boundary edges.
   - The class shares and the overall scale are free parameters.
2. **Calibration:**
   - weekday 17:00–18:00 directional DOT counts, years 2017–2025, matched to the nearest SUMO edge in the counted direction;
   - split the segments 50/50 by a fixed hash;
   - fit the 2–3 scale parameters on one half by least squares on hourly volume;
   - validate on the other half (GEH statistic, share of segments with GEH < 5).
3. **Test:** the same arms as before on 5 new demand days drawn from the calibrated model.
   - FT, ACT, LIGHT-grid, ft and BEST-grid;
   - same evaluators, no retraining;
   - a sensitivity check, not a replacement for the random-trip panel.

**Caveats:**
- Taxi OD is not all-vehicle OD.
- Counts come from different years and are a sparse sample.
- Turning movements are not observed.
- The result will be "calibrated to NYC counts", not "NYC".

## Correction (11/10 06:0x): what "the full Midtown map" contains
`midtown.net.xml` is the network of the OSM extract named above. The road content is narrower than its bounding box:
- 736 edges, 702 OSM ways, about 74 km of road;
- the numbered streets present are West 29th–58th and East 34th–61st, not 23rd–66th;
- avenues 1st–10th, Broadway, Park, Madison and Lexington are present;
- the east-side approaches are absent: York Avenue, Sutton Place, FDR Drive and the Queensboro Bridge ramps.

Earlier wording that said "the full map, 23rd–66th Street" (the demo footers) is corrected to "about 29th–61st Street". No result changes: every arm ran on this same network.

For the realistic-demand plan (MT-B), 24 of 60 DOT count targets (weekday 17:00, 2017–2025) match an edge in the counted direction. Most of the others lie on roads that are not in the network.

## Amendment MT-C (11/10 06:2x): rerun on the full Midtown map, registered before the data exist
User: "tải lại OSM đầy đủ cho Midtown đi", then "tải xong thì chạy lại thí nghiệm trên map đầy đủ luôn".

**Data:**
- every `highway` way and every turn-restriction relation in the same bounding box, from Overpass;
- `data/osm_full_20261011/`: query, source server, sha256;
- built into `net/midtown_full.net.xml` with exactly the netconvert options of `midtown.net.xml`;
- the actuated twin uses exactly the options of `midtown_actuated.net.xml`.

**Wrapper:** `MT_NET=midtown_full` selects the net, its actuated twin and demand `midtown_full_p075_s<k>` (same randomTrips command, test days 0–4). The default stays `midtown`, so jobs running on the old map are unchanged. MT-A1 (AI on two-green lights only) applies as before.

**Script:** `scripts/RUN_mt_full.sh`:
1. actuated twin;
2. demand;
3. network facts (signals by number of greens);
4. 600 s smoke of FT and LIGHT t59;
5. full tests on days 0–4, 6 lanes;
6. report (`report_mt_full.txt`, `MT_report.py` with `MT_EVAL_DIR` / `MT_TAG_PREFIX=MTF`).

**Arms (no retraining):**
- FT and ACT;
- LIGHT-grid t59–63, transferred;
- the A5-ft lights, fine-tuned on the OLD map and transferred to the full map;
- BEST-grid: grid lights × grid fleets, adapted forecast, 100 runs.

**Questions:**
- **MT-C1:** do the earlier orderings hold on the full map? LIGHT-grid and BEST-grid vs ACT and FT.
- **MT-C2:** does A5-ft still beat LIGHT-grid on average?

Descriptive, with the same caveats as before (random-trip demand; SUMO-generated signal plans).

### MT-C data (11/10 06:32)
**Fetch:** attempt 2 on overpass-api.de, at 06:32. Attempt 1 failed on all three servers (overloaded).
- `midtown_full.osm.xml`: 6.2 MB, 9 982 ways, 25 048 nodes, 208 relations, sha256 7ae00c18…;
- netconvert: "Success". Warnings: 23 default widths, and 25 turn restrictions whose edges or direction could not be determined.

| Net | Edges | Road km | Signals | West streets | East streets | FDR | York |
|---|---|---|---|---|---|---|---|
| midtown (02/10) | 736 | 74.5 | 248 | 29–58 | 34–61 | no | no |
| midtown_full (11/10) | 1 942 | 206.3 | 567 | 19–62 | 23–74 | yes | yes |

`RUN_mt_full.sh` was launched at 06:32 (log `midtown_transfer_20261010/run_mt_full.log`).

## Amendment MT-D (11/10 06:4x): maximum green for the learned lights, registered after the first MT-C rows and before any capped run except one diagnostic
**First MT-C rows (full map, partial):**
- ACT 154–173 s/trip, 0–6 teleports;
- FT 681 s, 239 teleports;
- grid lights + grid fleets (t59): 418–487 s, 237–395 teleports;
- A5-ft t59: 562–569 s, more than 1 300 teleports;
- learned greens: p90 = 346 s, against 104–146 s on the old map.

The transferred light starves cross traffic on the larger network (as at the three-green junctions, MT-A1).

**Fix:** `MT_MAX_G=50` in `DEMO_midtown.py` forces a switch after 50 s of green.
- 50 s is the maxDur netconvert gives the actuated programs of this net (1 152 of 1 154 phases).
- It is also the corpus's existing compatible mode, RL-C50 (Q7).
- Chosen from the actuated program, not tuned on results.

**Smoke (600 s, day 0):** with the cap, green p90 = 53 s; TL 102.0 s, 1 teleport.

**Diagnostic:** one full-horizon run, t59 day 0, `diag_maxg/`.

**Arms** (`scripts/RUN_mt_full_cap.sh`, after MT-C):
- full map, days 0–4: LIGHT-grid-cap50 (`MTF_LGc_t<k>`) and BEST-grid-cap50 (`MTF_BGc_t<k>_s<f>`);
- old map, days 0–4: LIGHT-grid-cap50 (`MTR_LGc_t<k>`), to measure what the cap costs where the uncapped light did not gridlock.

**Questions:**
- **MT-D1:** with the cap, do the learned lights beat ACT on the full map?
- **MT-D2:** what does the cap cost on the old map, compared with MTR_LG?

### MT-D diagnostic result (11/10 06:4x): the cap does NOT fix the full-map gridlock; the MT-D full run is NOT launched

| t59, day 0, full map | TL (s) | Teleports | Green p90 (s) |
|---|---|---|---|
| Uncapped | 452.2 | 303 | 346 |
| Capped at 50 s | 495.5 | 316 | 53 |
| t60 uncapped (shorter greens) | 439.7 | 273 | 96 |

Long greens are not the cause. `scripts/RUN_mt_full_cap.sh` stays unrun.

**Teleport log** (`diag_maxg/tele_full_LG59_d0.json`, 303 events, the first at t = 732 s):
- Before t = 1 800 the jam starts at signals the AI does NOT control:
  - the 7-green signal on East 57th St;
  - the 6-green signal in the 1st Avenue Tunnel;
  - a priority junction on Madison Ave.
- It then spills back to AI lights on 2nd / 3rd / Park Ave.
- The largest single sink is a FIXED 4-green signal on 2nd Ave (50 teleports).

Totals by place:

| Place | Teleports |
|---|---|
| AI lights | 160 |
| Fixed 3- to 7-green signals | 98 |
| Internal lanes | 33 |
| Priority junctions | 12 |

FT itself gridlocks on this map (611–681 s); ACT does not (154–173 s).

## Amendment MT-E (11/10 06:5x): AI on the two-green signals, the city's actuated program on the rest (registered before its runs)
**Mode:** `MT_BASE=actrest`. The 56 signals the AI does not control run their programs from `midtown_full_actuated.net.xml`, written to `net/midtown_full_act_rest.add.xml`.
- All 56 have link indices identical to the static net (checked).
- Their active program is 'act'; every other signal stays on '0' (checked with libsumo).

This is the deployment a city would run: AI where its phase structure applies, the existing actuated controller elsewhere. The comparator is ACT on every signal.

**Checks:**
- Smoke 600 s, t59: TL 82.1 s, 0 teleports.
- Full-horizon diagnostic: t59, day 0, `diag_maxg/actrest_full_d0.log`.

**If it does not gridlock**, run on days 0–4:
- LIGHT-grid t59–63 (`MTF_LGar_t<k>`);
- grid lights + grid fleets (`MTF_BGar_t<k>_s<f>`).

**Question MT-E1:** AI on the two-green signals + actuated on the rest, against actuated everywhere.

### MT-E diagnostic (11/10 06:52): no gridlock
t59, day 0, `MT_BASE=actrest`: TL 125.97 s, fuel 298.5 g, 20 teleports, green p90 296 s.

| Day 0 reference | TL (s) | Fuel (g) | Teleports |
|---|---|---|---|
| ACT everywhere | 163.26 | 329.1 | 0 |
| AI + static rest | 452.17 | — | 303 |
| FT | 680.93 | — | — |

**Decision:** run MT-E on days 0–4 (`scripts/RUN_mt_full_actrest.sh`) when the MT-C run finishes, so the two never compete. Job 308 resumes after MT-E.

### MT-C / MT-E results on the full map (11/10 07:23; days 0–4; `eval_full/`, `report_mt_full.txt`)

| Arm | Runs | TL (s) | Stop (s) | Fuel (g) | Teleports / run | Unfinished / run |
|---|---|---|---|---|---|---|
| FT | 5 | 644.4 | 526.9 | 547.2 | 234.8 | 309.2 |
| ACT | 5 | 161.9 | 70.6 | 328.0 | 1.6 | 0.0 |
| LIGHT-grid + static rest (MT-C) | 25 | 420.5 | 331.5 | 432.0 | 283.8 | 293.0 |
| A5-ft + static rest | 25 | 448.0 | — | — | 513.8 | — |
| grid lights + grid fleets + static rest | 60 of 100 so far | 395.8 | — | 412.4 | 271 | — |
| **LIGHT-grid + actuated rest (MT-E)** | 25 | **129.1** | **52.6** | **300.6** | 5.4 | 0.5 |

- A5-ft + static rest: +27.53 [+2.53, +56.47] vs LIGHT-grid.
- MT-E per-model TL: 124 / 135 / 127 / 128 / 131.

**MT-E1 (paired with ACT on the same day, 25 model × day pairs, bootstrap 2 000):**
- TL −32.8 s [−36.6, −28.4] (−20.1 %), better in 24 of 25 runs;
- stop −18.0 s [−21.4, −14.0] (−25.1 %), better in 24 of 25;
- fuel −27.4 g [−29.3, −25.2] (−8.3 %), better in 25 of 25.

**Reading:**
- Transferred unchanged, the learned lights gridlock the full map. The jam starts at the 56 complex signals left on their static plans; FT gridlocks too.
- With the city's actuated programs on those 56, the learned lights on the 511 two-green signals beat actuated control everywhere, on every day and with every model but one run.
- **MT-E1 holds**, descriptive (5 days × 5 models).
- MT-C2: A5-ft does not beat LIGHT-grid on the full map.
- Still to run: grid lights + grid fleets under MT-E, then the demo update.

### MT-E final (11/10 07:51): grid lights + grid fleets with the city's actuated programs on the 56 complex signals, full map, days 0–4

| Arm | Runs | TL (s) | Stop (s) | Fuel (g) | Teleports / run | Unfinished / run |
|---|---|---|---|---|---|---|
| lights + fleets | 100 | 127.4 | 44.1 | 290.8 | 4.4 | 0.0 |

**Paired with ACT on the same day** (100 pairs):

| Metric | Difference | 95 % interval | Relative | Better in |
|---|---|---|---|---|
| TL | −34.5 s | [−36.2, −32.5] | −21.2 % | 98 / 100 |
| Stop | −26.5 s | [−28.0, −24.8] | −37.2 % | 98 / 100 |
| Fuel | −37.1 g | [−38.0, −36.1] | −11.3 % | 100 / 100 |

**Fleet effect** (lights + fleets − lights alone, same light model and day, 100 pairs):
- TL −1.7 s [−4.0, +0.6];
- fuel −9.7 g [−10.9, −8.6], about −3.2 %.

On the full map the two populations together beat either alone in fuel. The MT-C static-rest BEST arm (100 runs) gridlocked: 396.9 s, 264.9 teleports/run.

Job 308 resumed at 07:51 (`kill -CONT`).

**Demo clips:** day 0, the median ACT day (ACT TL by day 163.3 / 173.1 / 154.3 / 163.5 / 155.3), light t59, fleet s1413.

## Amendment MT-F (11/10 08:4x): job 308 ported to the full map, registered before its run
User: "port job 308 sang map đầy đủ luôn đi".

**Old-map job stopped:**
- Job 308 (old map) was stopped at 08:39 at the user's request. The spool marks it FAILED.
- Its outputs are kept, incl. `forecast_grid/cmodel/n2_k59.pt`. Jobs 309–310 moved to `queue_mt_20261011/hold/`.
- The A4 / ft forecasters are not ported, because those lights lost on the full map.

**MT-F:** Midtown-fitted SPaT forecasters for the grid lights t59–63 on the full map, in the MT-E setting (`MT_NET=midtown_full`, `MT_BASE=actrest`).
- Recipe: `RUN_mt_forecast.sh`, now map-aware through `MT_NET` / `MT_BASE`; defaults unchanged.
- Training traffic: full-map seeds 10–17, the same randomTrips command.
- Smoke: whole pipeline on t59, then the evaluator with that forecast. `avg_identity` = 0; TL 88.2 s (600 s smoke).
- Output: `retrain/forecast_full_grid/`.

**Test:** `MTF_BGFar_t<k>_s<f>`, grid lights × grid fleets with the re-fitted forecast, days 0–4, 100 runs. No AI is retrained; this is the interface-only arm.

**Question MT-F1:** paired with MTF_BGar (same light, fleet and day; adapted grid forecast), does the on-site forecast lower the AI cars' fuel and delay?

### MT-F incident and resume (11/10, 11:22)
- **What happened:** the N2 forecaster fits of t60, t61 and t62 were killed (SIGKILL, `Killed: 9`) at 10:32–10:43. Five light pipelines were running at once and swap was nearly full (6.6 of 7.2 GB at 11:20 on a 16 GB machine; one fit holds about 1.3 GB). The fit logs end after the wrapper's start lines, so no fit output was lost. xargs then aborted, so the MT-F tests never started. t59 (closed-loop prep) and t63 (collection) were still running in the first run.
- **Diagnostic:** the same t60 fit command, on the same inputs, is rerun alone into `retrain/forecast_full_grid/diag_fitkill/` with `/usr/bin/time -l`.
- **Resume:** `scripts/RUN_mt_full_forecast_resume.sh`.
  - Recipe, inputs and test are unchanged.
  - It is launched only after the first run exits.
  - Every finished step is skipped by its own file check.
  - The remaining fits run one at a time.
  - A t60 model from the diagnostic run is copied (not moved) into `cmodel/`.
  - Then come the 20 MTF_BGFar jobs and the report.
- **Deviation:** none in the method. Only the lane count of the fits (1 instead of 5) and the launch order change.

### MT-F resume, corrected cause (11/10, 11:45)
- **The cause is not concurrency.** Run alone, the t60 fit was killed again after 121 s at an **80 GB peak memory footprint** (`diag_fitkill/fit_t60.log`, `/usr/bin/time -l`). The t63 and t59 fits of the first run were killed the same way, so all five fits failed.
- **Why:** `CITY_n2_fit.py` stores a dense light one-hot in every row. On the full map:
  - each collection log covers T = 4 242 s and L = 511 lights, about 4.3 M rows per log;
  - with 523 input columns, the six training logs need about 54 GB, the two validation logs about 18 GB, plus the concatenation copy.
  - On the grid (16 lights) the same design needs well under 1 GB, which is why it never showed up before.
- **Fix:** `scripts/CITY_n2_fit_lowmem.py`, the same fit without the stored one-hot.
  - The same: rows, the 12 state features and their order, the one-hot as the last L inputs, `QNet`, the checkpoint format, seeds, initialisation, minibatch permutation, loss, Adam, early stopping, and the age-only comparison.
  - The change: the first layer computes `W[:, :12] x + W[:, 12 + j] + b` by a column lookup instead of a product with the one-hot. This uses the same parameters and gradients; only the float summation order differs.
  - At start, a self-check compares the lookup forward with `QNet` on the explicit one-hot.
  - The validation loss and predictions are computed in batches.
- **KMT7, the equivalence gate.** Both scripts are fitted on the grid W19 data of t59 (`scripts/CITY_n2_fit_lowmem_check.py`, output `diag_fitkill/kmt7/KMT7.json`). Criteria, fixed before the run:
  - C1 (informational): the original rerun reproduces the stored W19 model.
  - C2: the best validation pinball of the two fits differs by ≤ 0.5 %.
  - C3: on every validation row, the median |Δ prediction| is ≤ 0.1 s and the 99th percentile ≤ 1 s.
  - PASS = C2 and C3.
- **Resume:** `scripts/RUN_mt_full_forecast_resume.sh`.
  - It needs KMT7 PASS and all upstream outputs, which have been verified present for t59–t63.
  - It fits the five forecasters one at a time with the lowmem script, then runs the 20 MTF_BGFar tests unchanged and the report.
  - The killed fits' logs are kept (`cmodel/fit_t<k>.log`).
- **Deviation:** the implementation of the fit (an equivalent computation, checked by KMT7) and the fit order. The method is unchanged.

## Results MT-F (11/10 13:55; `eval_full/MTF_BGFar_*` and `MTF_BGar_*`, all COMPLETE; `report_mt_full.txt`)

**Fits.** All five forecasters were fitted with `CITY_n2_fit_lowmem.py`, after KMT7 PASS.
- KMT7 on grid t59: the lowmem model is bit-identical to the original's (validation pinball 2.70185 for the stored W19 model, the original rerun and the lowmem fit; prediction differences exactly 0 on 233 164 rows).
- At full-map scale the start-up self-check gave a max |diff| of 0 for all five fits.
- Validation pinball and median-quantile MAE, with the age-only table on the same rows in brackets:

| Light | Validation pinball | Median-quantile MAE | Age-only MAE |
|---|---|---|---|
| t59 | 42.31 | 49.0 s | 50.7 s |
| t60 | 5.61 | 8.3 s | 9.2 s |
| t61 | 11.43 | 10.6 s | 12.2 s |
| t62 | 6.69 | 11.0 s | 12.2 s |
| t63 | 12.55 | 15.6 s | 19.4 s |

**Provenance.**
- Every MTF_BGFar run recorded the re-fitted model; for example, t60 has sha 70ab3b4afa1d, and the MTF_BGar t60 run recorded the grid model, 58d0673fa5cf.
- The evaluator source and environment sha256 are identical in both arms, and the arguments differ only in the tag.
- Upstream data: training days 10–17 only; tests on days 0–4.

**MT-F1 (registered: all 100 pairs, MTF_BGFar − MTF_BGar, same light, fleet and day; percentile bootstrap, 2 000 draws, seed 0).** **No.** The re-fitted forecast is worse:

| Measure | Difference [95% interval] | Re-fitted better in |
|---|---|---|
| Delay, all cars | +40.5 s [+20.1, +62.5] | 29/100 |
| Delay, AI cars | +46.6 s [+25.4, +71.1] | 18/100 |
| Fuel, AI cars | +20.4 g [+10.0, +32.7] | 67/100 |
| Stuck cars removed | +34.8 per run [+13.2, +59.9] | — |

**Why: light t59 (post hoc, descriptive).**
- All 20 t59 pairs are worse: delay +200.9 s [+129.7, +272.8], AI-car fuel +116.9 g, 0/20 better.
- The t59 pipeline ran on congested traffic from the start:
  - light alone with human drivers (traces): 6–24 cars removed per run, against 0–4 for t60;
  - closed-loop prep: 238–424 removed per run, against 46–169 for t60;
  - collection with the prep forecast: delay 197–448 s and up to 292 removed, against about 130 s and 0–9 for t60.
- So the t59 forecaster learned from jammed traffic, which it had partly produced itself. Its timing errors are about 50 s, and its forecast makes the test traffic jam. This is a feedback loop in the recipe's own data collection, not an implementation error: the age-only table fitted on the same data is just as wrong (50.7 s).

**t60–t63 (post hoc, 80 pairs).**

| Measure | Difference [95% interval] | Re-fitted better in |
|---|---|---|
| Delay, all cars | +0.4 s [−1.6, +2.1] | 29/80 |
| Delay, AI cars | +2.1 s [−0.0, +4.0] | 18/80 |
| AI-car fuel | −3.8 g [−4.9, −2.8], about −1.3 % | 67/80 |
| All-car fuel | −2.9 g [−3.9, −2.0] | 71/80 |

- Re-fitting helps fuel slightly where its data collection was clean, with no gain in delay.

**Consequence.** The headline arm stays MTF_BGar (the grid forecast adapted without retraining), and nothing changes in the demo. This is a third instance of the pattern "learning on site from the deployed system's own traffic does not beat the transferred grid model" (MT-A3/A5 lights, Midtown fleets, now the forecast).
