# Resume bullet bank: TSI research project (15/10/2026)

Pick 3–6 bullets per job description and copy the JD's keywords into the bullet you choose. Every number was checked against the paper,
the reports or the ledger. Notes for an honest interview:
- Say "SUMO simulation".
- Put HBEFA4 next to fuel numbers.
- Do not write "first" or "novel"; "unreported" means it was searched for and not found.
- `[...]` = fill in yourself.

**Header (choose one):**
- Undergraduate Researcher, Rider University (mentor: Dr. Jay Zhengping Luo) | `[dates]`
- Independent Research: AI Traffic Signals × Eco-Driving Fleets | Rider University | `[dates]`

---

## 1. ML / AI research intern

- Identified an unreported failure mode between two AI systems: eco-driving cars that glide on traffic-signal timing advice drop out of the stop-thresholded inputs of RL traffic signals, so the signal holds its greens and the timing forecast defeats itself.
- Isolated the root cause with a controlled ablation of 10 RL observation and reward designs, trained by an identical recipe; only the inputs that count stopped vehicles produced the harm.
- Showed the vulnerable design is the default state representation of two widely used open-source RL traffic benchmarks (sumo-rl, RESCO), where the effect cost AI-driven cars 2.6–16 s per vehicle.
- Designed TSI-G, a retraining-free "human-twin" sensing layer that presents each AI car to a frozen signal policy as the human driver it replaces; it repaired 3 of 4 frozen policy families and removed 97% of the harm on the fourth.
- Fixed a distribution shift between two frozen learned models by changing only their interfaces (inputs and published forecasts), with no gradient update to either model.
- Validated findings under a second, field-calibrated driver model; the mechanism persisted for 3 of 4 policy families in a pre-registered test.
- Benchmarked against task ports of two 2026 methods (DC-Ada, FoRL) and against model retraining.
- Wrote a 40-page manuscript; research poster accepted at CCSC `[region, year]`.

## 2. Reinforcement learning / multi-agent systems

- Trained two interacting learned populations in SUMO, double-DQN keep-or-switch traffic-signal controllers and PPO residual eco-driving fleets, and studied how upgrading one silently breaks the other.
- Diagnosed a performative feedback loop between agents: publishing a forecast changed the fleet's behaviour, which changed the signal's observations, which invalidated the forecast; publication error rose from 1.70 to 3.02 s.
- Designed a two-sided interface (TSI) that restores a frozen PPO fleet's fuel benefit (−3.85%, 95% CI 3.26–4.43, HBEFA4) within a +0.5 s/veh delay margin, without retraining either policy.
- Showed that interface calibration beats retraining the fleet by 1.5–2.6 percentage points of fuel, and that retraining with the interface in force beats retraining alone.
- Re-implemented the sumo-rl and RESCO (IDQN/IPPO, MPLight, wave) state and reward definitions and trained 25+ DQN signal controllers per world.
- Measured per-decision counterfactual credit by re-simulating from identical prefixes; found a signal-to-noise ratio of about 0.2, showing per-decision credit is unlearnable here.
- Ported FoRL (forecast-conditioned RL) and diagnosed its policy collapse to minimum-length greens (a reward-scale mismatch of 59×); corrected and re-tested it.
- Built multi-green observation and forecasting variants for 2- to 4-phase intersections (spider network, Salt Lake City corridors).

## 3. Autonomous vehicles / connected vehicles / ITS / transportation

- Studied the compatibility of connected eco-driving (GLOSA-style) fleets with learned adaptive traffic signals in SUMO, across 4 networks and the full Midtown Manhattan OpenStreetMap network (567 signals, 206 km of road).
- Transferred grid-trained signals and fleets, without retraining, to Midtown Manhattan: −21% delay, −38% stopped time and −11% fuel versus SUMO actuated control over 100 paired runs.
- Diagnosed a citywide gridlock by tracing removed vehicles to static multi-phase junctions; fixed it by keeping 56 junctions on actuated programs.
- Built a quantile SPaT (signal phase and timing) predictor that publishes a calibrated lower quantile, in the direction of SAE J2735's minEndTime convention. It kept its 10% quantile calibration on unseen days of real Hamburg adaptive-signal logs (3.4M s, 22 signal groups) and beat last-cycle and per-signal baselines.
- Analysed 82,392 SAE J2735 SPaT messages from the Tampa CV pilot: yellow ends exact in 99.9%, greens ending before the announced minimum in ~12%.
- Calibrated a car-following model (IDM) jointly to NGSIM car following and stop approaches, and showed that SUMO's default Krauss drivers inflate eco-driving fuel savings from ~1% to ~9%.
- Ran the pipeline on recorded 2023 demand for two Salt Lake City corridors (RESCO counts) with 4-phase protected-left programs.
- Tested robustness to V2X message loss (20–50%), 1-s latency, 80% detection and 1 m/s speed noise.

## 4. Data science / statistics / experimentation (A/B testing)

- Ran 20+ pre-registered experiment waves, each with a written protocol (arms, panels, decision rule, significance level) fixed before any code ran, and reported every failure.
- Used a crossed (pigeonhole) bootstrap over model × fleet × traffic seeds (B = 2,000) for one-sided superiority and non-inferiority tests on paired designs.
- Controlled the family-wise error over repeated attempts with Bonferroni chains (bound 0.075), and kept "not shown" separate from "no effect".
- Used difference-in-differences designs to separate a mechanism from confounds, e.g. the threshold family's harm minus a threshold-free control's.
- Ran fresh-data confirmation panels (5 signals × 4 fleets × 20 seeds; 4,000 episodes in one wave) generated only after a non-existence check, so no seed was ever used both to tune and to confirm.
- Found an emission-model reversal (+1.76% vs −2.6% fuel) and traced it to re-acceleration after glides with a fuel decomposition by driving mode.
- Ran a post-hoc cross-network analysis showing that harm scales with the change in green durations, not with traffic improvement, and labelled it descriptive.
- Re-audited published claims against raw results and found and fixed 6 false statements and 3 misleading omissions in a public poster.

## 5. Software engineering (Python)

- Built a simulation and evaluation platform in Python (PyTorch, NumPy, libsumo/SUMO, sumolib), using composable runtime wrappers that change the world, network or sensing without editing any evaluator.
- Wrote deterministic, resumable job pipelines (bash/xargs queues, 6–10 parallel lanes, disk guards, completeness checks) that ran thousands of simulation episodes.
- Implemented self-checks that fail loudly: offline–online feature parity (0 mismatches over 10k+ rows), bit-identical identity runs, and exactness checks against recorded phase traces.
- Re-implemented two open-source libraries' observation pipelines and verified them against an independent recomputation (0 mismatches over 1,920 checks per family).
- Maintained full provenance: source hashes on every result row, freeze records, and a ~250-entry research ledger linking each claim to its run.
- Used git sparse-checkout to keep a multi-GB research repo working on a laptop.

## 6. ML infrastructure / research engineering / MLOps

- Engineered reproducibility end to end: fixed seeds, PYTHONHASHSEED and OMP_NUM_THREADS pinning (set-order hashing had moved results by up to 1.45 s/veh), and bit-identical reruns.
- Made model calibration cheap: 52 simulated episodes per deployed controller and a ~30-s CPU fit of a 64-64 MLP quantile forecaster.
- Ran a full replication (train 5 signals and 4 fleets, calibrate, 1,600-episode confirmation) in 66 minutes, and a 2,220-episode tuning and confirmation in 43 minutes, on one laptop.
- Built smoke-test-first workflows: every job runs end to end on tiny inputs through its report before the full launch.
- Added a "human twin" tracker computing per-second counterfactual trajectories for hundreds of vehicles alongside the live simulation.
- Made long runs survive hangs and laptop sleep with resumable trainers, sleep prevention and per-run completeness checks.

## 7. Performance / debugging / systems

- Traced repeated SIGKILLs of a model fit to an 80 GB memory peak from a dense 511-wide one-hot encoding, by measuring the step alone. Replaced it with an equivalent column-lookup layer, verified bit-identical.
- Found a 1-s timing-convention error affecting 100% of 39,522 forecasts through a trace check designed so it could fail.
- Audited a comparator implementation: found mismatched evaluation horizons and wrong parameter initialization, withdrew the invalid results, and re-ran a corrected port.
- Diagnosed lane-change deadlocks created by speed commands (0–17 teleports per run) and removed them with a lane-aware release rule.
- Debugged a Manhattan-scale gridlock by logging every teleported vehicle's lane and wait time and tracing the queues back to their source junctions.

## 8. Simulation, modeling and operations research

- Modeled the signal–fleet feedback loop as a threshold queue and derived when a sensing adapter is needed; the model's registered prediction (max-pressure signals need no adapter) held in simulation.
- Wrote computer-verified proofs for small exactly solved models: a one-car two-sided game, a threshold queue, and the error bound of registered attempt chains.
- Built and calibrated microscopic traffic simulations: synthetic grids, random planar networks, an OSM city map, and recorded corridor demand.
- Calibrated driver models on NGSIM trajectories with Nelder–Mead (spacing NRMSE 0.210 vs 0.285 for Krauss).
- Designed counterfactual "human-twin" trajectories with one site parameter, calibrated so that twins reproduce human halting time (ratio 0.983).

## 9. Data engineering / geospatial / public datasets

- Converted the full OpenStreetMap extract of Midtown Manhattan (1,942 edges, 206 km, 567 signals) into a SUMO network, plus an actuated twin and random demand.
- Ingested and cleaned five public field datasets:
  - Vehicle Energy Dataset (196 cars, 7.6M s of OBD-II data);
  - NGSIM Peachtree trajectories;
  - Tampa CV-pilot SPaT;
  - Hamburg open traffic-light states and detectors;
  - RESCO Salt Lake City 2023 counts.
- Derived fuel from mass air flow and fuel trims for 196 vehicles, and bounded the deceleration fuel cut-off with two estimates.
- Built a matcher that aligns hundreds of thousands of served forecasts per network with realized signal phases. It passed an exactness check (1.0000 under fixed time).

## 10. Quantitative research / research analyst

- Turned a vague concern ("upgrades may break AI fleets") into falsifiable hypotheses with registered decision rules, and confirmed or refuted each on fresh data.
- Separated mechanism from coincidence by controlled ablation and by a prediction registered before the run (a max-pressure signal needs no repair).
- Quantified the work's main limitation (against field-matched drivers the fleet's own fuel benefit is about 1%) and stated it in the paper's abstract.
- Reported uncertainty everywhere with 95% bootstrap intervals and one-sided bounds, never a bare point estimate.

## 11. Energy / sustainability / emissions

- Evaluated eco-driving fuel savings under two emission models (HBEFA4, PHEMlight5) and validated both against measured fuel. HBEFA4 overprices idling by about 2.1×; PHEMlight5 matched.
- Designed a forecast-publication rule (low quantile) that keeps eco-driving fuel savings positive under both emission models (−4.6% HBEFA4 / −2.2% PHEMlight5).
- Measured citywide fuel −11% and stopped time −38% on a Manhattan-scale simulation versus actuated signals.

## 12. Visualization / frontend / technical media

- Built an interactive browser demo (HTML/JavaScript canvas) that animates a 567-signal Manhattan simulation with live delay and stopped-time counters and side-by-side signal designs.
- Produced deterministic 60-fps showcase videos by frame-stitching headless-browser captures (Playwright, ffmpeg), with on-screen highlights of key numbers.
- Generated publication figures (matplotlib) and a 48-inch conference poster built programmatically (python-pptx, two-pass LibreOffice layout).

## 13. Writing / communication / teaching

- Wrote and restructured a 40-page research manuscript: cut the main text by 40%, consolidated all limitations into one section, and kept every result in the appendices.
- Presented the research as a conference poster (CCSC `[region, year]`) and a public demo; wrote plain-language summaries for non-specialists.
- Self-audited public material and issued corrections, including the poster's fuel claims labelled by emission model.

## 14. Initiative / integrity (for any JD)

- Led an independent research project end to end: question, design, training, statistics, field validation, writing and presentation.
- Pre-registered every experiment and reported every negative result: one-lane network failures, the driver-model dependence, and a recorded-demand site where the fuel loss did not occur.
- Built audit trails that caught and corrected errors before submission: invalid comparator ports, a timing-convention error, overstated claims.

---

**Gợi ý ghép theo loại JD:**

| Loại JD | Lấy từ các mục |
|---|---|
| ML/AI research | 1, 2, 4 |
| RL engineer | 2, 6, 7 |
| Autonomous vehicles / ITS | 3, 8, 11 |
| Data scientist | 4, 9, 10 |
| SWE / backend | 5, 7, 6 |
| Research engineer / MLOps | 6, 5, 7 |
| Quant / analyst | 10, 4 |
| Sustainability / energy | 11, 3 |
| Frontend / visualization | 12, 5 |
| Mọi JD | 1 bullet ở mục 14 |
