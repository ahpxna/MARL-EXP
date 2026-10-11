# PROTOCOL W20: do the benchmark signal representations fall into the closed loop, and does human-twin sensing (TSI-G) repair them? (registered 09/10/2026, 01:24, before any W20 run on fresh traffic)

**User** (09/10, after W19 stage 1): "hoặc là giờ cố đấm ăn xôi với 1 phiên bản nâng cấp để generalize của tsi, có thể dùng cơ chế khác, research đi, còn ko phải bỏ luôn toàn bộ công sức bữa giờ" (either push a generalised TSI, possibly with another mechanism — research it — or throw the work away).

## Research basis (09/10, my own reading; no subagents)

**RESCO** (local copy `external_assets/RESCO/resco_benchmark`):
- `traffic_signal.Vehicle.observe`: a vehicle is `queued` from its first second below 0.1 m/s on a lane until it leaves the lane, and its `wait` grows only while queued.
- The learned agents' defaults (`config/agent.yaml`):
  - IDQN and IPPO: state `drq`, which holds approaching, wait, queued and speed per lane; reward `wait`.
  - MPLight: state `mplight` and reward `pressure`, both built from queued counts.
  - FMA2C: queued and max_wait.
  - The MaxPressure baseline also uses the `mplight` state.
  - Only `wave` (every vehicle) avoids the threshold.

**sumo-rl** (documentation, https://pypi.org/project/sumo-rl):
- Default observation: green one-hot, min-green flag, lane density, and lane queue (vehicles below 0.1 m/s / capacity).
- Default reward: diff-waiting-time.

**Reading:** the stop-threshold features that broke RL-H in W19 are the defaults of the two most used SUMO RL libraries.

**Collision search (limited; web):** found
- SPaT prediction for actuated signals;
- signal–vehicle co-training (retrains);
- cooperative perception at low CAV penetration (missing data);
- congestion attacks through spoofed CV data (malicious, not honest behaviour).

Nothing found on eco-driving vehicles becoming invisible to threshold-based learned controllers, or on a sensing correction for frozen controllers. The search was limited, so the verdict is "not found", not "novel".

## Seen before registration
- W19 stage 1 (C-226).
- Smoke runs of this job (scratch; slot 0; 15-episode smoke lights; one seed, 600 s). These are pipeline checks, not evidence.
  - The 3-episode smoke lights never switched, so no forecaster could be fitted for them.
  - KW20-1, KW20-2 and KW20-3 passed on smoke lights.
  - In the smoke, partly trained RDQ and RMP lights showed SV harm and a BIS repair (one seed).
- The twin calibration was smoke-tested on TRAIN seeds 0–1 (1,200 s and 300 s).
  - Pure-model twin halting time / human halting time: 1.13 at CREEP 0, 0.98 at CREEP 3, 0.88 at CREEP 5.
  - A first twin version (halt on reaching the tail, release 2 s × rank after green) overcounted human halting 2.2× in KW20-3. It was replaced by the car-following version below before any registered run (`legacy`-style copy in the scratchpad, `CITY_w20_bench_twin_v1.py`).
- W19 stages 2 and 3 are still running; their results are not seen.

## World, fleet, traffic

Unchanged from W19:
- grid4 Krauss;
- fleets FRESH3 s1413–s1713, frozen;
- fresh traffic 1400–1419;
- arms × HBEFA4 / PHEMlight5, KM13-1a/1b.

## Families (`scripts/CITY_w20_bench.py`; W19 trainer, RL-H recipe, DQN seed by slot, 120 episodes)

| Family | Lights | State (re-implemented) | Training reward | Uses the 0.1 m/s threshold |
|---|---|---|---|---|
| SRL | 84–88 | sumo-rl default: green one-hot, min-green flag, per lane density n/cap and queue h/cap, cap = length / 7.5 m (19) | diff-waiting-time (W_prev − W)/100, SUMO accumulated waiting time, between decisions | yes |
| RDQ | 89–93 | RESCO drq_norm (IDQN / IPPO): per lane [served by current green, approaching/28, wait/28, queued/28, avg-speed sum/20/28] (40) | RESCO wait_norm, clip(−wait/224, ±4) | yes |
| RMP | 94–98 | RESCO mplight (MPLight, MaxPressure): [green index, per-green pressure of queued in − queued out] (3) | RESCO pressure | yes |
| RWV | 99–103 | RESCO wave: per green vehicles/28, green one-hot (4) | wait_norm | state no; reward yes (as B2H) |

**Deviations from the libraries (stated):**
- Our DQN learner, not pfrl. pfrl is not installed, and no installs are allowed.
- drq's phase flag marks lanes served by the current green.
- Keep / switch over two greens.
- RWV adds the green one-hot. RESCO's wave is used by a static rule.

## TSI-G: human-twin sensing (adapter `bis`)

**Information right:** the infrastructure knows which vehicles follow SPaT (V2X membership).

For sensing only, each such vehicle is replaced by a human twin:
- **Free travel:** from lane entry (time, position) at its allowed speed (lane limit × speed factor), delayed by the braking time vf/(2·decel).
- **Car following:** the twin stays one (length + minGap) behind the vehicle ahead, real or twin.
- **On red:** after reaching the queue tail, the twin rolls CREEP s, then halts.
- **On green:** the twin starts τ after the queue member ahead started, or τ after green onset if there is none.
- **Real halts:** a fleet vehicle that really halts is halted.

Driver parameters come from the vehicle type (length, minGap, decel, τ, speed factor). The halting count, RESCO's sticky queued, wait and average speed, and pressure are all computed on the twin state; non-fleet vehicles are unchanged. TSI's speed-binned count is a coarse special case of this layer.

**One site parameter, CREEP:**
- Calibrated on all-human pre-deployment logs: TRAIN seeds 0–7, 3,600 s, FT, every vehicle twinned with the pure model (`scripts/CITY_w20_twin_calib.py`).
- Grid {0, …, 10} s; choose the value minimising |twin / human halting vehicle-seconds − 1|.
- No reward-based search.

**Fleet side:** the same q0.1 hybrid forecast as SV (FRESH3 recipe per light).

## Arms
- **R:** no SPaT.
- **SV:** forecast only.
- **BIS:** forecast + TSI-G.

Run on every W20 light, plus BIS on the W19 AH lights 34–38, whose R / SV / TG rows come from W19.

Light gate: GATE versus FT, every car a SUMO driver (HBEFA4).

## Self-checks
- **KW20-T:** family, 120 episodes, slot seed and input dimension in every checkpoint.
- **KW20-1:** every family's deployed observation equals an independent recomputation (RESCO sticky queued / wait kept per (vehicle, lane) visit), and actions equal the argmax. 0 mismatches over one 600-s episode.
- **KW20-2:** TSI-G with an empty fleet equals the raw observation exactly (AH and RDQ).
- **KW20-3 (descriptive):** twin fidelity when the members are driven by SUMO as humans.
- **KW20-P:** the family is in force in every closed-loop prep, and the widened prep network equals the family network.
- KF-3 for every light; KF-2 for the first light of each family.
- **Degenerate rule (registered):** a light whose 8 traces never complete some green cannot be given a forecaster. Its whole family is then excluded with this reason, and the other families continue. Without RWV, D20-1 is not computable.

## Decisions (crossed bootstrap, B 2000)
- **D20-1[f], f ∈ {SRL, RDQ, RMP}** (α 0.05/3 each): the DiD in agent time loss, (SV − R)_f − (SV − R)_RWV, has lower bound > 0. Publication harms the benchmark's threshold representation more than the threshold-free control.
- **D20-2[f], f ∈ {AH, SRL, RDQ, RMP}** (α 0.05/4 each): BIS − R meets every limit:
  - agent fuel upper < 0 under HBEFA4 and PHEMlight5;
  - city / agent / human time-loss uppers < +0.5 s/veh;
  - teleports ≤ R + 0.1, unfinished ≤ R.

  That is, TSI-G repairs the frozen signal without retraining.
- **Descriptive (95%):**
  - gates;
  - SV − R per family;
  - BIS − SV;
  - BIS − TG on AH (TSI-G against the original TSI);
  - RWV control (expected: SV meets the limits; BIS ≈ SV);
  - mechanism: mean green and served-lane halting under R / SV / BIS;
  - the calibrated CREEP and its fit.

## Reading map, fixed now

| Outcome | Reading |
|---|---|
| D20-1 SHOWN for the RESCO / sumo-rl families | The closed loop hits the community's default representations, not only our RL-H. |
| D20-2 SHOWN on them | A controller-agnostic sensing layer repairs frozen signals of every tested threshold representation. This is the paper's generalised contribution. |
| D20-1 NOT SHOWN | The vulnerability is narrower than the defaults suggest, and the paper stays a mechanism-plus-warning paper for RL-H-like signals. |
| D20-2 NOT SHOWN where D20-1 holds | TSI-G does not generalise, and the original TSI remains RL-H-specific. |

**Not tested here** (next, if W20 is positive):
- penetration 0.25 / 0.75;
- the field-matched driver world (W17 IDM);
- the CREEP sensitivity;
- RESCO's own learners.

## Budget
- **Training:** 20 lights × 120 episodes of about 3 s, in about 15 min at P10.
- **Calibration:** 88 runs.
- **Forecasters:** about 20 min.
- **Rows:** 341 confirmation lines × 20 seeds ≈ 6,800 runs, plus 420 gate runs. About 3 h at P9.
- **Order:** queued as job 105 after 104c.
