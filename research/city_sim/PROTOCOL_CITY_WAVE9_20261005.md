# PROTOCOL WAVE 9: robustness of the frozen TSI design, a calibration-free adapter, and a published adaptive signal (registered 05/10 ~17:05, before any wave-9 code was run)

**Why (the user, 16:4x):** "bắt đầu approach các limitation và làm thí nghiệm, nghiên cứu, thay đổi,... để giảm bớt đi".

Each experiment targets one listed limitation of the paper:

| Experiment | Limitation |
|---|---|
| W9-1 COMM | the SPaT channel is assumed perfect |
| W9-2 SENSE | the adapter assumes exact per-lane speed sensing |
| W9-3 EMIS | fuel comes from SUMO's default emission model only |
| W9-4 IDM | one driver model |
| W9-5 GLOBAL | per-signal calibration needs a site simulator |
| W9-6 MP | one signal family |

**Ground rules**
- No earlier verdict changes, and results are reported as they come out.
- Every arm runs the TSI design as frozen; W9-5 changes only the adapter constants.
- **Common rules** (as in waves 6–8): PYTHONHASHSEED 0, OMP 1, the queue with the 15 GB disk guard, a smoke run first, and strict reports that check teleports AND unfinished trips.
- **Bootstrap:** `CITY_wave2_report_v2` draws (seed 0, B = 2000), crossed over light × fleet × traffic.
- **M3 limits:** agent fuel upper < 0; city, agent and human time-loss uppers < +0.5 s/veh; teleports ≤ R + 0.1 per run; unfinished ≤ R.
- **Status:** all readings are **descriptive robustness checks at one-sided α = 0.05 per arm**, except W9-5 (a) and W9-6 (c), which are registered decisions. No family-wise claim is made across arms.

## Panel for W9-1 … W9-4: the W7-1 fresh-policy panel, unchanged

- **Panel:** lights RL-H t9–t13 × R10 fleets s613–s913 × traffic 780–799.
- **TSI configuration:** each light's W7-1 provider (`w7_20261005/fpr/prep/prov_rlh<k>_cl.json` + `cmodel/n2_k<k>.pt`) and its W7-1 adapter choice (`tune/choice.json`).
- **Reference rows:** the comparison is with the W7-1 R rows (`fpr/conf/R_t<k>_s<f>.json`). R uses no SPaT and no adapter, so no channel or sensing change touches it.
- **Exceptions:** W9-3 and W9-4 change the simulator itself, so they run their own R arm.
- **Wrapper:** all perturbations are installed by `scripts/CITY_w9_run.py <mode>`, which monkey-patches the evaluator at run time. No existing file is edited.

### W9-1 COMM: SPaT latency and message loss (fleet side)

| Arm | Change |
|---|---|
| TSI_LAT1 | The fleet receives, at time t, the provider's answer computed at t − 1 s. Times to event are aged by the elapsed time, as a receiver does with an absolute-time SPaT message (time to event − age, floored at 0). If no answer exists at or before t − 1, the answer is invalid. |
| TSI_LOSS20 | Each light's broadcast in each second is lost with probability 0.2. The draw is deterministic: crc32 of (seed, light, second). On a loss, the fleet uses the last delivered answer for that light and link, aged, or invalid if there is none. |
| TSI_LOSS50 | The same with probability 0.5 (stress). |

The provider is still called on every query, so its internal state is unchanged.

### W9-2 SENSE: adapter sensing errors (light side)

The perturbation applies only to the adapter's own count (q_g). The R light keeps its exact halting input, so the comparison is conservative for TSI.

| Arm | Change |
|---|---|
| TSI_DET80 | Each vehicle on a served lane is detected independently with probability 0.8 in each second (crc32 of seed, second, vehicle). A missed vehicle adds nothing to q_g, not even to its halting term. |
| TSI_SPN1 | Every detected vehicle's speed gets Gaussian noise (sd 1 m/s; from crc32 uniforms through the inverse normal CDF) before it is binned into the 0.1 / 2 / 5 m/s bins. |

### W9-3 EMIS: a second fuel model

- **Arms R_EM2 and TSI_EM2:** at every second, each vehicle that has just departed has its emission class set to **PHEMlight5/PC_EU4_G** (petrol Euro-4 passenger car). If the smoke shows that the default class is already a PHEMlight5 class, the class is **HBEFA4/PC_petrol_Euro-4** instead. The default class is printed in the smoke log.
- The first second of each trip keeps the default class. This is disclosed and negligible.
- **Self-check KW9-3:** the emission class does not enter the dynamics. So for every cell, R_EM2 and TSI_EM2 must reproduce the W7-1 R and TSI rows exactly (|Δ| < 1e-9) on city, agent and human time loss and on vehicle count. If not, the arm is VOID.
- **Reading:** TSI_EM2 vs R_EM2, agent fuel upper < 0, and every M3 limit.

### W9-4 IDM: a second car-following model

- **Arms R_IDM and TSI_IDM:** SUMO option `--carfollow.model IDM` for all vehicles. The route vType `v_passenger` sets no model, so the option applies to every vehicle.
- Lights, fleets, providers and the adapter are unchanged. All of them were trained or fitted under Krauss, so this is a model-misspecification stress test.
- **Reading:** TSI_IDM vs R_IDM meets every M3 limit.
- The change of the R arm itself (R_IDM − W7-1 R) is reported descriptively.

## W9-5 GLOBAL: one adapter setting for every light (calibration-free light side)

**The global setting (A, B) = (1, 0.5)**, fixed now from the TSI-2 lights t4–t8 alone (`tsi2_20261005/tune/choice.json`):
- The points qualified on all five lights are {(1, 0.5), (1.5, 0.5), (2, 0.5), (3, 0.5)}.
- The rule takes the smallest A, i.e. the setting closest to the unmodified light.

**(a) Registered decision, on the W8-2 FRESH2 panel** (lights t14–t18 × fleets s1013–s1313 × traffic 800–819):
- FRESH2 is running at this registration, and its tuning results have not been read.
- **Arm TSI_G:** FRESH2's per-light provider (its prep table and N2 model) + adapter q:1:0.5, against FRESH2's R rows.
- **CALIBRATION-FREE ADAPTER PASS** iff TSI_G meets every M3 limit (one-sided α 0.05).
- If FRESH2 did not complete, (a) is not run and this is reported.

**(b) Secondary, on the W7-1 panel:**
- Disclosure: the W7-1 TUNE grids were seen before this registration; (1, 0.5) qualified on all five W7-1 lights, and t9 / t11 / t12 chose (1, 0.25).
- **Arm TSI_G:** run on t9, t11, t12. On t10 and t13 the setting equals the W7-1 choice, so their TSI rows are reused.
- **Self-check KW9-5:** one cell, TSI_G_t10_s613 on seed 780, must equal the W7-1 TSI row bit for bit.

**(c) Calibration budget, offline:**
- For every light with a 4-seed TUNE grid (t4–t8, t9–t13, and t14–t18 when available), the registered selection rule is re-applied on every subset of 1, 2 and 3 of the 4 TUNE seeds.
- Reported: the share of subsets that select the 4-seed choice, and the share whose selection is in the 4-seed qualified set. Descriptive.

## W9-6 MP: a published adaptive signal (MaxPressure) as the upgrade, and a mechanism prediction

**Light: MaxPressure** (Varaiya 2013).
- **Implementation:** `CITY_eval4.MaxPressure`, unchanged. Every DT_L s after MIN_G, the light switches iff the other green's pressure exceeds the current one. Pressure is the vehicle count on incoming minus outgoing lanes, **at every speed**.
- **Earlier result:** with SUMO cars it beat the actuated program (C-23: 22.88 vs 24.59 s/veh).

**Fleets:** the W7-1 fleets s613–s913 (R10 recipe, trained under FT with exact SPaT).

**Fleet-side service for MP:** the TSI fleet-side pipeline, with the light set to MP.
1. Traces: σ* cars, TRAIN 0–7, then the open-loop table.
2. Closed-loop table: the development fleet L11_s13 querying c2 at q 0.5 of the open-loop table, TRAIN 0–7, recorded and refitted. This runs through the evaluator; `CITY_m3_train_E.prep` is RL-H-specific.
3. N2 logs: the development fleet on c2 at q 0.1, TRAIN 0–7.
4. N2 fit, then KF-2 parity on seed 0.

**Light side:** no adapter is defined for MP and none is tested.

**Traffic:** fresh grid4 traffic **820–839**, generated by the job after a non-existence check.

**Arms** (4 fleets × 20 seeds):

| Arm | Light | Fleet SPaT |
|---|---|---|
| R_FT | FT | none (≡ σ*) |
| PL_FT | FT | the fleet's own program SPaT, exact under FT |
| R_MP | MP | none |
| NAIVE_MP | MP | program-derived SPaT, which MP does not follow |
| C2_MP | MP | table service alone: c2 q 0.5 of the closed-loop table, the statistical residual-time family |
| HYB_MP | MP | the TSI hybrid service alone |

**Readings** (one light; crossed bootstrap over fleet × traffic; one-sided α 0.05):
- **(a) Precondition:** PL_FT − R_FT agent fuel upper < 0 on this traffic, i.e. the fleet is beneficial under FT.
- **(b) M2 under MP:**
  - NAIVE_MP − R_MP: harm if the agent fuel lower > 0 or the agent TL lower > 0 (descriptive).
  - DiD: (NAIVE_MP − R_MP) − (PL_FT − R_FT).
- **(c) PRIMARY, a registered mechanism prediction: HYB_MP meets every M3 limit vs R_MP.**
  - Grid4 account (§diag (a)): the service hides eco-approaching vehicles from the halting-count input of the learned light. MaxPressure counts vehicles at all speeds, so the prediction is **YES**: under MP the fleet-side half alone suffices.
  - If HYB_MP fails the agent-time limit, the halting-threshold account does not explain the light-side need in general, and this is reported as a failed prediction.
- **(d) Mechanism probe, descriptive:** mean green and mean halting, R_MP vs HYB_MP. Under RL-H the service lengthened greens from 15.0 to 17.1 s.
- **(e) Recovery, descriptive:** (HYB_MP − R_MP) − (PL_FT − R_FT) on agent fuel, the share of the FT benefit recovered under MP. C2_MP is reported the same way.

## Queue

| Job | Content | Order |
|---|---|---|
| 072b_W9_ROBUST.sh | W9-1 … W9-5 | after 072 LCD2 |
| 072c_W9_MP.sh | W9-6 | before 073 NET3 |

- 073 NET3 stays last, as the user asked.
- **Directories:** `research/city_sim/w9_20261005/{robust,mp}/`.
- **Report:** `scripts/CITY_w9_report.py robust | global | mp`.

## Amendment A1 (05/10 ~19:55, after the W9-1..4 rows were read; registered before any W9-3b code ran)

**Seen:** under PHEMlight5 the frozen TSI, with dynamics bit-identical to W7-1 (KW9-3 PASS), changes agent fuel by +1.76 % [+0.37, +3.12] against R, against −2.61 % under HBEFA4.

**Question W9-3b (descriptive):** is this a property of TSI, or of the fleet itself? Does the R10 fleet's own fuel benefit under the fixed-time signal (M1) survive the second emission model?

- **Arms:** on the W9-6 traffic 820–839, with the W7-1 fleets s613–s913:
  - R_FT_EM2: FT light, no SPaT, i.e. σ*;
  - PL_FT_EM2: FT light, the fleet's own exact program SPaT.
  - Both with every vehicle's emission class set to PHEMlight5/PC_EU4_G at departure (`CITY_w9_run.py em:…`).
- **Self-check KW9-3b:** time losses and vehicle counts equal the W9-6 rows R_FT / PL_FT (HBEFA4) bit for bit.
- **Reading:** (PL_FT_EM2 − R_FT_EM2) agent fuel, against (PL_FT − R_FT) under HBEFA4.
  - If the FT benefit also vanishes or flips under PHEMlight5, the fuel benefit of this fleet family is model-dependent from M1 on. TSI then recovers what the fleet was trained to save under its training model, not a model-free fuel saving.
  - If the FT benefit survives, the model dependence is specific to the upgraded-signal regime.
- **Job:** 072d_W9_EMFT.sh, after 072c, before 073.
