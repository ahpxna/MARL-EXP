# PROTOCOL W16: the IDM world, end to end (registered 08/10/2026, 09:58, before any W16 code ran)

**User decision** (08/10, after the field checks): "W16: thế giới IDM" (the IDM world), together with F1-B and F3.

**Why.** Field check F4 (C-199) found that IDM fits NGSIM Peachtree car-following better than Krauss and that SUMO's Krauss cars brake far later and harder at a stop than measured drivers. Every positive result of the paper was obtained with Krauss human cars; every IDM test failed on fuel. But those IDM tests deployed Krauss-trained policies (W9-4, W13-6a, W15-3a/b). W16 asks the decisive question: **in a world where every car follows a field-calibrated IDM, and the lights and the fleet are trained in that world, is there (a) a fleet benefit worth protecting, (b) a loss after the signal upgrade, and (c) a recovery by TSI?**

**Seen before registration:**
- All W15 results and F2, F3t, F4.
- The F4 calibrated IDM: accel 2.192, decel 2.054, τ 0.742 s, minGap 3.952 m (v0 11.38 m/s on Peachtree).
- No W16 simulation.

## World

**Every vehicle** is of type `DEFAULT_VEHTYPE`, redefined by an additional file `research/city_sim/w16_20261008/idm_peachtree.add.xml`:

```xml
<vType id="DEFAULT_VEHTYPE" carFollowModel="IDM" accel="2.192" decel="2.054" tau="0.742" minGap="3.952"/>
```

- The desired speed is the lane limit times SUMO's default speed distribution. The Peachtree v0 belongs to that arterial and is **not** used.
- Fleet agents are the same type; their speed is commanded by the policy when it acts.

**Wrapper `CITY_w16_idm.py`** (no file edited):
- It patches `CITY_env.run_episode` and `CITY_eval4.run_episode`, and every already-imported module attribute bound to the original function (in particular `CITY_q7_cross_version.run_episode`). This matters because `CITY_q7b_contract` / `CITY_q7_cross_version` import `run_episode` by name, which the W13 IDM wrapper did not reach for light training.
- It adds `-a idm_peachtree.add.xml` to every SUMO start.
- Optional `W16_EM` (PHEMlight5) as `W13_EM`.

**Self-checks:**
- **KW16-0:** in every process, the first vehicle's type is read back via libsumo; the run stops unless its tau is 0.742 and decel 2.054 (±0.001). Accel and minGap are checked too where the API exposes them.
- **KW16-1:** a 600-s smoke of every stage prints KW16-0.

## Panel FRESH4 (new seeds)

| Element | Seeds and settings |
|---|---|
| Lights | RL-H t24–t28 (DQN seed 11 + 100t), 120 episodes, TRAIN 0–7 |
| Fleets | R10 PPO s1813, s1913, s2013, s2113; 400 episodes; FT signals with exact FT SPaT; TRAIN 0–7 |
| F1-B | from scratch, 200 episodes, fleet i under light t(24 + i), q 0.1 |
| Fresh traffic | M1 / gate 1300–1319; confirmation 1280–1299. Generated only after a non-existence check. |
| TUNE | 660–663 |
| Statistics | crossed bootstrap B 2000; M3 limits; KM13-1a/1b |

## Stages and decisions (α = 0.05 unless stated; both emission models on the same trajectories)

**W16-1 (M1-IDM, registered).** Arms under FT on 1300–1319:
- OFF: every car is an IDM human (`--fleet human`);
- PL: the IDM-trained fleet with exact FT SPaT (`CITY_eval6_v11 --light FT`);
- R: the fleet without SPaT.

**D16-1:** PL − OFF agent fuel upper < 0 under HBEFA4 **and** PHEMlight5, every M3 time limit holds, and teleports are not higher.
- If D16-1 fails, there is no fleet benefit to protect in the IDM world. The fleet-side premise of the paper fails there; W16 stops and reports.

**W16-2 (light gate, registered).** RL-H(IDM) − FT city time loss on 1300–1319 (all IDM humans), upper < 0. If it fails, W16 stops.

**W16-3 (M2-IDM, descriptive + registered as M2).** Under the learned lights:
- PL with no SPaT (R) against OFF: is the benefit lost?
- PL with the old FT program served as SPaT: is there harm?

**W16-4 (TSI-IDM, registered).** Calibration exactly as W15-1 (traces → open-loop → c2 → N2 → fit, KF-2), all inside the IDM world.

Arms on 1280–1299:
- R;
- TG, the default (1, 0.25, 0.1), no adapter or quantile tuning;
- TU, rule R15-U over the W13 grid and the 27 state-dependent quantiles, on TUNE;
- F1B.

**Decisions:**
- **D16-2:** TG meets every M3 limit and saves agent fuel under both emission models.
- **D16-3:** TG − F1B fuel (PHEMlight5, the field-closer model by F2) upper < +0.5 pp.
- **Descriptive:** TU − TG; TG − R under HBEFA4.

**Order and cost.** One job (098), staged with stops:
1. training (lights and fleets in parallel);
2. W16-1 / W16-2;
3. if both pass, F1-B, calibration, W16-3 and W16-4.

Smoke first. Roughly 8–12 h.

## Amendment A1 (08/10, 10:00; after the first wrapper smoke, before any W16 run)

**Seen:** KW16-0 failed on the first smoke, as it should have. The grid4 route files define their own `<vType id="v_passenger" vClass="passenger"/>`, so redefining `DEFAULT_VEHTYPE` does not apply: the read-back gave τ 1.0, decel 4.5.

**Change:**
- The wrapper maps every grid4 route file to an IDM copy, `research/city_sim/demand/grid4_idm/rou_s<seed>.xml`, written atomically on first use. In the copy, the single `v_passenger` vType line gains `carFollowModel="IDM" accel="2.192" decel="2.054" tau="0.742" minGap="3.952"`; the check KW16-R fails unless that line is found exactly once.
- KW16-0 now reads back all four parameters.
- The model name is not exposed through the API. Matching parameters imply that the rewritten element, which carries `carFollowModel="IDM"`, was loaded.
- The additional file `idm_peachtree.add.xml` is kept for the record but no longer used.

## Amendment A2 (08/10, 10:08; procedural, before any W16 run)

The single staged job is split into two jobs. **098a:** training, W16-1, W16-2 and the M2 rows. **098b:** written only after 098a reports, and only if D16-1 and W16-2 both pass; it covers F1-B, calibration, tuning, R15-U and the W16-4 confirmation. Decisions, panels and levels are unchanged.

Row tags of stage 1 are as in `scripts/CITY_w16_report.py`. The all-human arms use `CITY_eval6_v11 --fleet L-ACT:0 --guard always`, the always-SUMO arm of the paper's M1.
