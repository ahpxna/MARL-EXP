# PROTOCOL W17: a field-matched human driver (registered 08/10/2026, 19:10, before any W17 code ran)

**User decision** (08/10): "W17: người lái khớp thực địa" (a field-matched human driver), together with F1-3/F1-4 and paper finishing.

**Why.** W16 (C-209) found no fleet fuel benefit against IDM humans calibrated on Peachtree car-following, while the paper's benefit is against Krauss humans. On stop approaches (F4 C2) Krauss stops over 17 m, the C1-calibrated IDM over 177 m (147 m with defaults), and measured drivers over 82 m (11.7 s, peak 2.6 m/s²). Neither world matches measured approaches. W17 calibrates one human model to **both** car-following and stop approaches, then re-measures the fleet benefit and TSI.

**Seen before registration:** F4 (C1 / C2 numbers above), W16 stage 1, F1 M1-SL. No joint calibration has been run.

## W17-0 Joint calibration (field data, NGSIM Peachtree; extends protocol FIELD F4)

**Model.** SUMO IDM with calibrated accel, decel (b), tau (T), minGap (s0) and delta (δ ∈ [2, 8]). The desired speed is the measured entry speed in C2, and the vType maxSpeed in car-following as in F4.

**Data split:**
- F4's train/test pairs.
- Free approaches split 60/40 by a hash of the key (approach train / test).

**Objective (minimised on train):**
- J = NRMSE_spacing(train pairs) + 0.5 × E_C2(train approaches).
- E_C2 = mean over approaches of (|log(d_sim / d_meas)| + |log(t_sim / t_meas)| + |log(a_sim / a_meas)|) / 3, where d = braking distance, t = time from the end of the last cruise plateau to stop, a = peak deceleration (F4 C2 definitions; SUMO single-vehicle runs as in F4).
- Nelder–Mead, start at the F4 IDM calibration (δ = 4) plus 3 seeded starts, ≤ 150 evaluations each.

**Report on test:** NRMSE_spacing, E_C2 and the three medians, for:
- the joint IDM;
- the F4 IDM;
- Krauss default and calibrated.

**Gate G17-0:** the joint model's test E_C2 is below both Krauss default and the F4 IDM, and its test NRMSE is at most 0.05 above the F4 IDM's. Otherwise W17 reports the trade-off and stops.

## W17-1 / W17-2 / W17-3 (as W16 stage 1 / stage 2, every car the joint model)

- **World:** a wrapper `CITY_w17_world.py`, a copy of CITY_w16_idm with the vType attributes read from `research/city_sim/w17_20261008/human.json`. Route copies go to `demand/grid4_w17/`. KW17-0 reads back accel, decel, tau, minGap.
- **New seeds:** lights RL-H t29–t33; fleets s2213, s2313, s2413, s2513; F1-B as W16; fresh traffic 1320–1339 (M1 and gate) and 1340–1359 (confirmation); TUNE 660–663.
- **Decisions:** D17-1 (M1 in this world; both emission models; every limit; stop if not shown), W17-2 (light gate), D17-2 (TG saves fuel under both models; every limit), D17-3 (TG − F1B PHEMlight5 upper < +0.5 pp); descriptive TU − TG.
- **Jobs:** 101a (training, M1, gate) and 101b (stage 2; it runs only if D17-1 and W17-2 pass, read from `m1/stage1.json`).
