# PROTOCOL W18: can any fleet design keep a material benefit against field-matched drivers? (registered 08/10/2026, 20:30, before any W18 run)

**User decision** (08/10): "thử toàn bộ cách đi" (try all the approaches) — designs D1–D5 of `research/papers/audits/FLEET_DESIGN_CEILING_20261008.md`.

**Seen before registration:**
- W17 stage 1 (C-218).
- The W17 fuel-by-mode decomposition (C-220): the trained fleet avoids idling by creeping at 2–5 m/s (+12.6 points against −13.7, HBEFA4), and its only net gain is smoother high-speed acceleration.
- The literature scan (field EAD results of 12–22% in light traffic; queue-aware optimisation without network-level gain).
- No W18 code has run.

**World.** W17, via `CITY_w18_world.py`, which imports `CITY_w17_world`: every car is the W17-0 joint IDM (KW17-0). Signals: the grid4 fixed-time program (FT), the M1 setting, because the question is whether a fleet has any benefit to protect.

**Comparison.** Each design against OFF: the same cars all human (membership L-ACT:0, guard always, same share). Measures:
- agent fuel under HBEFA4 and PHEMlight5 (same trajectories);
- city / agent / human time loss;
- network fuel (all vehicles);
- crossed bootstrap B 2000, CITY_w13_modes, KM13-1a/1b.

## Designs

| ID | Design | Training | Screen variants |
|---|---|---|---|
| D1 | Off-peak demand (randomTrips period 4.0 s, half demand; `demand/grid4_p4`) | R10 recipe trained at off-peak, fleets s3613 / s3713, 400 ep | — |
| D2 | Queue-aware, no-creep (`CITY_fleet_w18.CarPPOLQ`): rule speed d_q / (ttg + t_q) with queue length q from lane halting (7.5 m / 2.0 s per vehicle); release below 5 m/s | (a) rule only: residual 0 = the zero-initialised net; (b) PPO residual trained on this base, s3213 / s3313, 400 ep | both |
| D3 | R10 recipe trained with PHEMlight5 fuel in the cost (W17_EM during training) | s3413 / s3513, 400 ep | — |
| D4 | Penetration: the W17 fleets s2213–s2513 at shares 0.75 and 1.0 (OFF at the same share) | none | 0.75, 1.0 |
| D5 | Gentle departures: always-SUMO agents with acceleration capped at 1.0 / 1.5 / 2.0 m/s² (no SPaT) | none | three caps |

**Baseline.** The W17 fleets at share 0.5 (the W17 result, re-measured on the new seeds).

## Stages

**W18-1 screen (descriptive).**
- TUNE 660–663 (peak) and TUNE_p4 660–663 (off-peak, new files).
- Every design and variant against OFF, both models.
- Per family, the **candidate** is the variant with the best max(fuel H4, fuel P5) among those whose city / agent / human time-loss means are ≤ +0.5 s/veh.

**W18-2 confirmation (registered).** Each family's candidate against OFF on fresh traffic: peak 1360–1379; off-peak `grid4_p4` 1380–1399. Both are generated only after a non-existence check.

**Decision per family (α = 0.01; Bonferroni over 5 families):** a **material benefit** requires
- agent fuel upper < −3% under **both** emission models;
- every M3 time-loss upper < +0.5 s/veh;
- teleports not above OFF + 0.1 per run.

Reported regardless of outcome: network fuel and the mode decomposition.

**Reading.**
- If no family shows a material benefit, the answer for this design space is "no tested design keeps ≥ 3% against field-matched drivers on grid4". That is not a proof that none exists.
- If some family does, the TSI question (does the upgrade remove that benefit?) becomes worth re-running for that design.

## Self-checks

- **KW18-0:** KW17-0 in every process.
- **KW18-1:** with `W18_DEMAND=p4`, the route copies carry the W17 vType and the off-peak files have about half the vehicles of the peak files (0.4–0.6).
- **KW18-2:** D2(a) at episode 0 is the queue-aware rule (zero residual): its rows are identical with the deterministic zero-initialised CarPPOLQ net. Checked by running the untrained s3213 checkpoint at episode 0 = a smoke.
- **KW18-3:** D4 OFF at share 1.0 has agent fuel equal to total fuel.

**Jobs:** 103a (training D1 / D2b / D3 in parallel, the screen, the per-family candidates) and 103b (the confirmation and the report). Smoke first.

## Amendment A1 (08/10, 20:34; after the job smokes only, before any real W18 run)

**Seen:** the 600-s smokes (1 seed, 1-episode fleets). D5 gentle departures showed large PHEMlight5 fuel reductions with agent time-loss increases above +0.5 s/veh, so the eligibility rule excludes them.

**Change (descriptive only):**
- The screen also records a **trade-off** candidate: the D5 variant with the best max(fuel H4, fuel P5), ignoring time.
- The confirmation runs it against OFF as family `D5_tradeoff` and reports fuel (upper < −3% under both models, α 0.01) **together with** the time-loss intervals.
- The label is "trade-off: fuel bought with time". It is not a registered material-benefit decision, because time non-inferiority is not required.
- The five registered family decisions are unchanged.

**Also documented:** at share 1.0 (D4b, OFF100) there are no humans, so human time loss and human fuel are set to 0 for the paired statistics.
