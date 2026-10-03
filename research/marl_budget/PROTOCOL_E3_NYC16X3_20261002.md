# PROTOCOL E3-NYC — the third network: Manhattan 16×3 with taxi-derived demand
# (written 02/10/2026 22:4x EDT, before any NYC training beyond a 2-iteration smoke; user 22:0x "ok làm số 3 và 4 đi")

## Question
Do the E3 claims established on the 3×3 and 4×4 synthetic grids hold, PROSPECTIVELY, on a third network with 48 agents, real
block spacing and a real route mix: (i) the relay receiver beats the compiled-silent student Z; (ii) rule A (training-relative
provisioning floor) predicts the channels where the iid-trained receiver falls below Z; (iii) training at the deployment channel
rescues it; (iv) the upgrade hazard (a K = 1-trained receiver loses on the fresher iid channel); (v) the support fallback of
PROTOCOL_E3_SUPPORT_FALLBACK_20261002 repairs the hazard cells.

## What this is NOT (user 22:1x)
* The road network is CoLight's roadnet_16_3.json: a STYLISED 16 × 3 grid with Manhattan block spacing (100 m × 350 m), 3 lanes
  per road, 9 phases, 11.1 m/s — not surveyed geometry, not real signal plans.
* The demand keeps the 903 taxi-derived routes and their empirical frequencies (anon_16_3_newyork_real.json), with arrivals
  re-drawn per traffic seed and the intensity scaled by the matched-load rule below — not a replay of real vehicles.
* Controllers, messages and channel versions are all simulated and trained by us.  No real controller logs, no J2735 traces, no
  independently developed stack, no real cross-version data.
* The CoLight data carry no licence: read locally, never redistributed (not committed).

## Setup
* Scenario factory scripts/MARL_nyc_scenario.py (data sha256 918fe133… / f8cbaaae… asserted); every E3 script runs UNCHANGED
  through scripts/MARL_nyc_wrapper.py (scenario factory, 48-agent set actor, relay slots = 8 nearest agents by grid index).
* Matched-load rule (fixed before any run): per-intersection crossing rate = the E3 grids' at the same load parameter (8 / load
  crossings per intersection per s; measured 0.49–0.52 at load 16 and 0.94–1.08 at load 8 on 3×3 / 4×4).  The real intensity
  is 0.147, so μ(16) = 3.40 and μ(8) = 6.80 times the real demand.  Smoke check (22:3x): MP2 Σ waiting on the select episodes
  6 183 for 48 intersections = 129 per intersection vs 134 on 4×4 (2 139 / 16): matched congestion.
* Components per seed s ∈ {0, 1, 2, 3, 4} — the 4×4 commands (RUN_marl_g4_phase1 / phase2 / train_match), unchanged:
  teacher set_full_s (MARL_e3_actor_train_delivery_v6, 2 000 iterations, delivery full); Z = distill_none_s
  (MARL_e3_actor_distill, 500); relayCage_st_s (MARL_e3_actor_distill_v6, prefix, age relay, quant 4, order agefirst, iid);
  relayCK1_st_s (MARL_e3_actor_distill_v9, const1, resumable).  Training / select episodes as in E3 (301–364 / 401–408).
* Panel: traffic seeds 5001–5064 × headways {8, 16} (checked unused).  Evaluations: Z (MARL_e3_delivery_eval_v6, none);
  R_{arm}_K for arm ∈ {relayCage_st, relayCK1_st}, K ∈ {1, 2, 3, iid} (MARL_e3_ageclip_eval, A = −1); the fallback cells of
  PROTOCOL_E3_SUPPORT_FALLBACK (systems FB_S, FB_F, FB_R; calibration on training episodes 301–332 under the training channel).
* Metric and interval: gain vs Z as in scripts/MARL_e3_mixq_report.py (two-level bootstrap over seeds and traffic seeds).
* Rule A input, measured BEFORE any panel evaluation and written to research/marl_budget/e3_nyc16x3_20261002/ruleA.json:
  τ_train = the 99th percentile of the ages (decision steps) of the entries present in relayCage_st's calibration views (its
  own iid training channel, training episodes 301–332; scripts/MARL_e3_fallback_eval.py --calibrate, age_hist), pooled over
  seeds; reported with the closed form K_min = (1 + θ)(m − 1)/(τ_train + 2), θ = −0.08 (frozen, E3), m − 1 = 47.
  Open provenance item (22:40): measured this way, relayCage_st_s0 on 4×4 has p99 = 4, not the 9 of
  PROTOCOL_E3_G4_CONSTK_ADDENDUM4; the source of the 9 is to be traced before either value enters a manuscript.

## Predictions (fixed now)
* N1 (communication helps on NYC) relayCage_st at iid: gain vs Z with 95 % lower bound > 0.
* N2 (rule A, prospective, the count form of Addendum 4 "C-rel") for K ∈ {1, 2, 3}: predicted sign of relayCage_st's gain =
  sign(net_rel / 47 − θ), net_rel = mean over the RELAY deployment views of (entries of age 0 − entries older than τ_train −
  missing agents), from the age histograms the fallback cells record; a cell whose interval covers 0 is "no sign" (reported,
  not scored).  Supported if every scored cell has the predicted sign.  The closed-form K_min is reported alongside.
* N3 (train-match rescue) relayCK1_st − relayCage_st at K = 1: paired gain difference with lower bound > 0.
* N4 (upgrade hazard) relayCK1_st's gain at iid < its gain at K = 1 (paired difference, upper bound < 0).
* N5 (support fallback transfers) FB1 and FB3 of PROTOCOL_E3_SUPPORT_FALLBACK on the NYC cells.
Kill rule: if N1 fails, NYC is a network on which relay communication does not beat compiled silence; N2–N5 are then reported
descriptively and the E3 headline is restricted to the synthetic grids.

## Budget and order
Teachers first (5 in parallel), then Z / relayCage / relayCK1 per seed as its teacher finishes; evaluations last.  Smoke
(22:3x, 2 iterations): 30 s and 79 s per teacher iteration under a load average of 27 (test D running) — the full plan is about
one day of machine time.  Resumable: finished items are skipped, the watchdog restarts stalls.

## Outputs
research/marl_budget/e3_nyc16x3_20261002/{actors, eval, fallback}, ruleA.json, report (scripts/MARL_e3_nyc_report.py).
