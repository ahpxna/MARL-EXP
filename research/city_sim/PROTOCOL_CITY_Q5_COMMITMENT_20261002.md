# PROTOCOL Q5 — honest [minEnd, maxEnd] commitment windows: the light's own gain against the cars' information (written 02/10/2026
# 19:2x EDT, before any run)

Plan: research/city_sim/PLAN_CITY_IDEAS_20261002.md (idea 5).  SAE J2735 SPaT carries minEndTime / maxEndTime / likelyTime, which
adaptive controllers fill with meaningless defaults; here a light publishes an HONEST window and is bound by it.

## Model
* One intersection, approaches A (studied, eco cars) and B (cross); 1 s steps; Bernoulli arrivals λ_A, λ_B per second; the green
  approach discharges one queued vehicle with probability 0.5 per second; each switch costs 4 s of all-red; 2 h per run.
* Lights:
  ADAPT (w = ∞) — max-queue rule: once 10 s of green have passed, switch when the other queue exceeds the current one by ≥ 2 or the
    current queue is empty and the other is not; forced at 60 s.
  COMMIT(w) — at each green start the light plans D* = clip(10 + 2·q_current, 10, 60) and publishes the window
    [D* − w/2, D* + w/2] (clipped to ≥ 10 s); inside the window it applies ADAPT's rule, it switches at the window's end at the
    latest and never before its start.  w ∈ {0, 2, 5, 10, 20, 40}.  w = 0 is a strict commitment made at the phase start.
  REVISE1 — COMMIT(0) that may revise its D* ONCE, at the phase's midpoint, to clip(t_mid + 2·q_current, ...), republishing it.
  FIXED — pre-timed: the best fixed split over a grid (reported).
* The light's own objective G_L: mean delay per vehicle over both approaches (arrival to departure).
* Cars (probes on A; they do not change the queues): C0 dynamics (stop line, actions, costs), episodes started at random times
  with L0 ~ U{150..250} m.  Policies: PRIVILEGED (exact DP with the realised schedule; regret 0 by definition), RULE (C0's rule
  car, no SPaT), WINDOW (uses the published window: on red it aims to reach the line at the earliest possible green; on green it
  goes only if it reaches the line before the window opens, else it prepares to stop).  Car metric H_C: regret of WINDOW.
* Demand (λ_A, λ_B) ∈ {(0.20, 0.15), (0.25, 0.20), (0.30, 0.25)}; seeds 0–2; 1 000 car episodes per (light, demand, seed).
## Predictions (fixed now)
* P5-1 (the price of predictability is small somewhere): at every demand level there is a w ≤ 10 s with G_L within 5 % of ADAPT and
  H_C within 25 % of COMMIT(0)'s.
* P5-2 (one revision): REVISE1 has G_L within 5 % of ADAPT and H_C within 25 % of COMMIT(0)'s at every demand level.
* P5-3 (reported) the frontier (G_L, H_C) over w; RULE's regret on every light (information value of the window); FIXED.
Kill rule: if neither P5-1 nor P5-2 holds, the commitment contract costs the light too much on this model and idea 5 is reported
as a negative.

## Outputs
research/city_sim/q5_commitment_20261002/ (rows.json, report.txt); scripts/CITY_q5_commitment.py; smoke first.

## Addendum 1 (written 02/10/2026 19:2x EDT, after the smoke run (1 demand, seed 0, 60 car episodes), before the full run)
The smoke run showed ADAPT (δ = 2) with a HIGHER delay than COMMIT(5) (27.2 vs 18.2 s/veh): the switching rule is too twitchy and
pays the 4 s all-red too often, so the "fully adaptive" reference was not the best light of its family and the frontier would be
meaningless.  Change: per demand level, on tuning seeds 100–102 (light objective only, no cars), choose ADAPT's switching margin
δ ∈ {2, 4, 6, 8, 12, gap-out only} and COMMIT's planning slope c ∈ {1, 2, 3, 4} (D* = clip(10 + c·q, 10, 60)) that minimise
the mean delay; every COMMIT(w) and REVISE1 then uses that δ inside its window and that c for its plan, so COMMIT(w) → ADAPT as
w grows.  Predictions, thresholds, seeds 0–2 and the car side are unchanged.  The smoke numbers are not results.
