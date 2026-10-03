# PROTOCOL Q2b — is the eco-driving × sensing harm robust to the eco design, and which light-side fix removes it?
# (written 02/10/2026 19:3x EDT, after Q2's result (ledger C-1), before any Q2b run; user 19:3x: Q2b before Q5)

## Why
Q2's eco rule was crude (no SPaT; coast to a 3 m/s crawl, 15 s guess).  Q2b asks whether the harm survives (i) other crawl
speeds and (ii) a SPaT-aware GLOSA rule, and whether a LIGHT-side change removes it (detector timing, or sensing delay instead
of gaps).  No learning.

## Setup (as Q2 except where stated)
* Network grid4 (4 × 4, 200 m, 2 lanes, fringe); demand research/city_sim/demand/grid4_levels/rou_p{2,1_0}_s{0,1,2}.xml
  (1 800 and 3 600 veh/h; seeds 0–2).
* Lights: FT (static); ACT (SUMO actuated, defaults); ACT_GAP5 (max-gap 5 s instead of 3); ACT_FAR (detector-gap 4 s instead of
  2: detectors further upstream); DELAY (SUMO delay_based: extends green on the accumulated time loss of approaching vehicles);
  HQ and VQ as in Q2.  ACT_GAP5 / ACT_FAR are the actuated net with the parameter written into every tlLogic; DELAY is the same
  grid generated with --tls.default-type delay_based.
* Eco fleet share ρ ∈ {0, 0.5}; eco variants at ρ = 0.5: CRAWL3 (Q2's rule), CRAWL5, CRAWL7 (crawl floor 5 / 7 m/s), GLOSA
  (target arrival at the predicted green: time to green = SUMO's next switch of the current phase plus the program durations of
  the following phases up to the car's green; speed set to max(2, distance / time to green) when below the current speed; on
  HQ / VQ no prediction exists, GLOSA falls back to CRAWL3 and is reported as such).
* Per vehicle: time loss (primary), waiting time, stops, fuel; 2 demands × 3 seeds × 7 lights × 5 (ρ = 0 + four variants) = 210 runs.
## Predictions (fixed now)
* B1 (robust to the eco design) ACT's excess over FT — (TL(0.5)/TL(0) − 1)_ACT − (TL(0.5)/TL(0) − 1)_FT with the same eco
  variant — is ≥ +10 points for EVERY eco variant, GLOSA included, at both demands.
* B2 (eco works where SPaT is exact) under FT, GLOSA changes time loss by ≤ +3 % and cuts stops by ≥ 15 %.
* B3 (a light-side fix exists) for CRAWL3 and for GLOSA, at least one of ACT_GAP5, ACT_FAR, DELAY has an excess over FT at most
  half of ACT's (reported which; DELAY expected best, since a crawling car still accumulates time loss).
* B4 (reported) the hidden-queue share (HQ excess − VQ excess) / HQ excess per eco variant and demand.
Kill rule: if B1 fails for GLOSA, the Q2 claim is restricted to SPaT-less eco-driving.

## Outputs
research/city_sim/q2b_eco_robustness_20261002/ (rows.json, report.txt); scripts/CITY_q2b_eco_robustness.py; smoke first.
