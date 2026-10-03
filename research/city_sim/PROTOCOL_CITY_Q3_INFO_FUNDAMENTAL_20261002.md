# PROTOCOL Q3 — the information fundamental diagram of vehicle-carried neighbour information (written 02/10/2026 19:0x EDT,
# before any run)

Plan: research/city_sim/PLAN_CITY_IDEAS_20261002.md (idea 3, "the cars are the channel").  Channel side only; the learned-light
consequence is Q8.

## Model and prediction from theory
A light i that hears about its upstream neighbour j only through vehicles that travelled j → i (store-carry-forward) holds a
copy whose age is the carrier's travel time plus the wait for the next carrier.  With link length L, space-mean speed u and flow
q, a renewal (Poisson) carrier stream gives a mean age A = L/u + c/q with c = 1 (c = ½ for perfectly regular headways).  Under
Greenshields (u = u_f(1 − ρ), q = ρ k_j u), A(ρ) = (L + c/(ρ k_j)) / (u_f (1 − ρ)): it diverges at BOTH ends (no carriers at low
density, slow carriers near jam) and has one interior minimum at ρ* = (−b + √(b² + Lb))/L, b = c/k_j.  A light trained at an
intermediate demand therefore meets information older than its training range at both low and high demand.

## Measurement (SUMO, no learning)
* research/city_sim/net/grid4.net.xml with its static programs (FT; the age then depends on the light policy only through
  travel times, which is reported) and the actuated net (ACT, reported).
* Demand levels: randomTrips periods p ∈ {8, 4, 2, 1.4, 1.0, 0.8} s (≈ 450 … 4 500 veh/h), seeds 0–2, 1 h of departures, run
  to 5 400 s.  Demand files generated with the same command as research/city_sim/demand/grid4 (fringe factor 10, min distance 300).
* Directed links (j → i) whose both ends are traffic lights.  A vehicle entering link (j → i) takes j's snapshot at that time;
  it DELIVERS it when it comes within R = 100 m of i's stop line.  Per light-second (from 600 s, after warm-up): age of i's
  freshest copy of j (undefined before the first delivery: counted as "no copy").  Per cell (demand, link): mean / p50 / p90 age,
  no-copy share, mean link speed, mean density.
## Predictions (fixed now)
* I1 U shape: the demand level with the smallest network-mean age is neither the lowest nor the highest; the lowest and the
  highest levels both exceed that minimum by ≥ 50 %.
* I2 closed form: across (demand, link) cells, A_pred = L_eff/u + 1/q (measured u, q; L_eff = L − R) has Pearson ≥ 0.9 with the
  measured mean age (reported also for c = ½).
* I3 support exit at both ends: with the p = 2 level (1 800 veh/h, the demand used for training elsewhere) as the training
  channel, the share of light-seconds whose age lies above that level's 99th percentile is ≥ 20 % at the lowest AND at the
  highest demand level.
Kill rule: if I1 fails (no interior minimum), the "information gridlock" story is reduced to its low-demand half.

## Outputs
research/city_sim/q3_info_fd_20261002/ (cells.json, report.txt); scripts/CITY_q3_info_fd.py; smoke first.
Lean: LeanCityInfoFundamentalV1 (the closed form: divergence at both ends, the interior minimiser, the both-ends support exit).

## Addendum 1 (written 02/10/2026 19:0x EDT, after the smoke run (1 500 s, seed 0, p = 8 / 2 / 0.8), before the full run)
The smoke run showed that the registered levels never reach congestion on this grid: at p = 0.8 (4 500 veh/h) the mean link
density is 0.007 veh/m/lane (jam ≈ 0.13), so the high-density side of the U cannot appear.  Levels are extended upward with
p ∈ {0.5, 0.35, 0.25} (≈ 7 200 / 10 300 / 14 400 veh/h; teleports reported, time-to-teleport 300 s as before); I1 is evaluated
on all nine levels; I3's "highest level" becomes p = 0.25.  The smoke numbers are not results.
