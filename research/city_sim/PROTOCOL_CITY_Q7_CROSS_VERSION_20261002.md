# PROTOCOL Q7 — learned lights × learned cars: does a genuinely better learned upgrade break a deployed learned partner?
# (written 02/10/2026 21:4x EDT, before any Q7 run; user 21:4x "làm novelty check Q2 rồi viết Q7 đi")

The decisive missing piece of research/papers/audits/CITY_TWO_POPULATION_NOVELTY_20261002.md §6: an upgrade that is a LEARNED
controller, better on its OWN objective with the traffic it was trained on, deployed next to an already-deployed LEARNED partner.
Both directions are measured with the same trained components.

## Setup
* SUMO grid4 (research/city_sim/net/grid4.net.xml; grid4_actuated.net.xml for ACT), demand research/city_sim/demand/grid4/rou_s{k}.xml
  (1 800 veh/h, 1 h); training seeds k ∈ {0..7} cycled, evaluation seeds 100–104 (generated with the same command).
* Environment scripts/CITY_env.py (LightRL, CarRL); trainer / evaluator scripts/CITY_q7_cross_version.py.
* Lights: FT (static program), ACT (SUMO actuated), RL-H (DQN keep/switch every 5 s, shared over the 16 lights; observation
  halting and vehicle counts per green phase, current phase, time in phase; reward −halting/10; trained with HUMAN traffic only),
  RL-C (RL-H deployed with a forced switch at 50 s = ACT's maxDur: the compatible mode), RL-J (the same DQN retrained with the
  learned fleet L-ACT present at ρ = 0.5: train-match on the light side).
* Fleets (share ρ = 0.5 of vehicles; the rest human SUMO drivers): L-ACT (DQN eco-approach agents trained against ACT: speed
  choice every second within 200 m of the next stop line; observation distance, speed, green, yellow, time in phase, leader gap;
  cost 1 + 0.05a² + idle per second; an approach ends at the stop line), L-RLH (the same trained against RL-H: the car-side
  specialist for the new light).  Each DQN: replay 200 000, batch 256, Adam 1e-3, soft target 0.01, ε linear 1 → 0.05 over the
  first 60 % of episodes; lights γ = 0.9 per decision, cars γ = 0.97; 120 training episodes each.
* Metrics (evaluation seeds 100–104, paired): network mean time loss per vehicle (tripinfo, all vehicles); the fleet's own
  objective = mean approach cost of agent cars (the training cost); the light-side interface statistic for the cars = time in
  phase at agent decision points; the light's own log statistic = share of green-seconds beyond ACT's maximum (50 s).
## Predictions (fixed now)
* Q7-1 (the upgrade is genuinely better): with human traffic only, RL-H's mean time loss is ≥ 5 % below ACT's and below FT's.
* Q7-2 (light → car hazard): Δ_car = cost(L-ACT under RL-H) − cost(L-RLH under RL-H) > 0 (paired bootstrap lower bound > 0).
* Q7-3 (certificate, partner-only): the share of RL-H green-seconds beyond 50 s in RL-H's OWN logs with human traffic is ≥ 10 %,
  and the out-of-support mass of the fleet's decision-time τ under RL-H (vs its ACT training range) is ≥ 10 %.
* Q7-4 (compatible mode): RL-C keeps ≥ 80 % of RL-H's improvement over ACT with human traffic AND halves Δ_car
  (cost(L-ACT under RL-C) − cost(L-RLH under RL-H) ≤ ½ Δ_car).
* Q7-5 (car → light hazard, learned version of Q2): RL-H's relative time-loss change from human-only to the L-ACT fleet exceeds
  FT's by ≥ 5 points; RL-J recovers ≥ half of that excess.
Kill rules: if Q7-1 fails the RL light is not a genuine upgrade and Q7-2 … Q7-4 are reported as descriptive only; if Q7-2 fails
the light → car hazard does not appear with learned partners in SUMO.

## Outputs
research/city_sim/q7_cross_version_20261002/ (checkpoints *.pt, training logs, eval rows.json, report.txt); smoke first.
