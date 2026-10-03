# PROTOCOL Q2 — does eco-driving hide queues from lights that sense halting vehicles? (written 02/10/2026 19:0x EDT, before any run)

Plan: research/city_sim/PLAN_CITY_IDEAS_20261002.md (idea 6, the car → light direction).  No learning anywhere: the question is
whether the mechanism exists at the sensing layer before any RL is involved.

## Setup
* Network research/city_sim/net/grid4.net.xml (4 × 4, 200 m blocks, 2 lanes per direction, fringe roads), demand
  research/city_sim/demand/grid4/rou_s{0..4}.xml (randomTrips, 1 800 veh/h for 1 h, fringe factor 10; generated 18:18).
* Lights (four modes):
  FT  — the net's static programs (42 s greens; senses nothing);
  ACT — grid4_actuated.net.xml (SUMO actuated logic with its own induction loops, minDur 5, maxDur 50);
  HQ  — halting-count max-queue: every 5 s, once 5 s of green have passed, switch to the other phase when its lanes have at least
        one more HALTING vehicle (speed < 0.1 m/s) than the current phase's lanes; forced switch at 60 s;
  VQ  — the same rule on VEHICLE counts (all vehicles on the served lanes): the sensing variant that a crawling car cannot hide from.
* Eco fleet: a share ρ ∈ {0, 0.25, 0.5, 0.75} of vehicles (stable hash of the id) run a rule-based eco-approach with no SPaT:
  within 200 m of a red / yellow signal head they set their speed to max(3 m/s, distance / 15 s) when that is below their
  current speed (coast to a crawl instead of driving up and stopping); on green they hand back to SUMO's driver model.  SUMO's
  safety checks stay on (no red running, no collisions).
* Seeds 0–4 (SUMO seed = demand seed); 80 runs.  Outputs per vehicle (tripinfo): time loss (primary), waiting time, stops,
  fuel; per run: arrived, teleports.  Fleet-only log statistic H(ρ) = share of vehicle-seconds within 100 m upstream of a
  red / yellow head with 0.1 < v < 5 m/s ("hidden queue mass").

## Predictions (fixed now)
* E1 (reference) under FT, mean time loss at ρ = 0.5 is within ± 3 % of ρ = 0.
* E2 (mechanism) the eco-induced change in mean time loss, (TL(0.5) − TL(0)) / TL(0), is larger under HQ than under FT by at
  least 5 percentage points (paired over seeds; reported with a bootstrap interval over seeds and vehicles).
* E3 (sensing fix) under VQ that excess over FT is less than half of HQ's.
* E4 (reported) ACT: the same excess, with its sign.
* E5 (reported) under HQ the mean WAITING time (the halting-based metric) falls with ρ while the time loss does not: the
  metric divergence.
* E6 (reported) across ρ, H(ρ) from the FT runs (fleet-only logs) ranks HQ's excess harm.
Kill rule: if E2 fails (HQ's excess < 5 points), the car → light mechanism is not established at the sensing layer and idea 6
is dropped from C1.

## Outputs
research/city_sim/q2_eco_detection_20261002/ (rows.json, report.txt), script scripts/CITY_q2_eco_detection.py; smoke first.
