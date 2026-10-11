# The fleet MDP actually implemented by trainers v6 / v7 (written 04/10/2026 12:03, Step 0 of the user's audit CITY_B6_FINAL_AND_SPAT_AUDIT)

This file describes the CODE (`scripts/CITY_env.py` CarRL, `CITY_fleet_train_v3.py` / `v4.py` / `v6.py` / `v7.py`, `CITY_q7_cross_version.DQN`) as it ran for B6-R, B6-H and B6-R5. It is a description, not a fix. Nothing was retrained.

## Agents, decisions, observation

- **Agent set.** A vehicle is an agent iff `_stable_u(seed, vid) < 0.5`, the same rule in training and evaluation. Every other vehicle is SUMO Krauss (σ 0.5, speedDev 0.1).
- **When an agent decides.** Every 1 s simulation step, while its next signal (`getNextTLS`) is ≤ ZONE = 200 m ahead. On grid4 every approach edge is 179–190 m long, so this covers each whole approach link.
- **Observation (6 numbers).**
  1. distance to the stop line / 200;
  2. speed / 14;
  3. 1 if the vehicle's own signal state is green (G/g);
  4. 1 if it is yellow;
  5. `getSpentDuration` of the CURRENT phase of that light / 60;
  6. leader gap / 100 (within 100 m, else 1).

  There is **no time-to-switch, no phase plan and no information about followers.**

## Actions (ownership semantics)

| Class | What happens each second |
|---|---|
| acc | `setSpeed(clip(v + a, 0, v_allowed))`, a ∈ {−3, −2, −1, 0, +1, +2}. The command persists until the next decision. |
| release | acc plus one action that calls `setSpeed(-1)`: SUMO drives that second. Cost is still read and attributed to the decision. |
| residual | `setSpeed(clip(getSpeedWithoutTraCI + δ))`, δ ∈ {−3 … +1}. **Under a persistent `setSpeed`, `getSpeedWithoutTraCI` is capped by the command, so δ = 0 never accelerates** (C-25 / C-27). |
| fine | acc with a ∈ {−1.5 … +1}. |

- When an agent leaves the zone, `_end` calls `setSpeed(-1)`, so SUMO drives outside every zone.
- The SUMO passenger launch acceleration is 2.6 m/s². acc tops out at +2 and fine at +1.

## Cost (reward = −cost, read 1 s after the decision, or at the terminal moment)

- **v3:** `max(0, 1 − v / v_allowed) + 0.5 · fuel_rate[mg/s] / 1000`. This is a realized delay rate plus fuel over the controlled approach only.
- **cotv (CoTV Eq. 2 as a cost):** mean over vehicles on the agent's edge of `max(0, v* − v_j) / v*`, plus `sqrt(Σ_j (max(0, a_j) / 3)²) / N`.

## Terminal and gap conventions

| Event | approach horizon (v6; v7 `approach`) | v7 `trip` (= "chained approaches") |
|---|---|---|
| arrival | terminal, cost 0 | terminal, cost 0 |
| next signal id changes | terminal, cost read now | chained (done = 0) if the new signal is ≤ 200 m ahead; else terminal |
| no next signal (after the last intersection) | terminal, cost read now | terminal, cost read now |
| distance > 200 m | terminal | terminal |
| episode cut (3600 s training, 5400 s evaluation) | the open state is dropped: no transition, no bootstrap | same |
| teleport (lane '' or a sentinel speed) | the agent is hidden that second (counted `skipped`). Its stored state is KEPT, so the next transition **bridges the gap with one discount step γ** whatever its length | same |

**Measured from the training logs** (last 50 episodes):
- Trip mode has about 0.98 terminals per agent trip (857 terminals / 876 trips): every signalised approach of a trip is chained, and about 2 % of trips are cut by the 3600 s end.
- Approach mode has about 4.2 terminals per trip.

So the "trip" horizon costs every signalised approach of a trip, but NOT:
- the exit link after the last signal;
- the time after the episode cut;
- the time inside teleport gaps.

## Silent zeros and counters (what `invalid = 0` does and does not show)

- **Counted:** sentinel or non-finite readings (`invalid`, cost 0), finite negative fuel clamped to 0 (`clamped`), teleport-hidden agent-seconds (`skipped`).
- **NOT counted:**
  - v3: an exception in the reading returns 0;
  - cotv: an exception, an empty edge list, or an invalid lane max speed returns 0.

  So `invalid = 0` does not exclude every API failure. There is also no counter for gap length.
- **Abort:** a positive reward stops training. It catches sign errors, not silent zeros.

## DQN

- Network 6 → 64 → 64 → n_actions (ReLU), double-DQN target, Huber loss, Adam 1e-3, gradient-norm clip 5, Polyak target 0.99.
- Batch 256, 400 gradient steps per episode, replay capacity 200 000.
- Early random episodes produce about 195 000 transitions each, so early on the buffer holds about one episode.
- ε goes from 1.0 to 0.05 over the first 60 % of episodes, then stays at 0.05. γ 0.97 per decision second.
- Training traffic seeds 0–7 in rotation, against ACT.
- Checkpoint = the last episode. No selection by training reward.
- **Logged statistic:** `mean_r` = the mean of per-transition rewards over all agents in the episode. It is NOT a per-trip discounted return and NOT trip fuel / TL.

## Required before any next trainer (no retroactive change to v6 / v7 results)

- Separate counters for: exception-zero, invalid-zero, empty-edge-zero, teleport skips, and the gap-length distribution.
- A declared gap rule: either drop the bridging transition, or accumulate cost over the gap and discount by γ^Δt.
- Explicit costs: outside the zone, the exit link, arrival, teleport and the episode cut.
- Log per-trip return and per-trip fuel / TL beside `mean_r`.
- If SPaT is added: the movement-specific time-to-green / time-to-red, with a validity flag, and a forecast-vs-promise declaration (see `PROPOSAL_SPAT_CONTRACT_20261004.md`, corrections).
