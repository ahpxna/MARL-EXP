# Claim table (draft): two populations, lights × cars, staged upgrades. Written 09:44 04/10/2026

Every row points to a city-ledger row (`research/city_sim/CITY_LEDGER_20261002.md`), a registered protocol and a report file. Rows are claims that are ALLOWED NOW. Pending rows are marked. Nothing here is a manuscript.

## Setting

SUMO 4×4 grid (`grid4`), 1 800 veh/h for 1 h, half the cars belong to the "fleet" (`_stable_u(seed, vid) < 0.5`). Lights:
- ACT: SUMO actuated;
- FT: fixed time;
- RL-H: a learned keep/switch DQN, trained with human (SUMO, σ 0.5) traffic;
- RL-C50: RL-H with a 50 s green cap;
- MP: MaxPressure.

Fleets are learned speed policies within 200 m of the next signal, or SUMO's driver model at imperfection σ. Determinism: PYTHONHASHSEED = 0, OMP = 1 (bit-identical across runs, C-27).

## Claims allowed now

| # | Allowed wording | Evidence |
|---|---|---|
| T1 | A learned light (RL-H, four training seeds) beats the actuated light for all-SUMO traffic by 2.48–2.75 s/veh city time loss on grid4 (049l, σ 0.5 rows; SELECT), and MaxPressure (city TL 22.88 with all-SUMO traffic, job 045) by about 0.8–1.0. Not replicated on cologne8 with the same recipe (C-35, C-36). | job 049l (C-30 panel; always-SUMO ≡ human-only run, W3 self-check), job 045 / dir 090 (C-23) |
| T2 | When the light is upgraded, a frozen learned fleet trained under ACT can regress sharply (agent TL +25). A REACTION repair on the car side, falling back to the human driver model outside the fleet's training support, removes about 70 % of the city-level harm with no retraining. An INPUT repair (τ-clip) does not help. A green-release guard brings the city below the ACT baseline in 16/16 cells, on fresh traffic too. **But switching the fleet off is better still in every light**, so these fleets were not worth deploying. | C-14, C-16, C-17, C-19 |
| T3 | (corrected 12:04, C-37) **No learned recipe was confirmed to meet, at once, the fuel benefit, the TL margin and no harm to other vehicles, in the settings tried**: more than 10 recipes, a published CAV reward (CoTV), 4× budget, approach and chained-approach horizons. The time gains seen on SELECT did not confirm on new seeds (B6-T), and they were smaller than SUMO Krauss without imperfection (σ 0: −5.2 s/veh). Strict dominance test (descriptive, both axes): 11 / 12 early fleets are dominated by some σ; R4v6_t1 is not separated. The chained-approach v3 / release recipe (R5h) is a different trade-off: it saves fuel on every seed (pooled −3.3 %) and is beyond the tested σ-family on fuel, but it is slower (+3.0 s/veh) and fails B6-1 on 4/4 new seeds. Its development checkpoint t0 passes B6-1 on fresh traffic, so a feasible policy exists in the class. The cause (information, objective, optimisation stability) is NOT isolated. | C-21, C-23, C-26 … C-31, C-37 |
| T4 | A beneficial non-learned fleet upgrade (σ 0.5 → 0.3: −2.5 s/veh and −2.2 % fuel for the fleet) keeps its benefit under the frozen learned light. The interaction with the light upgrade is −0.16 [−0.43, +0.09] s/veh city TL, i.e. none detected. The learned light is not specific to the driver model in this range. Confirmed on VALIDATION 200–209 (−0.17 [−0.48, +0.12]). This does NOT isolate why the earlier learned fleets were harmed (learning, reward errors, support and behaviour all differ between the groups; C-37 F). | C-30, C-32, C-37 |
| T5 | An automated fleet upgrade (SUMO's ACC car-following model on the fleet cars, not learned) is not harmed by the frozen learned light; the two upgrades are super-additive: city-TL interaction −0.83 [−1.17, −0.52] (VALIDATION), and the learned light's gain grows from −2.41 to −3.24 s/veh. ACC raises fleet fuel by 5–8 %. The registered prediction (interaction inside ±0.5) failed, in the beneficial direction. **T4 and T5 hold for two more learned-light families** (RL-C50; RL-J, trained with a learned fleet as partner): no harm in 4/4 cells, ACC interaction −0.80 … −0.86. | C-33, C-34 |
| M1 | Evaluation pitfalls, each with a demonstrated effect: (a) rewards that score the command instead of the realized motion are exploited (v1, C-17 / C-21b); (b) libsumo returns a sentinel −2³⁰ for teleporting cars, which entered rewards (C-22); (c) under `setSpeed`, `getSpeedWithoutTraCI` is capped by the command, so "SUMO + residual" with δ = 0 never accelerates and jams the network (C-25 / C-27); (d) always-SUMO (σ 0.5) is a weak comparator for a commanded fleet; use the σ-family, with a strict two-axis dominance test (C-28, corrected C-37); (e) a registered OR-of-one-sided rule ('better on TL or fuel') must not be reported as dominance when it fails. | as listed |

## Pending (registered, running or gated)

| # | Question | Job / rule |
|---|---|---|
| ~~P1~~ CLOSED (C-31) | R5h NOT CONFIRMED: fuel −3.3 % on every new seed but agent TL +3.0 and human NI fails; a fuel-for-time trade-off | 050r, B6-R5 |
| ~~P2~~ not run | gated on P1 | 051p exited at its gate |
| ~~P4~~ DONE (C-32) | T4 confirmed on VALIDATION 200–209: interaction −0.17 [−0.48, +0.12] | 052v |
| P3 (C-35) | Second network (RESCO cologne8): T1 NOT replicated with the grid4 light recipe (RLK worse than FT by +4.79); T4 / T5 inconclusive (point ≈ 0, CI ±2: underpowered, and the light is not beneficial). At 480 episodes the light is worse still (+15.10, C-36), so the recipe does not transfer; a different light recipe is needed. | jobs 055, 056 |

## Wording rules

| Do NOT write | Write |
|---|---|
| "learned fleets beat human drivers" | T3 wording; always give the σ-family comparator |
| "the guard makes the fleet safe / beneficial" | "limits the damage of a harmful fleet; fleet-off is better" (T2) |
| "observation repair does not work" | "in the panel tried, the car-side fallback helped clearly and τ-clipping did not" (user wording) |
| "no compatibility problem between populations" | T4 is about a NON-learned fleet upgrade; for learned fleets see T2 and P2 |
| "R5h is beneficial" | "R5h is a fuel-for-time trade-off that failed B6-1 on 4/4 new seeds; its development checkpoint t0 passed on fresh traffic" (C-31, C-37) |
| "no learned fleet can be beneficial in this observation space" / "SPaT is necessary" | T3 (corrected): not confirmed in the settings tried; cause not isolated |
| "dominated by the σ-family" for a failed S-2 | "not established beyond the tested σ-family" unless the two-axis dominance test holds |
| "trip horizon" | "chained approaches" (exit link, episode cut and teleport gaps not costed) |
| "perfect driver" (σ 0) | "SUMO Krauss without imperfection (σ = 0)" |
| "the earlier harm came from exploited rewards" | "harm was seen with weak / fragile learned fleets; the cause is not isolated" |
