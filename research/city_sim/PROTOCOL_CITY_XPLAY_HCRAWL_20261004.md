# PROTOCOL — two-population cross-play (B1) and the hidden-queue sensing test (B1b)

Written 04/10/2026 02:4x EDT, wake 1, before any run. Context:
- `research/papers/audits/TWO_POPULATION_AUDIT_VERIFY_20261004.md` §5;
- review TWO_POPULATION_DESTINATION_AND_REOPENING_20261004.

## Status

**B1 is EXPLORATORY.** Every checkpoint and its same-index rows were already examined in Q7 / Q7b. No result here confirms a hypothesis.

**B1b is registered here.** It has its own predictions. Its sensing variant has never been run.

## Policies (existing checkpoints only — no training)

**Lights** (shared-parameter DQN; keep / switch every 5 s):

| Light | Checkpoints |
|---|---|
| RL-H_t | t = 0 `research/city_sim/q7_cross_version_20261002/RL-H.pt`; t = 1..3 `research/city_sim/q7b_contract_20261002/RL-H_t{t}.pt` |
| RL-J_t | same locations |
| RL-C50_t | RL-H_t with a forced switch at 50 s |
| ACT | SUMO actuated, `grid4_actuated.net.xml` |

**Fleets** (agent share ρ = 0.5; speed choice every 1 s within 200 m):

| Fleet | Checkpoints |
|---|---|
| L-ACT_t′ | t′ = 0..3 |
| L-RLH_0 | the only fleet trained against a learned light (RL-H_0) |
| human | no agent cars |

**Sensing** (B1b): `default` is LightRL's halting count (SUMO halting, v < 0.1 m/s). `crawl` is the same light with the SAME weights, but its two "halting" features (and nothing else) are replaced by the count of vehicles with v < 2.0 m/s on the same served lanes. The reward is not used at evaluation.

## Configurations

Evaluation seeds 100–104; 5400 s per run, as in Q7b. Configs:
- 13 light settings (ACT; RL-H_t, RL-C50_t, RL-J_t for t = 0..3) × 6 fleets (L-ACT_0..3, L-RLH_0, human);
- plus RL-H_t with `crawl` sensing (4) × the same 6 fleets.

Total: 102 configs × 5 seeds = 510 SUMO runs, 3 lanes.

## Metrics per run

- whole-city mean time loss (all trips, unfinished included, as in Q7b), human-only and agent-only;
- finished and unfinished trips, teleports;
- fleet approach cost (the fleet's training objective) and its τ out-of-support share against its own published tmax;
- per light decision (every 5 s, served lanes): number of vehicles halting (v < 0.1), crawling (0.1 ≤ v < 2.0) and moving, split agent / human;
- HIDDEN-QUEUE share = crawling / (halting + crawling).

## SELF-CHECK (parity)

Every configuration that also exists in Q7b must reproduce Q7b's stored time loss and approach cost exactly (tolerance 1e-9): same index t = t′, default sensing, seeds 100–104. Those are ACT, RL-H, RL-C50 and RL-J, each × L-ACT_t and × human. If they do not match, the run is invalid and nothing is reported.

## B1 — exploratory readings (no thresholds)

- Regression r(L, F) = approach_cost(F | L) − approach_cost(F | ACT) on the 4 × 4 RL-H × L-ACT matrix, paired per seed.
- Two-way decomposition of r over light index, fleet index and interaction: the share of variance of the 16 cell means; seeds are the replicate.
- Whether susceptibility follows the light, the fleet or the pair.
- The same for RL-J and RL-C50.
- The (L0, F0) cell RL-H_0 × L-RLH_0 against RL-H_t × L-RLH_0 (t ≥ 1): a learned-light upgrade facing a fleet that learned against a different learned light.
- City time loss with the fleet vs light gain with human traffic, per cell (the coupled trade-off).

## B1b — registered predictions (hidden queue)

| | Prediction | Supported iff |
|---|---|---|
| HC-1 | The hidden-queue share among AGENT vehicles under RL-H_t × L-ACT_t′ exceeds that among HUMAN vehicles in the same runs. | Paired over the 16 cells × 5 seeds: the mean difference is > 0 and ≥ 14 / 16 cells are positive. |
| HC-2 | Crawl-aware sensing reduces the fleet's regression under RL-H. | Mean over the 16 RL-H × L-ACT cells of r(crawl) − r(default) < 0, with the two-level bootstrap (cells × seeds, 2000 draws, rng 0) upper bound < 0. |
| HC-3 | Crawl-aware sensing is near-identity for human traffic. | \|time loss(RL-H_t, human, crawl) − time loss(RL-H_t, human, default)\| ≤ 0.5 s/veh for every t. |
| HC-4 (reported) | Crawl-aware sensing changes city time loss with the fleet. | No threshold. |

Readings:
- HC-1 and HC-2 both supported → the light-side hidden queue is a real, repairable part of the harm. The repair is honest receiver-side input reconstruction with no retraining, i.e. the physical analogue of legacy-view emulation.
- HC-2 fails → the harm is not (mainly) hidden-queue sensing. The fleet-side τ support and objective mismatch remain.
- HC-3 fails → crawl sensing is not a pure repair; it changes the light for humans too.

## Scripts

- `scripts/CITY_xplay.py` — one config × seeds per call.
- `scripts/QUEUE_city_xplay_20261004.sh`
- `scripts/CITY_xplay_report.py`

Output: `research/city_sim/xplay_20261004/`. Smoke: 1 config, 1 seed, 600 s, through the report. Freeze hashes are appended below before launch.

## Freeze (02:45:25, before the panel; parity smoke RL-H_1 x L-ACT_1 seed 100 reproduced Q7b exactly: TL 34.3344…, cost 28.5542…)
* CITY_xplay.py 937d643102dfd58c
* QUEUE_city_xplay_20261004.sh a644e5e8c927b595
* CITY_env.py 02a297a56a12955d
* CITY_q7_cross_version.py a88f724ac9e02c1a

## Addendum A1 (04/10/2026 03:44 EDT, wake 2) — parity FAIL diagnosed; determinism amendment

**What happened.** The full panel (102 configs, `xplay_20261004/`, hash seed random) finished. The report stopped at the parity self-check: 156/160 rows identical, 4 different:

| Config | ΔTL (s/veh) | Δ cost |
|---|---|---|
| ACT × L-ACT_0, seed 100 | 1.7e-5 | 1.4e-5 |
| ACT × L-ACT_0, seed 101 | 2.2e-5 | 1.2e-5 |
| ACT × L-ACT_0, seed 102 | 6.9e-3 | 4.1e-3 |
| RL-H_0 × L-ACT_0, seed 102 | 0 | 9.3e-5 |

No B1/B1b statistic was computed. Disclosure: before this addendum I saw ~10 per-run progress lines in `run.log` (including agent/human hidden shares of a few runs).

**Diagnosis (measured, scratchpad reruns).** `CarRL.step` (scripts/CITY_env.py:112) iterates `list(self.agents)`, a Python `set` of vehicle-ID strings. Its order depends on PYTHONHASHSEED, which is random per process. The order changes the row order of the policy batch, hence last-bit float differences and rare near-tie argmax flips.
- Same hash seed → bit-identical results: PYTHONHASHSEED=0 run twice.
- Different hash seeds → different results: hash seeds 0 / 1 / 2.
- Q7b's stored rows are one draw of this jitter; this is not a bug in CITY_xplay.py.
- **Every Q7 / Q7b city number carries the same jitter.** Magnitude: see J below.

**Amendment (before any B1/B1b statistic).**
1. **Primary panel.** Rerun the same 102 configs with `PYTHONHASHSEED=0` into `research/city_sim/xplay_h0_20261004/`. It is deterministic, so a rerun reproduces it bit for bit.
2. **Jitter envelope J.** Rerun the 16 Q7b-existing fleet configs (ACT / RL-H / RL-C50 / RL-J × L-ACT_t, t = 0..3) for seeds 100–104 under PYTHONHASHSEED = 1, 2, 3, 4, into `xplay_jitter_20261004/h{k}/`. Then:
   - J_TL and J_cost = the maximum, over (config, seed), of the range across the 5 replicates (hash seeds 0–4).
   - Human-only configs have no CarRL and must be bit-identical.
3. **Amended parity self-check.**
   - Human-only rows: exact (1e-9).
   - Fleet rows: |h0 − Q7b| ≤ J for both TL and cost.
   - FAIL if any row exceeds this, or if a determinism re-run of 2 h0 configs is not bit-identical.
4. **Robustness.** HC-1 … HC-3 are evaluated on the h0 panel (primary) AND on the original random-hash panel. A verdict that differs between the two is reported as "jitter-sensitive".
5. **Predictions, thresholds and the B1 readings are unchanged.**

Future city scripts in this program run with `PYTHONHASHSEED=0` (or iterate agents in sorted order) and record it.
* QUEUE_city_xplay_h0_20261004.sh f9baa3db88e795eb (A1, launched 03:44:59)
