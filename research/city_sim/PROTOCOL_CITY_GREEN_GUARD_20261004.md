# PROTOCOL: L4, in-support reaction repair of a frozen fleet (green-release guard)

Written 04/10/2026, 04:47 EDT (wake 3). Written after B4F (city ledger C-14) and before any L4 panel run.

## Motivation (from C-14)

The B4F support gate removed about 70 % of the city-level harm, but FB-2 failed. The residual agent regression is +10 … +21 s/veh and lies in-support (RL-C50: +11.6 with no OOS). The τ-clip input repair did nothing.

**Hypothesis H-green.** The frozen fleet's harmful reactions happen mostly while its head is GREEN: it brakes for a switch it expects from ACT's hazard of phase ending. Its eco-approach on red is not the problem.

**Repair (iii-type, on the frozen side).** Release the car to SUMO's driver model whenever its head is green; keep the policy on red / yellow. `green+oos` also releases out-of-support red / yellow (the B4F rule).

**Not a no-op under ACT.** ACT greens are in support, so the guard's cost in the training environment is measured (GG-4).

**Prior art.** This is a rule-based fallback, Simplex-style. It is a baseline-class mechanism; the claim, if any, is the measured locus.

## Disclosure

One smoke seed was seen before this protocol:
- RL-H_0 × L-ACT_0, seed 100, `green+oos`: city TL 23.27 (agent 23.86, human 22.75), released on 31 909 / 70 115 decisions;
- plain city TL 50.92; B4F fallback 29.56; ACT with the plain fleet 24.31.

`none` mode is bit-identical to the h0 row (ACT × L-ACT_0, seed 100).

## Configurations

`scripts/CITY_xplay_guard.py`, PYTHONHASHSEED=0, 5400 s, ρ 0.5.

**SELECT** (traffic 100–104): 13 lights (ACT, RL-H_t, RL-C50_t, RL-J_t) × L-ACT_t′ (t′ = 0..3) × guards {none, green, green+oos}. 156 configs.

**TEST** (traffic 200–209). New demand from the identical generator: regenerating seed 100 reproduced the stored file vehicle for vehicle. Configs: (ACT, RL-H_0..3) × L-ACT_0..3 × {none, green+oos}. 40 configs.

## Endpoints

Bootstrap: cells × seeds, 2000 draws, rng 0. "ACT baseline" = ACT with the plain (`none`) fleet of the same index, same seeds.

| | Prediction | Supported iff |
|---|---|---|
| GG-1 | `green+oos` lowers the agent regression under RL-H vs `none` | Mean over 16 cells of the agent-TL change < 0, upper < 0 |
| GG-2 (SELECT) | With `green+oos` the light upgrade becomes a city gain | City TL(RL-H_t, L-ACT_t′, green+oos) < ACT baseline in ≥ 12/16 cells |
| GG-2T (TEST, confirmatory) | GG-2 on fresh traffic 200–209 | Same rule, ≥ 12/16 |
| GG-3 | The in-support harm under RL-C50 is reduced | Mean agent-TL change (green+oos − none) over 16 RL-C50 cells < 0, upper < 0 |
| GG-4 | The guard keeps the fleet's benefit in its training environment | Under ACT (4 fleets × 5 seeds): agent TL change (green+oos − none) ≤ +0.5 s/veh, and agent fuel change ≤ +2 % |
| GG-5 (reported) | — | `green` vs `green+oos`; released share; human TL; fuel; RL-J; teleports; unfinished |

**Readings.**
- GG-1, GG-2 and GG-2T supported → a reaction repair at the frozen fleet's green phase, with no retraining and no messages, turns a harmful light upgrade into a city gain. Together with C-14 (input repair ✗) this answers "observation or reaction?" for the light-upgrade direction: reaction.
- GG-4 fails → the repair costs the fleet its own benefit, and the trade-off must be reported, not hidden.

## Scripts

- `scripts/CITY_xplay_guard.py`
- `scripts/QUEUE_city_green_guard_20261004.sh`
- `scripts/CITY_green_guard_report.py` (written before the report is run)

## Freeze (04:48 EDT, before the panel)

* CITY_xplay_guard.py 66ba56fa74ed643b
* QUEUE_city_green_guard_20261004.sh beccd1e3215a9b38

Runs as spool job `010_L4_green_guard` (`scripts/RUN_spool_20261004.sh`, sequential, OMP_NUM_THREADS=1, 4 lanes). The spool starts after the B3-X queue (PID 33671) exits.

OMP_NUM_THREADS=1 was checked first: RL-H_0 × L-ACT_0, seeds 100–102, reproduced the h0 rows bit for bit.
