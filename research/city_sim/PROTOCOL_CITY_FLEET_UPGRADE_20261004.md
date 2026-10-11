# PROTOCOL — F-branch (fleet upgraded, light frozen) and V3 (reward-v2 fleets)

Written 04/10/2026 04:51 EDT (wake 3), before any training. Program `research/papers/audits/TWO_POPULATION_EXPERIMENT_PROGRAM_20261004.md` §F and §V. This is the direction review R1 chose.

## Pairs (L0, F0) where the light learned with that fleet; policy seeds 0–1 are the SELECT seeds

| Pair | L0 | F0 | How it was learned |
|---|---|---|---|
| P-J_t | RL-J_t | L-ACT_t | Light trained against the frozen fleet |
| P-C_k | SIM-halt_k light | SIM-halt_k fleet | Co-trained (B3) |

## Upgraded fleets F1 (`scripts/CITY_fleet_upgrade.py`; each trained against the frozen L0; PYTHONHASHSEED=0)

| F1 | Recipe | Seed |
|---|---|---|
| FTv1 | Fine-tune F0, 60 episodes, reward v1 (data-only upgrade) | 2013 + 100·idx |
| FTv2 | Fine-tune F0, 60 episodes, reward v2 (realized idle, ledger C-13): the vendor fixes the reward | 2013 + 100·idx |
| NEWv2 | From scratch, 120 episodes, reward v2 | 3013 + 100·idx |

12 trainings: 2 P-J + 2 P-C pairs × 3 recipes.

**V3.** L-ACT-v2_t, t = 0, 1: from scratch against ACT with reward v2 and the SAME DQN seeds as L-ACT_t (13 + 100t). It isolates the reward change. 2 trainings.

## Evaluation

Spool job 030, `scripts/CITY_eval2.py`, SELECT traffic 100–104 and TEST 200–209.

| Fleet | Evaluated under |
|---|---|
| F0, each F1 | Its L0 |
| F0, each F1 | ACT |
| V3 fleets | ACT and RL-H_0..3 |
| human-only | Each L0 |

Metrics:
- city, agent and human TL;
- agent and human fuel;
- unfinished, teleports;
- the light's own reward (mean halting per decision);
- phase-duration histogram.

## Registered endpoints

| | Statement | Rule |
|---|---|---|
| U-1 | Which F1 is an upgrade (defines the panel, not a hypothesis) | Agent TL under L0 below F0 by ≥ 0.5 s/veh, seed mean on SELECT. Only qualifying (pair, F1) enter U-2 / U-3. If none qualifies, the F-branch is reported empty. |
| U-2 | **Asymmetry prediction**: a fleet upgrade does NOT materially hurt the frozen light's other users | For qualifying (pair, F1): human TL(F1) − human TL(F0) under L0 ≤ +0.5 s/veh in ≥ 3/4 of them (SELECT, then TEST). Reading with C-12 / C-14: lights are robust to fleet changes, fleets are fragile to light changes. |
| U-3 | Does the upgrade help the city? | City TL(F1) < city TL(F0) under L0 (two-level bootstrap upper < 0). Reported per F1 recipe. |
| V3-1 | Reward v2 removes the command loophole | L-ACT-v2_t under ACT: realized-idle decisions avoided by command ≤ 0.2 (v1: 0.76–0.997), measured with `CITY_cmd_realized`'s logic |
| V3-2 | The fragility is not caused by the idle loophole | L-ACT-v2_t still has a positive agent regression under RL-H (mean over RL-H_0..3 > +2 s/veh in ≥ 1 of 2 seeds) |

**If U-2 FAILS** (the frozen light's other users ARE hurt), then F2 (observation adapters at the light) and F4 (light fallback / fleet discharge guard) are run on exactly the failing pairs. The 2×2 is then complete.

**If U-2 holds,** F2 / F4 are reduced to one confirmation pair, and the paper's two-population result is the asymmetry plus the reaction repair (C-14 / L4).

## Spool jobs

- `020_F0_train`: 14 trainings, 4 lanes.
- `030_F1_eval`: written after `CITY_eval2.py` is smoked.
* CITY_fleet_upgrade.py b4e8b6e47ea52f9f (smoke: ft v2 vs RL-J:0, new v2 vs ACT, ft v1 vs SIM-halt:0; 2 × 300 s episodes; weights change; scratchpad)
