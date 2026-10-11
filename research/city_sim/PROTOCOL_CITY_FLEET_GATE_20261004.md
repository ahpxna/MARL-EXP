# PROTOCOL: fleet-side support gate (B4F). Can the car population survive a light upgrade without retraining?

Written 04/10/2026 04:0x EDT (wake 2), after the B1/B1b report (city ledger C-12) and before any gated run.

## Motivation (from C-12; exploratory evidence, not a test)

The RL-H × L-ACT regression is set by the FLEET: variance share 0.83. τ-OOS tracks it (Spearman +0.74). L-RLH_0, trained against a learned light, is robust.

**Mechanism hypothesis H-phantom.** Under ACT (maxDur 50) a green that has lasted about 50 s always ends. An ACT-trained fleet can learn "long green ⇒ imminent yellow ⇒ brake". Under a learned light, greens last up to about 200 s, so the fleet brakes for a yellow that does not come. Fleets differ in how they extrapolate beyond τ = 50; this is a seed lottery: L-ACT_0 is fragile, L-ACT_3 is not.

**Novelty.** OOD gatekeepers and Simplex fallbacks are known (e.g. arXiv 2510.21254; the Simplex architecture). What is new is the setting:
- a cross-population version update;
- a gate defined by the fleet's OWN published support (`tmax`, already in every checkpoint);
- the guarantee that the gate is an exact no-op in the fleet's training environment.

It is the car-side dual of E3's receiver-side legacy-view emulation and fallback gates.

## Arms (no retraining; existing L-ACT_t checkpoints)

For an agent car within ZONE of its next light, with observation τ = time in phase:
- `lim` = tmax[green] if the head shows green, else tmax[red], using the fleet's published support;
- the gate fires iff τ > `lim`.

| Gate | When it fires |
|---|---|
| `fallback` | The car is released to SUMO's driver model for that second (`setSpeed(-1)`); no action. Its stage cost is recorded as 1 + IDLE·[v < 0.1] at the decision. |
| `clip` | The policy acts on the observation with τ replaced by `lim` (input clamp: the nearest in-support value). |
| `none` | The plain fleet (identical to CITY_xplay2). |

## Configurations

- Lights: ACT, RL-H_t, RL-C50_t, RL-J_t (t = 0..3).
- Fleets: L-ACT_t′ (t′ = 0..3).
- Gates: fallback, clip.
- Evaluation seeds 100–104, 5400 s, PYTHONHASHSEED=0.

104 configs, 520 runs. Plain rows come from xplay2 phase 1 (same script semantics). Script `scripts/CITY_xplay_gate.py`; output `research/city_sim/xplay_gate_20261004/`.

## SELF-CHECKS

| | Check | Fail condition |
|---|---|---|
| G-0 identity | Under ACT, every gated row equals the plain xplay2 row bit for bit, and the gate fired 0 times | Any difference → the gate is not a no-op in the training environment; the run is invalid. |
| G-0b | Under RL-H_t, the gate fires > 0 times | Otherwise the test cannot discriminate. |

## Registered endpoints

Metric: agent-car time loss (tripinfo), so that it does not depend on the gate's cost bookkeeping. Agent regression rA(L, F) = agentTL(F | L) − agentTL(F | ACT), paired per seed. Uncertainty: two-level bootstrap over cells × seeds, 2000 draws, rng 0.

| | Prediction | Supported iff |
|---|---|---|
| FB-1 | The fallback gate reduces the agent regression under RL-H. | Mean over the 16 RL-H_t × L-ACT_t′ cells of rA(fallback) − rA(none) < 0, bootstrap upper < 0. |
| FB-2 | With the fallback gate, the light upgrade becomes a city-level gain. | City TL(RL-H_t, L-ACT_t′ + fallback) < city TL(ACT, L-ACT_t′, plain) in ≥ 12/16 cells. |
| FB-3 | The gate does not hurt human drivers. | Mean human TL change (fallback − none) over the 16 RL-H cells ≤ +0.5 s/veh. |
| FB-4 (reported) | The same for RL-C50 and RL-J; the clip gate; the share of agent decisions gated; per-fleet fragility vs gate effect. | No threshold. |
| FB-5 (reported, H-phantom probe) | Offline, with no simulation: each fleet network's brake propensity on synthetic GREEN observations with τ ∈ (50, 200] vs τ ∈ [0, 50]; Spearman over the 4 fleets with their mean r. | No threshold (n = 4). |

**Readings.**
- FB-1 and FB-2 supported → the fragility is out-of-support extrapolation. A zero-retraining, zero-communication fleet-side gate, exact in the training environment, removes it. This is the two-population counterpart of legacy-view emulation.
- FB-1 fails → the regression is not (only) OOS extrapolation, and the in-support behaviour of the fleet itself is mismatched.
EOF
echo ok
## Freeze (04:04 EDT, before the panel)

**Smoke** (scratchpad):
- G-0 holds on ACT × L-ACT_0, seeds 100–101: the gate fired 0 / 69 990 and 0 / 78 613 times; the rows are bit-identical to the h0 panel.
- Under RL-H_0 × L-ACT_0, seed 100, the gate fired on 4 110 / 79 400 decisions.

**Disclosure.** That one smoke seed was seen before the panel:

| Gate | City TL | Agent TL | Human TL |
|---|---|---|---|
| plain | 50.9 | 69.5 | 34.6 |
| fallback | 29.6 | 35.1 | 24.7 |
| clip | 48.4 | — | — |

The predictions above were written before the smoke and are not changed.

* CITY_xplay_gate.py 838c212a286d52c4
* QUEUE_city_xplay_gate_20261004.sh (hash below)
* QUEUE_city_xplay_gate_20261004.sh e4e2f8a1c6958775
