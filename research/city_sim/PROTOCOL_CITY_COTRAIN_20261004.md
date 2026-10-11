# PROTOCOL: staged learned pairs (B2), light–car co-training (B3) and the all-lights × all-fleets matrix (B3-X)

Written 04/10/2026 03:49 EDT (wake 2), before any B2/B3 training or evaluation. No B1/B1b statistic had been computed at this time (the B1 report is pending Addendum A1).

Context:
- `research/papers/audits/TWO_POPULATION_AUDIT_VERIFY_20261004.md` §5 (plan B0–B5);
- the user's order: co-train the light and car populations, and pair every light policy with every fleet policy.

## Novelty check (done before writing)

**Co-training lights and CAVs jointly is NOT new.**
- CoTV (arXiv 2201.13143, T-ITS 2023): cooperative DRL control of signals and CAV speed.
- HONEST-CAV (arXiv 2602.18740, IEEE IV 2026): VDN signals plus ML trajectory planning, on a 4×4 network at 60 % CAV.
- Neither tests cross-play, mismatched partners, or one population updating while the other is frozen.

**Cross-play and partner specificity are standard in zero-shot coordination,** but in symmetric games: Other-Play, FCP, SBRT (arXiv 2302.05063).

**The collision-free question here** is asymmetric and two-population, and is the city analogue of E3: two owners (city and fleet operator) update their policies independently.
- Does co-training buy pair performance at the price of partner specificity, i.e. upgrade fragility?
- Which training order (light first, fleet first, joint) leaves the most upgrade-robust pair?

## Populations

Same environment as Q7 / Q7b (`scripts/CITY_env.py`, grid4 static net, ρ = 0.5, training demand seeds 0–7, 3600 s episodes, the Q7 DQN; ε decays to 0.05 over 60 % of a population's own learning episodes).

**Every new process runs with PYTHONHASHSEED=0**, because of the set-order jitter found in xplay Addendum A1.

**B2, staged fleets.**
- L-RLH_t, t = 1..3: a fleet learns 120 episodes against the frozen RL-H_t (Q7's L-RLH_0 recipe; fleet DQN seed 13 + 100t).
- Together with the Q7 L-RLH_0 this gives four staged pairs S1_t = (RL-H_t, L-RLH_t): light first, then fleet.
- The opposite order already exists: S2_t = (RL-J_t, L-ACT_t), fleet first, then light.

**B3, co-training,** training index k = 0..3. Light DQN seed 1011 + 100k and fleet DQN seed 1013 + 100k are SHARED across arms (paired design).

| Arm | Schedule | Light reward |
|---|---|---|
| SIM-halt | both populations learn in every episode (independent learners), 120 episodes | −halting / 10 (as RL-H) |
| ALT-halt | alternating blocks of 20 episodes, light first; each population learns 120 episodes; the frozen one acts greedily | −halting / 10 |
| SIM-delay | as SIM-halt | −Σ over vehicles on the served lanes of (1 − v / v_allowed), / 10 (instantaneous time-loss rate; counts crawling cars) |

The light's OBSERVATION is the same in all arms (halting counts); only the training reward differs.

## B3-X: evaluation matrix (every light × every fleet)

**Lights (26):**
- ACT, FT;
- RL-H_t, RL-C50_t, RL-J_t (t = 0..3);
- SIM-halt_k, ALT-halt_k, SIM-delay_k (k = 0..3).

**Fleets (25):**
- human;
- L-ACT_t, L-FT_t, L-RLH_t (t = 0..3);
- SIM-halt_k, ALT-halt_k, SIM-delay_k (k = 0..3).

**Runs.** 650 configs × evaluation seeds 100–104, 5400 s, default sensing. Script `scripts/CITY_xplay2.py`: CITY_xplay's run with a generalized checkpoint resolver.

**SELF-CHECK.** Every config also present in the h0 panel must be bit-identical to it. Same script semantics and hash seed 0.

**Metrics** as in xplay:
- city / agent / human time loss;
- fleet approach cost and τ-OOS;
- hidden-queue counts.

## Registered endpoints

Uncertainty: two-level bootstrap over training index (4) × evaluation seed (5), 2000 draws, rng 0. "Own pair" means matched index (light_k with fleet_k; for S1 / S2, t with t).

| | Prediction | Supported iff |
|---|---|---|
| C-1 | Co-training improves the matched pair: city time loss of SIM-halt own pairs < S1 own pairs (RL-H_t, L-RLH_t). | Bootstrap upper bound of the mean difference < 0. |
| C-2 | Co-training creates partner specificity. For an arm's 4 × 4 matrix of city time loss over (light_k, fleet_k′), the specificity is Spec = mean off-diagonal − mean diagonal. Spec(SIM-halt) > 0. | Bootstrap lower bound > 0 (resampling training indices for both rows and columns jointly, and evaluation seeds). |
| C-2b | Co-trained pairs are more partner-specific than staged pairs: Spec(SIM-halt) > Spec(S1). | Bootstrap lower bound of the difference > 0. |
| C-3 | The time-loss reward helps the matched pair: city TL of SIM-delay own pairs < SIM-halt own pairs. | Upper bound < 0. |
| C-4 (reported) | Same differences for ALT-halt vs SIM-halt, and S2 vs S1. Light gain with human traffic for every learned light. | No threshold. |
| C-5 (reported) | Two-way decomposition of the 26 × 25 city-TL and fleet-cost matrices (light, fleet, interaction), and the interaction share inside each training family. | No threshold. |

**Readings.**
- C-1 and C-2 both supported → co-training trades upgrade robustness for pair performance. This is the multi-population analogue of E3's frozen-receiver problem: a co-trained light cannot be upgraded without retraining the fleet.
- C-2 fails → co-trained conventions are seed-robust in this environment, and independent upgrades are safe.
- C-3 supported → the halting reward is a measurable part of the light–fleet friction.

**Failure handling.**
- A training run that crashes is re-run once from scratch with the same seeds. If it crashes again, it is reported as missing and its index is dropped from every arm (paired design).
- Teleports are reported per run.

## Scripts

- `scripts/CITY_cotrain.py` — modes sim / alt / fleet-vs; reward halt / delay.
- `scripts/QUEUE_city_cotrain_20261004.sh`
- `scripts/CITY_xplay2.py`
- `scripts/QUEUE_city_xplay2_20261004.sh`
- `scripts/CITY_cotrain_report.py`

Output:
- `research/city_sim/cotrain_20261004/` (checkpoints and logs);
- `research/city_sim/xplay2_20261004/` (matrix).

Smoke: one 2-episode training run per mode (300 s episodes), then one evaluation config, before launch. Freeze hashes are appended below before launch.

## Freeze, training (03:51 EDT, before launch)

The smoke ran all four modes, 2–5 episodes of 300 s, in the scratchpad. It surfaced one change, made before the freeze: fleet checkpoints also store `tmax_late`, the published support over the fleet's last 20 % of learning episodes.

Reason: with a learning light, the early near-greedy random light keeps phases up to the whole episode, so the all-episode tmax is inflated. τ-OOS for co-trained fleets uses `tmax_late`; this is reported, not an endpoint.

* CITY_cotrain.py 9b53e6da0d37cc8c
* QUEUE_city_cotrain_20261004.sh 22ca6e6c3bf01b9b
* CITY_env.py 02a297a56a12955d
* CITY_q7_cross_version.py a88f724ac9e02c1a

## Run note N1 (03:52 EDT): process observation, not an outcome

**ALT-halt.** In the first light block the frozen fleet is the UNTRAINED greedy network, as the protocol specifies. That fleet gridlocks the city: about 2000 teleports per episode in episodes 0–2. SIM arms: 0 teleports.

The ALT arm runs as registered. Running processes are not stopped (standing rule), and ALT-halt is reported with this property stated.

If ALT-halt's light is degenerate, a corrected variant may be added by a dated addendum before its evaluation: ALTH-halt, whose first light block faces all-human traffic. It would be labelled exploratory.

## Freeze, evaluation (03:53 EDT, before launch)

Smoke: RL-H_1 × L-ACT_1, seeds 100–101, 5400 s, reproduced the h0 panel bit for bit (TL, cost, hidden shares, τ-OOS); FT × L-FT_2 also ran.

Per-vehicle tripinfo XML is temporary (`xplay2_20261004/tmp/`, removed after each run); the JSON rows are the artifact.

* CITY_xplay2.py 4f41f5664ebec111
* QUEUE_city_xplay2_20261004.sh 5323cb4b1de872a7
  - phase 1: 140 configs, existing checkpoints;
  - phase 2 waits for the training queue (PID 33018): 510 configs.
