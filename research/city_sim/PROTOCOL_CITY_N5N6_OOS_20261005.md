# PROTOCOL N5 / N6: out-of-sample commitment selection on the H3 branches (registered 05/10 ~00:35, before any per-seed split was computed)

**Hypotheses** (`METHOD_HYPOTHESES_NIGHT_20261004` §2; night plan):
- **N5:** utility ≠ sensitivity. A rule that uses cost / outcome information picks better commitments than a sensitivity-only rule.
- **N6:** cheap timing. Commitments are cheap when the base policy would switch anyway ("switch, then announce"), and expensive when they force a switch or a hold against it.

**Data:** the existing H3 branches (C-96), `m3h3_20261004/h3_results.json` plus `br/*_veh_s*.npz`.
- 96 situations = k ∈ {0, 1} × seeds 0–3 × 12 (6 eligible + 6 random ticks).
- Options Z / H5 / H10 / H15 / P, plus I0.
- No new simulation. Offline, one process.

**Why out of sample:**
- One intervention changes 640–900 of 1800 vehicles (chaos).
- I0 is one draw per (k, seed) episode, shared by its 12 situations.
- The oracle-best share is the same on random and eligible ticks.
- So the registered H3 "YES" can be max-of-noise. Only realized gains of rules fixed BEFORE seeing the evaluation seeds count.

## Estimand (deployment-consistent)

For situation s and option o:
- g(s, o) = −(full-episode agent fuel % vs I0) — positive = saving;
- ΔTL_city(s, o) = full-episode city TL change;
- ΔTL_agent(s, o) = (sum of agent TL changes) / (number of agents in the I0 episode); ΔTL_human likewise. Fixed denominators: the affected cohort is NOT used.
- Feasible(s, o) iff all three TL changes ≤ +0.5 s/veh.
- g(s, I0) = 0.

A rule maps the causal features of s to one option in {I0, Z, H5, H10, H15, P}. Infeasible choices are evaluated as chosen; they are not filtered after the fact.

**Causal features (all available at t\* without the future):**
- near (fleet vehicles within 200 m);
- qgap = Q(switch) − Q(keep), and |qgap|;
- rl_action;
- eligible (the RPC receiver trigger);
- hD;
- t / 3600;
- k.

## Rules (fitted on the training fold only)

| Rule | Definition |
|---|---|
| I0 | never intervene |
| RANDOM | uniform over the 5 options; its value is the exact mean over options (no sampling) |
| FIXED | the single option with the best training mean of g, used everywhere |
| SENS (sensitivity-only) | intervene with the training-best option iff near ≥ τ; τ from the training quantiles {0, .25, .5, .75} |
| COST (cost-only) | intervene iff \|qgap\| ≤ τ (cheap deviation for the light), with the training-best option for that subset; τ as above |
| RC (receiver + cost) | 2 × 2 cells: near ≥ training median × \|qgap\| ≤ training median. Per cell, the training-best option, or I0 if no option has a positive training mean |
| LEARN | ridge regression per option of g on the standardized features (λ = 1). Choose the argmax prediction if > 0, else I0 |
| STRAT (N6) | per rl_action stratum, the training-best option, or I0 |

## Cross-fitting and statistics

- **Folds:** A = train seeds {0, 1}, test {2, 3}; B = the reverse. Each situation is scored by the rule fitted on the other fold. Pooled out-of-sample (OOS) n = 96.
- **Contrasts:**
  - rule − I0;
  - rule − RANDOM (situation-wise; removes the shared I0 draw);
  - LEARN / RC − SENS;
  - COST − SENS;
  - RC − COST;
  - STRAT − FIXED.
- **Uncertainty:** cluster bootstrap over the 8 (k, seed) episodes (4000 draws, percentile 95 %). Per-cluster signs are reported too.
  - With 8 clusters the interval is rough. A NO is "not detected in this sample", not impossibility.
- **Noise floor (descriptive):** a within-situation permutation of option labels (2000 draws). It gives the null distribution of max_o mean g, and the p-value of the observed best fixed option.

## Checks

- **KN6-0:** in rl_action = 1 situations, P is applied as Z (code); their outcomes must be identical (determinism).
- **KN5-1:** every situation has all 6 branches, and the I0 denominators exist.
- **KN5-2:** fold separation. The test seeds never enter fitting (asserted in code).

## Decisions (registered)

- **OOS OPPORTUNITY:** YES iff LEARN or RC has a pooled OOS gain vs RANDOM with cluster-bootstrap lower bound > 0. Otherwise NO, and the commitment-learner path (method B, HYP §4) stops for this option family.
- **N5:** SUPPORTED iff (LEARN or RC) − SENS has lower bound > 0. If COST − SENS > 0 (lower bound > 0) while RC − COST includes 0, the reading is "cost-only suffices" (no receiver-specific claim). REJECTED if no rule beats SENS.
- **N6:** SUPPORTED iff STRAT − FIXED has lower bound > 0 AND STRAT picks a switch-now option (Z / P) in the rl_action = 1 stratum. Descriptive: per-stratum means of Z, H5–H15 and P.

**Scope:**
- One fleet per light, 8 episodes, single interventions only (N7 tests accumulation).
- The option menu is the H3 menu; this is not a statement about all commitment designs.
