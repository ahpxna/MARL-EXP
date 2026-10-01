# Four cheap checks (v2) — results, 27/09/2026

This file does not edit any ledger and has not been gated.

> **Corrected 27/09 after `research/papers/audits/MARL_CHEAP_V2_INDEPENDENT_AUDIT_20260927.md`.**
> All 8 audit findings were checked against the code and data and confirmed. The numbers below are
> unchanged; the readings are corrected.
> - `bid` is an offline feature ablation: bids were NOT transmitted and NOT charged. The collector
>   docstring and manifest wrongly call them charged; those files are left unedited so their hashes
>   still identify the producer.
> - `ceiling` is privileged current summaries (phase and approach totals), not the simulator state
>   and not an information ceiling.
> - Check 4 optimised the shared order AFTER the receiver budgets were drawn, and did not bound R.
> - Holdout used all-size labels in one scalar target scale.
> - Similar mean regret is not identical selection.
>
> Fixed reruns:
> - `scripts/MARL_cheap_checks_v3_train.py`, with a label-isolation test in
>   `tests/test_marl_cheap_checks_v3.py`;
> - the exact mechanism oracle `scripts/MARL_hetero_exact_oracle.py` under
>   `PROTOCOL_HETERO_v0.md`, preregistered.

## Setup

- **Evidence class:** oracle-labelled offline screening. The actor is frozen MP2 and each value is
  held-phase over H = 3 decisions, on a 3×3 grid. This is not learned MARL.
- **Producers:** new files, with no existing file modified:
  - `scripts/MARL_cheap_checks_v2.py` (collector);
  - `scripts/MARL_cheap_checks_v2_train.py` (trainer).
  - Both import the other session's `MARL_cheap_screen.py` / `MARL_cheap_pilot.py` without edits.
- **Data:** `research/marl_budget/cheap_checks_v2_20260927_171810/data`.
  - 192 snapshots in 16 episodes, the same seeds and splits as the pilot (96/48/48).
  - manifest COMPLETE, table sha 0f812364…
- **Models:** `…/models/report.json`, COMPLETE.
  - 3 initialisation seeds, 150 epochs, hidden 64.
  - Every method's checkpoint is chosen by validation decision regret at training budgets.
  - The critic loss is centred within each subset-size layer.
- **Metric:** mean episode regret. Waiting-count units; the homogeneous k-set spread is about 49.6.
  Each cell below is the mean over 3 seeds.

## Checks 1–3: learned selectors (test = held-out episodes; train = training episodes)

| features / budgets | cached-queue prefix | critic chain (one priority) | critic per-budget table | critic chain + R1 | direct budget net | score prefix → +R1 (critic) | oracle R1 of critic chain |
|---|---|---|---|---|---|---|---|
| public, all k: test | 24.45 | 25.65 | 25.74 | 25.74 | 23.43 | 25.82 → 25.17 | 4.22 |
| public, all k: train | 20.98 | 4.75 | 4.70 | 4.72 | 6.70 | 7.43 → 4.96 | 0.40 |
| + fresh-bid feature ablation (not sent, not charged), all k: test | 24.45 | 25.03 | 24.84 | 24.85 | 23.45 | 25.86 → 24.61 | 4.28 |
| + fresh bids, all k: train | 20.98 | 8.06 | 8.06 | 8.04 | 6.13 | 8.02 → 7.10 | 0.98 |
| privileged current summaries (ORACLE; was "ceiling"), all k: test | 24.45 | 23.78 | 23.81 | 23.84 | 23.94 | 26.16 → 24.38 | 4.41 |
| ceiling, all k: train | 20.98 | 5.64 | 5.65 | 5.64 | 4.65 | 10.62 → 6.12 | 0.39 |
| public, train k∈{2,4,6} → eval {3,5,7}: test | 25.35 | 28.04 | 27.94 | 28.05 | 26.49 | — | 5.56 |
| same, train contexts | 22.92 | 9.48 | 9.38 | 9.45 | 7.39 | — | 1.28 |
| bids, holdout k: train contexts | 22.92 | 8.83 | 9.02 | 8.97 | 4.44 | — | 1.24 |
| ceiling, holdout k: test | 25.35 | 27.37 | 27.09 | 27.05 | 25.53 | — | 6.04 |
| ceiling, holdout k: train contexts | 22.92 | 5.28 | 5.30 | 5.31 | 2.52 | — | 0.46 |

**Check 1, privileged current summaries.** Adding every agent's current phase and approach totals
(oracle) does not move held-out regret.
- Test: 23.8–23.9, against the public heuristic's 24.45 and the oracle's 4.4.
- Train is fitted: 4.6–5.6.

This shows a generalisation gap. Its cause is NOT identified; candidates include limited independent
contexts, architecture or optimisation, missing predictive features (vehicle-level state is absent),
and distribution shift. It does not show data scarcity, and it does not rule the information rule in
or out. The test panel has only 2 traffic seed IDs.

**Check 2, fresh-bid feature ablation.** Adding a 1-byte fresh summary per agent as a feature does
not help either: test 23.45–24.84. This is not a paid-bid algorithm comparison.

**Check 3, unseen budgets.** The single-priority advantage is not observed. On training contexts at
held-out budgets, the direct budget-conditioned network interpolates as well as or better than the
priority derived from the critic:

| features | direct net | critic priority |
|---|---|---|
| public | 7.39 | 9.48 |
| bids | 4.44 | 8.83 |
| ceiling | 2.52 | 5.28 |

On held-out episodes every learned method is worse than the heuristic.

The comparison of 6.7 (all-k) with 7.4 (holdout) changes both the training and the evaluation
budgets, so it does not measure the cost of withholding budgets. v3 evaluates both regimes on the
same k = 3,5,7 records. The v2 holdout also used all-size labels in its target scale (22.99 against
22.85). v3 removes this and tests the removal. The table shows no observed priority advantage for
these models; it does not establish a general advantage of budget-conditioned networks.

**Across all configurations:**
- critic chain, critic per-budget table and critic chain + R1 have similar MEAN regret (largest
  spread 0.324). This does not show identical selections, zero nesting cost per context or budget,
  or no tail penalty. The chain minimises the SUM of predicted regret over k, not the worst-k
  regret. v3 saves every decision and adds a minimax chain.
- Revision helps only a WORSE score: score prefix → +R1 improves by 0.65–1.8 on test and 0.9–4.5 on
  train. It never beats the critic's own per-budget table by more than noise.

## Check 4: heterogeneous receivers on one broadcast stream (oracle)

Each receiver draws its own budget in 1–7, and the shared order is then optimised FOR THAT drawn
vector. This is a budget-aware shared order, not an order prepared before the reveal. The value is the
held-phase rollout value: minus the SUM of waiting counts at 3 decision boundaries. It is not unique
vehicles or delay.

| quantity | value | on reference scale 49.6* |
|---|---|---|
| best-found (budget-aware) shared order vs heuristic shared order | +26.0 | 0.53 |
| unrestricted per-receiver sets vs best-found shared order | +4.8 (positive in 95/192 snapshots) | 0.10 |

\* 49.6 is the homogeneous global-subset spread, a different feasible family. It is a labelled
reference scale, not the available heterogeneous benefit.
| full communication vs none | +5.5 (episode range −11.6 … +19.4) | — |

Both sides are heuristic searches: transposition local search from two starts, and coordinate ascent
from the best shared profile. The +4.8 is neither a lower nor an upper bound on the gap between the
optima. The private search has no R bound and no patch cost, so this is NOT a bounded-revision
result. The exact, bounded-R, prepared-before-reveal version is `PROTOCOL_HETERO_v0` plus
`MARL_hetero_exact_oracle.py`.

## What this decides

1. Under PROTOCOL_v1 the three candidate advantages of prepared priority plus revision all fail on
   this panel:
   - latency: see LATENCY_PREMISE_CHECK;
   - generalisation to unseen budgets: check 3;
   - quality given a critic: no observed mean-regret difference.

   The revision mechanism has no empirical support in the global-budget protocol.
2. Whether the mechanism has a home where nesting is forced (one stream, heterogeneous receivers) is
   NOT established here. It is tested by the preregistered exact oracle (PROTOCOL_HETERO_v0).
3. No learned selector here generalises to held-out episodes. The cause is unresolved. A blind 10×
   rerun of the global-subset learner would not test the heterogeneous mechanism, and it is not run.
   A learning curve is run only on the mechanism's own objective, and only if the oracle supports it,
   with new independent traffic seeds and a fresh test panel.

## Limits

- Frozen MP2 actor and held-phase short-horizon value.
- Tiny MLPs, 96 training contexts.
- 3 initialisation seeds, which are not actor-training seeds.
- One grid, two loads.
- Check 4 uses heuristic searches.
- Nothing here is a theorem.
