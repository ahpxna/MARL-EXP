# Step 3 pilot: learned bounded repair on the heterogeneous-receiver objective — results, 27/09/2026

This file does not edit any ledger and has not been gated. Frozen MP2 actor, held-phase value with
H = 3. This is not learned MARL.

> **Corrected 27/09 after `research/papers/audits/MARL_SCOPE_AFTER_CHEAP_TESTS_20260927.md`.** The
> numbers are unchanged; five readings are corrected.
> - "Search error 0" means only this: uncapped search scored by the TRUE value attained exact R1 on
>   this panel. It does not show that ν or ζ is small for search guided by the LEARNED critic, which
>   can visit a different candidate set. Nor does it hold at every cap. Mean regret and MSE are not
>   the uniform ε of `LeanMarlProfileSearchV1`, and the pilot does not instantiate that bound.
> - `direct_unrestricted` is a coordinate single-swap search with the SAME critic, not a separately
>   trained budget-conditioned selector.
> - The pass limit is the same, but equal call counts are NOT enforced: 423/4,608 paired runs differ,
>   by up to 48 calls, with close means (132.3 vs 132.0).
> - The public critic input omitted legal information: each receiver's own delivery history. The
>   scheduler can reconstruct it from what it transmitted and to whom. See the mirror diagnostic.
> - Seeds 61–64 have now informed development. They are no longer an untouched test panel.
> - The proposed joint-action control cannot, on its own, attribute the failure to the information
>   rule. f_x(S) = Q_H(x, a_x(S)) holds within one snapshot. Across snapshots, equal actions give
>   different returns.

## What was built (contract of MARL_HETERO_STEP3_DECISION §A–D)

- **Transport:** `envs/external/cityflow_hetero.py`.
  - One broadcast stream, per-receiver capacities k_i ~ U{1..7}.
  - Each receiver decodes only S_i, and its cache is updated only for decoded packets.
  - The scheduler caches every transmitted packet.
  - Bytes come from the single shared cost function.
- **Selector:** `models/marl_hetero_selector.py`.
  - Only z (paid cache and time), the base order, K and a learned critic enter.
  - Cost is min(patched, explicit) accounted bytes.
  - Search is a deterministic, bounded coordinate search.
  - Over-cap candidates are rejected before scoring.
  - `learned_R1` (moves within one replacement of the prefix) and `direct_unrestricted` (single swaps
    from the current set, no radius) get the same number of evaluator calls.
- **Tests:**
  - `tests/test_marl_hetero_selector.py`, 7/7 PASS: legality under caps and radius, equal move
    counts, cost = min, search never beats exact, inference ignores labels, infeasible prefix
    reported.
  - Collector smoke: live actor actions equal the diagnostic counterfactual actions for a non-prefix
    profile with the same old cache (contract A).
- **Data:** `research/marl_budget/hetero_pilot_20260927_181207/`.
  - Labels (`labels/`, sha 82e3b497…):
    - 96 train contexts (traffic seeds 41–48) and 24 val contexts (seeds 51–52), both new;
    - 4 capacity vectors per context;
    - about 180 labelled profiles per (context, K).
  - Test (`test_eval/`, sha a4e59d28…): seeds 61–64, 48 snapshots × 4 K × 4 caps, evaluated once.
- **Critics:** one per (information, seed), shared by both searches.
  - public (deployable) and privileged current summaries (diagnostic);
  - seeds 0/1/2, checkpoint selected by validation decision regret.

## Results (test panel, 8 episodes; gain over the SAME base prefix, per-episode mean)

References:

| reference | gain | episodes > 0 |
|---|---|---|
| exact R1 optimum (uncapped) | +25.13 | 8/8 |
| exact private optimum | +27.16 | 8/8 |
| search error of the bounded search scored by the TRUE value | 0.00 in every case | — |

The search is not the bottleneck.

| method | cap +0 B | cap +28 B | cap +56 B | no cap |
|---|---|---|---|---|
| oracle-scored R1 search | +0.56 (5/8) | +16.60 (8/8), +13 B | +24.69 (8/8), +22 B | +25.13 (8/8) |
| **learned_R1, public critic** | −0.01 | +0.89 (4/8), +21 B | +1.39 (4/8), +42 B | +1.31 (4/8), +49 B |
| direct_unrestricted, public critic | +0.07 | +0.94 (5/8), +21 B | +0.46 (4/8), +42 B | +0.73 (4/8), +50 B |
| learned_R1, privileged-summary critic | −0.02 | −0.43 | −0.16 | −0.16 |
| direct_unrestricted, privileged critic | −0.04 | −0.35 | +0.19 | +0.16 |

Paired learned_R1 − direct_unrestricted, same critic, calls and cap: between −0.35 and +0.93, with
4–6 of 8 episodes positive. There is no consistent difference.

Validation (before test):
- On validation the critics' argmax among R≤1 candidates has regret 15.5–18.0. Keeping the prefix
  has regret 16.5.
- Train regret is 0.6–1.5 when training runs long. Three of the six selected checkpoints are
  epoch 0.
- The critics memorise the training panel and do not generalise.

## Reading

- The mechanism is there, and it is easy to search: one patch per receiver is worth +25, and the
  bounded search finds the R = 1 optimum exactly when it is scored by the true value. With +28 B
  it still reaches +16.6.
- The learned critic captures about 5% of that (+0.9 to +1.4, positive in half the episodes) and
  spends 20–49 extra bytes to do so.
- Privileged current summaries do not help.
- Learned repair is not distinguishable from the direct budget-aware search with the same critic.
- The pilot therefore does NOT show that a legal-information selector can exploit the headroom at a
  useful cost.

**Stop rule (MARL_HETERO_STEP3_DECISION, schedule 5).** The critic only memorises. Diagnose
representation, optimisation and search before collecting more.
- Search is cleared: its error is 0 with the true value.
- What remains open is representation and optimisation versus information.

## Cheapest diagnostics before any expansion

1. **Action-informed critic (privileged diagnostic).**
   - The value of a profile depends on the state only through the joint action it induces, and
     that joint action depends on the FRESH payload contents.
   - Train a critic on (privileged summaries, induced joint action).
   - If it generalises, the barrier is that a public scheduler cannot infer from stale packets what
     the actors will do with fresh ones. That is an information-rule problem, and it points to a
     paid fresh-bid protocol (SchedNet-style) as the legal fix.
   - If it does not generalise, the value itself is hard to learn at this scale.
2. **Simple regularised learners** (ridge or k-NN on the same inputs) as a check on optimisation.
3. **A 192-context point**, only if 1 or 2 shows validation signal.

## Theory status

- `work/p13_conjectures/LeanMarlProfileSearchV1.lean` compiles with standard axioms and 0 sorry. It
  is not gated. It gives the finite-search bound V_{R,B} − f(Ŝ) ≤ 2ε + ν + ζ on the actual profile
  space, plus the private decomposition.
- The pilot measures ν ≈ 0 (search) and a large ε (evaluator).
- T1 (a single k-subset theorem) is still not instantiated by this profile space.
