# Bounded learner diagnostic (MARL_SCOPE_AFTER_CHEAP_TESTS) — results, 27/09/2026

This file does not edit any ledger and has not been gated. Frozen MP2, held-phase H = 3. Only TRAIN
and VALIDATION data were used; seeds 61–64 were not read.

> **Corrected 27/09 after `research/papers/audits/MARL_HETERO_DIAGNOSTIC_INDEPENDENT_AUDIT_20260927.md`.**
> All five points were checked and confirmed. The v1 numbers below reproduce, but v1 is NOT a
> conclusive test of selective revision.
> 1. **Tie bug.** `select_eval` compared the winning raw prediction with absolute 0 instead of
>    anchoring the prefix at 0, and ties did not favour the prefix. It could pick a harmful edit
>    whose score was tied with the prefix.
> 2. **No threshold was selected.** This file says "model and threshold selection"; in fact only the
>    epoch and λ were selected. The threshold was fixed at 0 and there was no never-edit option.
> 3. **Ridge explanation.** "Predictions nearly tied, ties do not favour the prefix, widening the
>    grid only moves toward never-edit" was NOT measured. No margins or coefficients were saved.
> 4. **Privileged control.** It adds summaries AND both joint actions together, so it "supports
>    actor-response prediction as one candidate bottleneck". It does not identify THE barrier. Its
>    gain is concentrated at headway 8 (+12.3 to +13.3) against headway 16 (+0.5 to +1.5), from 2
>    traffic seed IDs × 2 loads.
> 5. **Scope.** Selection is a candidate-set argmax over about 181 stored candidates, not the
>    deployed search. About 60% of non-prefix candidates have exactly zero gain, and about 59%
>    induce the prefix's joint action.
>
> The corrected diagnostic is `scripts/MARL_hetero_diag_train_v2.py`: anchored scores,
> prefix-favouring ties, and an inner-selected no-edit threshold including never-edit. Results are
> in HETERO_DIAGNOSTIC_V2_RESULTS_20260927.md.

## What was done, as the audit specified

1. **Legal receiver history.**
   - `models/marl_receiver_mirror.py` (pure class) and `envs/external/cityflow_hetero_mirror.py`
     (a subclass in a new file, so earlier artifact hashes stay valid).
   - The scheduler reconstructs every receiver's packet cache from what it transmitted and to whom.
   - Tests: `tests/test_marl_receiver_mirror.py`, 5/5 PASS. They cover:
     - an unselected receiver keeps its old packet;
     - reset clears the mirror;
     - two histories with the same latest broadcaster cache give different receiver features;
     - a sender cannot be decoded without being transmitted;
     - features read only the mirror and the clock.
2. **Deterministic replay of the 120 train/val snapshots.** Script:
   `scripts/MARL_hetero_mirror_replay.py`; output `…/mirror_diag/`, 120 records, sha ba1f8cb1….
   - At every snapshot the replay reproduced the saved z, base order and live K exactly.
   - Two stored values were re-rolled and matched exactly.
   - The mirror equalled the true receiver caches after every live transmission.
   - Mirror features were built with `_summary` and `_sensor` disabled.
   - Existing labels were reused, not relabelled.
   - A first run crashed on the sensor guard itself (bound methods left in `__dict__` broke the
     snapshot `deepcopy`). The guard was fixed, and the failed partial output was moved to scratch.
     No data from that run is used.
3. **Learners.** Script: `scripts/MARL_hetero_diag_train.py`; report `…/diag/report.json`,
   sha 6c7ecd14…
   - All learners share the same labels, the same candidate budget and the same paired-gain target
     Δ = f(S) − f(P).
   - Model and threshold selection used an inner split of the training seeds: fit 41–46, select
     47–48. Validation seeds 51–52 (4 episodes) were used only for this comparison.

   | learner | inputs |
   |---|---|
   | `mlp_public` | the pilot critic's inputs |
   | `mlp_history` | + the legal receiver mirror |
   | `ridge_edge_public` / `_history` | context-by-profile interaction model: edge weights β_ij + θ·c_ij(z) |
   | `mlp_joint_priv` | PRIVILEGED control: + current summaries and the induced joint actions of S and P |

4. **Selection rule.** Among the labelled candidates under each cap, "keep the prefix" is always
   allowed, and an edit is made only if its predicted gain is > 0. The same predictor also drives an
   unrestricted "direct" choice.

## Results (validation, 4 episodes; realised gain over the unchanged prefix)

Oracle references, true argmax among the same candidates:

| cap | oracle R1 | oracle all |
|---|---|---|
| +0 B | +0.39 | +0.39 |
| +28 B | +14.59 | +14.68 |
| +56 B | +16.39 | +19.35 |
| none | +16.50 | +20.29 |

Learned R1 at each cap. Each cell is the range over the 3 seeds, then [episodes with positive
gain out of 4; harmful-edit rate].

| learner | +0 B | +28 B | +56 B | none |
|---|---|---|---|---|
| mlp_public | 0.00 | −1.36 … −0.21 [1–2/4; harm 8–14%] | −1.89 … −1.06 | −2.11 … −0.93 |
| mlp_history (legal) | 0.00 … +0.04 | −0.88 … +0.31 [1/4; harm 4–15%] | −1.98 … −1.42 | −2.29 … −1.43 |
| ridge_edge_public | +0.21 | −1.12 [1/4; harm 21%] | −1.69 | −1.41 |
| ridge_edge_history | +0.17 | −1.28 [0/4; harm 18%] | −2.19 | −2.27 |
| **mlp_joint_priv (privileged control)** | +0.22 | **+6.42 … +7.19 [3–4/4; harm 7–16%]** | +6.22 … +7.76 | +6.78 … +7.98 |

The direct choice with the same predictor gives the same picture:
- the legal learners sit between −3.9 and +0.3;
- the privileged control reaches +6.5 to +9.5.

The ridge models selected λ = 10⁴, the edge of the grid, i.e. the flattest model. They edit on
100% of groups because their predictions are nearly tied and ties do not favour the prefix. This
means no usable signal was found. It is not a tuned negative result; widening the grid or breaking
ties in favour of the prefix would only move them toward "never edit".

## Reading (no causal claim beyond this)

- **No legal-information learner gives a repeatable validation improvement at any relevant cap.**
  At +28 B and above, the MLPs, the MLP with legal receiver history and the regularised interaction
  model all edit most of the time and realise small NEGATIVE mean gains. Adding the legal history
  does not change this.
- **The privileged control learns about 45% of the oracle R1 headroom at +28 B** (+6.4 to +7.2 of
  +14.6), repeatably across seeds and in 3–4 of 4 episodes, mostly at headway 8. With current
  summaries and joint actions supplied together, repairs become rankable from 72 training
  contexts.
- **Per the audit, this does not prove the information rule is irreducibly insufficient, nor that a
  fresh bid would fix it.** It shows that predicting the actors' response to a profile is the hard
  subproblem for a legal selector here, and that the value given the action is learnable at this
  scale.

## Decision under the audit's rule

> "Only a repeatable validation improvement at a relevant resource cap justifies more data and a
> new confirmatory test. If this diagnostic fails, stop expanding this learned-traffic direction for
> the present submission; do not automatically add fresh bids, a larger actor or a new simulator."

The legal-information diagnostic FAILED. For this submission cycle, the learned-traffic expansion
stops. What remains supportable:

1. **Mathematics**, compiled and not yet gated:
   - T1 estimated revision;
   - T2 needle calibration law;
   - tabulation dominance;
   - finite profile-search bound;
   - the earlier revision, nesting and XOR results.
2. **Oracle mechanism evidence** (exact, preregistered): on one stream with heterogeneous receivers,
   R = 1 recovers 88% of the private gap, and private beats the exact known-budget shared order in
   106/256 cases.
3. **Negative and diagnostic findings:**
   - the latency premise is refuted in PROTOCOL_v1;
   - legal-information selectors did not learn the headroom;
   - privileged summaries plus joint actions make it learnable, which supports actor-response
     prediction as one candidate bottleneck (corrected).

No empirically successful learned MARL algorithm can be claimed from this evidence.

## Limits

- Offline candidate-set evaluation: about 180 labelled candidates per group, not the full R1
  family.
- 4 validation episodes; 3 initialisation seeds.
- One grid, frozen MP2, held-phase value.
- The joint-action control uses oracle information by construction.
