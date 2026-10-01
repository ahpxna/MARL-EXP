# B1 — learning curve on the heterogeneous-receiver objective: results (27/09/2026)

- Protocol, preregistered before data: `PROTOCOL_B1_LEARNING_CURVE_20260927.md`, sha e84ca65f…
  The same hash appears in the collector manifests and in the training report, so it was not
  edited after data existed.
- No ledger is edited.
- Evidence class: frozen MP2 actor, oracle labels, candidate-set argmax. This is not learned MARL.

## Provenance

- **Run:** `research/marl_budget/b1_lc_20260927_201443/`, via `scripts/RUN_marl_b1_lc.sh`
  (sha c57c7195…).
- **Labels:** `scripts/MARL_hetero_lc_collect.py` (sha 05377da1…), 4 shards, each COMPLETE, 240
  records each, 960 in all.
  - 64 train seeds (301–364), 8 select (401–408), 8 test (501–508), at headways 8 and 16.
  - 3840 groups (snapshot × capacity vector).
- **Mirror:** `scripts/MARL_hetero_mirror_replay.py`, unchanged. 4 × 240 records, COMPLETE. Every
  snapshot reproduced z, the order, K and two stored values, and the mirror equalled the true
  caches after every transmission.
- **Training:** `scripts/MARL_hetero_lc_train.py` (sha d7165fb2…).
  - v2 learners and selection imported unchanged.
  - 40 jobs, 4777 s, `train/report.json` COMPLETE.
  - Self-checks passed: seed-disjoint splits; prefix delta 0; oracle R1 gain ≥ 0; sources unchanged.
- **Smoke:** a `--smoke` run (contract A) and a `--mini` run (the full replay and training path),
  both in scratch.
  - The first attempt to replay smoke labels was correctly refused: smoke submits a non-prefix
    profile, so its trajectory differs from the one the replay rebuilds.
  - `--mini` was added for that reason, before the full run.

## Results: test panel, cap +28 B, gain over the same prefix

Oracle R1 = +13.33 on the same 384 groups.

| learner (information) | N = 8 | N = 16 | N = 32 | N = 64 |
|---|---|---|---|---|
| **mlp_history** (legal; PRIMARY) | +0.21 [−0.30, +0.76] | +0.24 [−0.36, +0.92] | +0.83 [+0.32, +1.35] | **+0.19 [−0.35, +0.75]**; seeds +0.72, −0.06, −0.09 |
| mlp_public (legal) | +0.74 [+0.14, +1.40] | +0.80 [+0.26, +1.43] | +0.81 [+0.29, +1.37] | +0.62 [+0.01, +1.29] |
| ridge_edge_history (legal) | +0.01 | +0.88 | +0.84 | +0.76 [−0.05, +1.57] |
| mlp_joint_only (PRIVILEGED reference) | +8.31 [+5.58, +11.19] | +8.73 | +8.73 | **+8.82 [+5.77, +12.09]** (66% of oracle) |

Brackets are 95% cluster-bootstrap intervals over the 16 test episodes, on the seed-averaged gain.

At N = 64, cap +28:

| learner | edit rate | harm per edit | executed action changed, per ALL groups (per edit) | extra bytes |
|---|---|---|---|---|
| mlp_history | 0.48–0.85 | 0.09–0.15 | 0.12–0.24 (0.25–0.33) | 9–14 |
| mlp_public | 0.88–1.0 | 0.05–0.16 | 0.23–0.29 (0.23–0.33) | 14–19 |
| mlp_joint_only | 0.89–0.97 | 0.16–0.18 | 0.89–0.95 (0.99–1.00) | 11–12 |

## Decision (preregistered rule)

**B1 FAILS.** At N = 64, `mlp_history` has seeds at −0.06 and −0.09, a CI that includes 0, and 1.4%
of the oracle. Criteria 1–3 all fail.

`mlp_joint_only` meets criteria 1–3 at every N. The protocol's reading table names this case
"information bottleneck confirmed at 8× the data". That wording is too strong and is corrected in
the section below. The legal learned selector is not claimed. The next step
named by the protocol is B2, a paid fresh-bid protocol. The stop-rule exception covered B1 only,
so B2 needs a new authorisation.

## Reading

- **Growing the training pool from 8 to 64 seeds did not close the gap for these
  learner/representation/selection choices** (corrected wording; see below).
  - Legal learners are flat from N = 8 to N = 64, at 1–7% of the oracle. `mlp_history` is not
    monotone: +0.83 at N = 32, +0.19 at N = 64.
  - The privileged reference is already at 62% of the oracle with 8 seeds, and it stays flat.
  - 8× more traffic does not move either class.
- **Counterfactual joint actions substantially improve prediction and selection.** This supports an
  actor-response hypothesis; it does not identify the mechanism (corrected; see below).
  - Legal learners edit often but change the executed joint action in only 12–29% of groups.
  - The privileged reference changes it in about 90% of groups.
  - This repeats the diagnostic v2 finding (HETERO_DIAGNOSTIC_V2) on a fresh panel with 8× the
    training data.
- **mlp_public** has a small positive gain with CI > 0 at every N: about +0.6 to +0.8, 5–6% of the
  oracle. It is secondary under the protocol and does not rescue the primary. It is recorded as
  "a small, statistically positive but practically negligible legal gain".

## Limits

- Frozen MP2 actor, one 3×3 grid, H = 3 held-phase value, candidate-set argmax.
- 8 test seeds.
- The ridge rows use one fit per level; they have no initialisation seeds.
- The `mlp_history` N = 64 fits took about 76 min each, against about 4–5 min for other learners.
  Swap was in use at the time (3.9 GB). The selection procedure is unaffected, but the wall time
  should not be read as the method's cost.

## Corrections after MARL_B1_INDEPENDENT_VERDICT_20260927 (27/09, 22:40)

The protocol is unchanged byte for byte. These correct the interpretation only.

1. **"Not a data-scale failure / information bottleneck confirmed" is too strong.** The supported
   statement is:
   - increasing the training seed pool from 8 to 64 did not close the gap for these
     learner/representation/selection choices;
   - giving counterfactual joint actions substantially improved prediction and selection.

   Joint actions change both the information AND the representational difficulty. Nothing
   establishes a Bayes-risk bound, an indistinguishable legal-history witness, or a
   consistent-estimator limit. Legal information is not shown to be insufficient in principle.
2. **Action-change rates.** The code reports action changes per ALL groups. The report to the
   user wrongly called them "per edit". Conditional on editing, the rates are:
   - history 25.3–32.8%;
   - public 22.7–32.8%;
   - privileged 98.7–100%.

   The table above now shows both.
3. **The privileged +8.82 is not a target for a small bid.** That reference receives
   candidate-dependent counterfactual joint actions, not one current action per agent.
4. **Comparator.** The direct policy shares the critic whose epoch was selected for repair_R1; it
   gets only its own threshold. It is a shared-critic comparator, not an independently tuned
   budget-aware baseline. No unique advantage of revision over budget-aware selection is shown.
5. **Scope.** These are offline candidate-set results on frozen MP2 with H = 3. The oracle is over
   the stored candidate set, not over every byte-feasible profile.
6. **Artifact limitation.**
   - The B1 driver discarded model blobs and did not save predictions or chosen indices, so
     individual choices cannot be replayed. The independent audit could verify attainability of
     the saved gains, not replay the choices.
   - Later drivers (`MARL_hetero_mitigation_dev.py`, `MARL_hetero_b2_confirm.py`) save per-job
     models, taus, chosen indices and gains atomically.
