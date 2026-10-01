# B4 — one DAgger iteration, then the preregistered closed-loop test (28/09/2026, 00:05)

- Protocol: `PROTOCOL_B4_DAGGER_20260927.md`, written before any on-policy label existed.
- Runner: `scripts/RUN_marl_b4_train_and_test.sh`. Run dir `b4_run_20260927_230436/`.
- No ledger is edited.

## Provenance and separation (checked)

- **Manifests.** `cl_dev`, `cl_test` and `cl_test_frozenB2` are COMPLETE. Every recorded source
  hash equals the current file.
- **Evaluator.** `MARL_hetero_closed_loop_v2.py`, cap +84, direct, bids charged.
- **Models.**
  - Retrained: `top2_joint/` and `controls/`, via `dev_map.json`.
  - The frozen-B2 reference loads `b2_freeze_20260927/dev_map.json`.
- **Data.**
  - On-policy collection used seeds 301–364 (train) and 401–408 (select), β = 0.5, aggregated with
    the B1 prefix-trajectory data.
  - The test seeds 801–816 appear in no other manifest under `research/marl_budget/`.
  - The development closed loop used 501–508 and decided nothing.
- **Oracle access.** `MARL_hetero_closed_loop_report.py`: no deployable method used oracle access
  on either test run.
- **Pairing check.** The prefix rows of `cl_test_frozenB2` equal those of `cl_test` on all 32
  episodes.
- **Endpoints.** Recomputed independently from `rows.json`; they agree with `cl_test_verdict.txt`
  up to bootstrap noise.

## Registered result: **PASS** (all three criteria)

| criterion | value | pass |
|---|---|---|
| c1: 95% upper bound of relative Σ waiting, retrained bid − retrained ctrl_history, < 0 | −1.49% [−2.75%, −0.23%] | ✓ |
| c2: mean against the prefix < 0 | −0.68% | ✓ |
| c3: finished-trip difference against the control ≥ 0 | +1.65 | ✓ |

## What the pass does and does not show (read with the numbers below)

32 episodes; init seeds are averaged per episode; bootstrap over episodes.

| method (801–816) | Σ waiting vs prefix | better episodes | edits/episode (steps of 26) | bytes vs prefix |
|---|---|---|---|---|
| retrained ctrl_history | +0.89% [−1.33, +2.96] | 13/32 | 15.9 | +15.3% |
| **retrained mlp_top2_joint** | **−0.68% [−2.88, +1.32]** | 17/32 | 20.6 | +25.0% |
| frozen B2 mlp_top2_joint (not retrained) | −0.74% [−1.77, +0.24] | 11/32 | 2.1 | +7.1% |
| oracle_heldphase (reference) | −15.00% [−17.02, −13.05] | 32/32 | 19.5 | — |

**Reading.**
1. **The registered comparison passes.** Against the retrained control, the retrained bid selector
   lowers Σ waiting by 1.5%.
   - Finished trips +1.1% [−0.2, +2.5].
   - Censored travel time −0.25% [−0.49, −0.01].
2. **Part of the pass comes from the control getting worse.**
   - DAgger made the control edit 15.9 of 26 steps, and it drifted to +0.89% against the prefix.
   - Against the PREFIX, the bid selector's −0.68% is not significant.
   - Against the FROZEN B2 design it is +0.10% [−2.05, +2.16]. The retraining did not improve
     the bid selector on waiting; it changed how much both selectors edit.
3. **The closed-loop editing symptom is fixed, the benefit is not.**
   - The retrained selectors now edit as often as the oracle: 20.6 against 19.5 steps.
   - They realise about 4.5% of the oracle's closed-loop reduction (−0.68% against −15.0%).
   - Before B4, the frozen models edited 1–3 steps (B3, and the 1101–1116 panel).
   - So the edit rate was a real symptom of the prefix-only training distribution, but restoring
     it does not restore the gain.
4. This leaves open the second hypothesis from the independent readiness audit (§4.6): held-phase
   target mismatch. The labels score a joint action held for H = 3; the live loop re-selects every
   step. The planned diagnostic is `MARL_hetero_target_diag.py`, on fixed development states.
5. **Scope.** Frozen MP2 actor, one DAgger iteration, 3×3 grid, i.i.d. capacities, +84 B. This is
   a selector result, not learned-actor MARL.

## Development closed loop (501–508; decided nothing)

- Retrained bid against the prefix: +1.97% [−2.40, +6.64]. Against the control: +0.60%.
- Development criteria c1 and c2 fail and c3 passes. This is recorded as the registered
  development check.
- The test was run as preregistered, whatever the development outcome.

## Related closed-loop evidence this round (descriptive, fresh panel 1101–1116)

| method | Σ waiting vs prefix | edits/episode |
|---|---|---|
| independently tuned direct, no bid (`cl_direct_indep_20260928_000001`) | +0.68% [−0.13, +1.70] | 1.5 |
| independently tuned direct, top-2 bid (same run) | +0.34% [−1.01, +1.74] | 2.3 |

Both were trained on prefix-trajectory data only, and they show the same low edit rate as the
frozen B2 models.

## Decision input for E3

- By the protocol this is a PASS, so it is evidence for the selector on a fixed MP2 actor.
- By the numbers the closed-loop benefit is small, and not distinguishable from the prefix.
- Per the critical path and the readiness audit P1.4, a PASS opens the actor pilot (P2).
- The target diagnostic above decides which label target the actor pilot's evaluator should use.
