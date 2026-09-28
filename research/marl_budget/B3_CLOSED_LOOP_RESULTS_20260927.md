# B3 — closed-loop test of the frozen B2 design: results (27/09/2026, 23:00)

- Protocol: `PROTOCOL_B3_CLOSED_LOOP_20260927.md`, preregistered before the run.
- Run: `research/marl_budget/b3_closed_loop_20260927_225248/`. Evaluator `scripts/MARL_hetero_closed_loop_v2.py`; verdict
  `scripts/MARL_hetero_b3_verdict.py` → `verdict.json`.
- 32 fresh episodes (seeds 601–616 × headways 8, 16), 26 decisions each, total cap +84, direct,
  bids charged.

## Verdict: FAIL (c1)

| quantity | value |
|---|---|
| Σ waiting, mlp_top2_joint vs ctrl_history | **−0.26%, 95% CI [−1.20%, +0.62%]** (c1 ✗); better in 11/32 |
| Σ waiting vs prefix | −0.65% [−1.63%, +0.30%] (c2 ✓ on the mean) |
| ctrl_history vs prefix | −0.38% |
| finished trips vs ctrl / vs prefix | +1.1 / +2.0 (c3 ✓) |
| bytes vs prefix | +7.4% (bid) / +1.1% (control) |
| oracle_heldphase (reference) vs prefix | **−14.5% Σ waiting, +15.2 trips** |
| edits per 26-step episode | mlp_top2_joint 2.15, ctrl_history 1.06, oracle 19.2 |

## Diagnosis (not a bug)

- **Parity holds.** At a labelled snapshot (seed 601, headway 8, t = 10), the closed-loop code
  reproduces the confirmation's anchored predictions for both models to within 5e-6: 66 and 72
  positive candidates.
- **The trace shows the collapse.** On seed 601, mlp_top2_joint/s0 edits at t = 2, 3, 4. From
  t = 5 it predicts every candidate worse than the prefix (max anchored score 0), and never edits
  again.
- **Shadow mode shows the cause.** Run on the prefix trajectory with nothing transmitted, the same
  models WOULD edit at 13–16 of the 16 later steps (all three seeds, seeds 601–603). The held-phase
  edit rate is 0.68–1.0.
- **Conclusion: covariate shift induced by the policy itself.**
  - Critics and the stage-A model were trained only on states of PREFIX trajectories.
  - Once the selector's own patches change caches, ages and the base order, the inputs leave that
    distribution, and the models stop proposing edits.
  - The held-phase B2 gain (confirmed) does not become closed-loop benefit for this reason. The
    closed-loop headroom itself is real (the oracle gets −14.5%).

## Next step implied

On-policy (DAgger-style) data: label snapshots along the selectors' OWN closed-loop trajectories.
- The oracle held-phase values of the same candidate family are the expert labels.
- Aggregate these with the prefix-trajectory data, retrain, and test in closed loop again on a
  fresh panel under a new preregistration.
