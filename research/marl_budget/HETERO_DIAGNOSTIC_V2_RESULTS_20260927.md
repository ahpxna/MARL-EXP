# Selective-revision diagnostic v2 — results, 27/09/2026

This file does not edit any ledger and has not been gated. It completes the diagnostic required by
`research/papers/audits/MARL_HETERO_DIAGNOSTIC_INDEPENDENT_AUDIT_20260927.md`. Frozen MP2, held-phase
H = 3, TRAIN/VAL only.

## Setup

- **Producer:** `scripts/MARL_hetero_diag_train_v2.py`. v1 and its report are kept.
- **Tests:** `tests/test_marl_hetero_diag_v2.py`, 3/3 PASS. They cover the audit's synthetic tie
  case, invariance to adding a constant to every score, never-edit and caps.
- **Output:** `research/marl_budget/hetero_pilot_20260927_181207/diag_v2/`. report.json COMPLETE,
  571 s; decisions sha 2068d0ec…
  - Every model and its normalisation are saved, together with epoch/λ/τ, the anchored candidate
    scores and the chosen index for every validation group and cap.
- **Rule:**
  - Scores are anchored, s(S) = pred(S) − pred(P), with s(P) = 0.
  - Ties and scores ≤ τ keep the prefix.
  - τ is chosen on inner-selection seeds 47–48 from {0, quantiles of positive scores, never-edit}.
    Epoch, λ and τ all target the declared operating point cap = prefix + 28 B. Repair and direct
    use the same procedure.
  - Comparison is on validation seeds 51–52: 4 episodes = 2 traffic seed IDs × 2 loads, 96 groups.
- **Selection** is a candidate-set argmax over about 181 stored candidates, not the deployed
  search.

## Results at the operating point (+28 B)

Oracle R1 over the stored candidates: +14.59. Gains are the range over 3 initialisation seeds.

| predictor | information | repair_R1 gain | episodes > 0 (per seed) | edit rate | harm / edit | executed action changed | extra bytes |
|---|---|---|---|---|---|---|---|
| mlp_public | legal | −1.49 … −0.17 | 1, 0, 1 | 1.00 | 0.12 | 0.27 | +17.5 |
| mlp_history | legal + receiver mirror | −0.15 … +0.78 | 1, 2, 1 | 0.38 | 0.08 | 0.10 | +6.5 |
| ridge_edge_public | legal | −0.62 (τ = 5.5) | 0 | 0.02 | 1.00 | 0.02 | +0.3 |
| ridge_edge_history | legal + mirror | −0.51 | 0 | 1.00 | 0.09 | 0.27 | +15.8 |
| mlp_summaries_only | privileged summaries | −0.44 … +0.22 | 1, 3, 2 | 1.00 | 0.14 | 0.33 | +14.8 |
| **mlp_joint_only** | privileged joint actions | **+7.09 … +7.98** | 4, 3, 4 | 0.96 | 0.17 | 0.94 | +10.8 |
| mlp_joint_priv | summaries + joint actions | +6.93 … +7.70 | 3, 2, 3 | 0.98 | 0.21 | 0.97 | +10.7 |

Additional observations:
- The direct choice with the same predictor matches repair_R1 within about 1 in every row.
- For the ridge models, the inner split selected never-edit in the direct policy.
- The privileged joint-action gains are concentrated at headway 8: about +15 there, and −0.5 to
  +0.8 at headway 16.
- At the +0 B cap every method is within ±0.3, and the oracle is +0.39.

## Reading

- **After anchoring, prefix-favouring ties and inner-selected thresholds, no legal-information
  predictor shows a repeatable validation improvement at the operating point.**
  - The best is the receiver-history MLP: one seed at +0.78; the others at +0.10 and −0.15; 1–2 of
    4 episodes positive.
  - The thresholds work as intended: its edit rate drops to 0.38 and harm per edit to 0.08. But
    what remains is about 0 to 5% of the oracle headroom.
- **The ablation splits the earlier privileged control.**
  - Current summaries alone do not help.
  - Candidate and prefix joint actions alone recover about half of the oracle headroom, repeatably
    across seeds and 3–4 of 4 episodes, mostly at headway 8.
  - So the information that makes repairs rankable here is what the actors will DO under a profile.
    This is consistent with actor-response prediction being a bottleneck for legal selectors.
  - It does not prove that legal information is irreducibly insufficient, nor that a fresh bid would
    fix it (audit §4).
- **Executed action.** Many "edits" do not change the executed joint action. For the legal MLPs at
  τ = 0, only 27% of groups change the action even though nearly every group edits.

## Decision (audit rule)

This corrected diagnostic "remains unhelpful" for legal-information selection. For the present
submission cycle, stop the learned-traffic expansion:
- no more data collection for this design;
- no actor training;
- no bids;
- no simulator change.

Preserve the oracle mechanism and mathematical results. Do not claim an empirically successful
learned MARL method.

## Limits

- 4 validation episodes (2 seed IDs); validation 51–52 was also used in earlier development.
- 72 fit contexts.
- Candidate-set argmax, not the deployed search.
- Frozen MP2, held-phase value, one grid.
