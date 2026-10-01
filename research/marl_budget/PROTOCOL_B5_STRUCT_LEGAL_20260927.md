# PROTOCOL B5 — confirmation of the LEGAL structural response selector `struct_legal` (preregistered)

Written 2026-09-27 23:18:35, before any B5 label exists. No ledger is edited.

## Question
On development data (opened B1 panel 501–508), `struct_legal` improved on the no-bid legal controls
using ONLY legal information: the frozen MP2 is run on scheduler-known data, with no bid and no
extra bytes. Is that improvement real on fresh traffic?

## Frozen design (mechanical: the maximum development difference over (C, policy) against the
better no-bid control at the same (C, policy))
**policy = direct, total cap C = +84, control = ctrl_history**. Models and τ are frozen in
`research/marl_budget/mitigation_dev_20260927_221203` (struct_legal/ctrl_* s0–s2).

| C | policy | control | struct_legal | control | diff |
|---|---|---|---|---|---|
| 84 | direct | ctrl_history | +2.240 | +1.609 | +0.630 |
| 84 | repair_R1 | ctrl_public | +1.429 | +0.828 | +0.601 |
| 28 | direct | ctrl_public | +1.202 | +0.706 | +0.497 |
| 28 | repair_R1 | ctrl_public | +1.066 | +0.685 | +0.381 |
| 56 | direct | ctrl_public | +1.582 | +1.305 | +0.278 |
| 56 | repair_R1 | ctrl_public | +1.136 | +0.937 | +0.200 |

## Panel
- Fresh seeds 901–916 × headways 8, 16: 32 episodes, iid capacities, prefix live policy.
- Collector `scripts/MARL_hetero_panel_collect.py` (split `confirm`). It computes every field
  live, and it reproduces the replay pipeline exactly on seed 301.
- Evaluation: `scripts/MARL_hetero_b2_confirm_v2.py` with the frozen models; no refit.

## PASS iff
1. The 95% cluster-bootstrap lower bound of Δ = gain(struct_legal) − gain(control) is > 0.
2. The lower bound of gain(struct_legal) is > 0.
3. All 3 seeds have a gain > 0.

The verdict file's c4 (bid_queue) does not apply to a no-bid method and is ignored.

## Scope
Held-phase H = 3, frozen MP2, 3×3 grid. It is not closed loop.
