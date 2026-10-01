# CityFlow mitigation screens after B1: development results (27/09/2026, 22:10–23:05)

- Evidence class: DEVELOPMENT.
  - Fit on the B1 train pool 301–364; epoch and τ selected on 401–408.
  - Reported on 501–508, which was OPENED by B1.
  - Frozen MP2 actor, held-phase H = 3, candidate-set argmax, 3×3 grid.
- Nothing here is confirmatory. The chosen design is confirmed on a fresh preregistered panel
  (`PROTOCOL_B2_FRESH_BID_20260927.md`).
- No ledger is edited.

## 1. What was tried, and why

B1 left one gap: legal selectors reach 1–5% of the oracle, while counterfactual joint actions
reach about 66%. Each direction below attacks one link in the chain
packets → actor response → value.

| direction | script | information at inference |
|---|---|---|
| retrained controls `ctrl_public`, `ctrl_history` | `MARL_hetero_mitigation_dev.py` | legal |
| auxiliary actor-response supervision `aux_*` (+ gate) | same | legal (privileged action labels at TRAINING only) |
| decision-focused loss `cls_history` | same | legal |
| structural response model `struct_legal`: frozen MP2 run on scheduler-known data | `MARL_hetero_response_replay.py` + same | legal |
| receiver bids `bid_prefgap` / `bid_flag` / `bid_queue` | same | 10 / 3 / 10 B charged |
| request bids: rule, sparse rule, MLP | `MARL_hetero_bid_replay.py`, `MARL_hetero_bid_request_dev.py` | 10 B (sparse: actual bytes) |
| top-2 bids + scheduler refresh score: rule, sparse rule, MLP | `MARL_hetero_bid_replay_v2.py`, `MARL_hetero_bid_top2_dev.py` | 10 B |
| legal emulation of the joint-action critic `mlp_top2_joint` | `MARL_hetero_top2_joint_dev.py` | 10 B (stage A trained on privileged labels) |
| privileged reference `ref_joint`, retrained | `MARL_hetero_mitigation_dev.py` | PRIVILEGED |

All learned selectors share one trainer: 2×128 MLP, Adam, 40 epochs, epoch chosen on the select
split. Every job saves its model, τ, chosen indices and per-group gains.

## 2. Diagnostics that shaped the designs (all B1 splits; diagnostic only)

- **The legal response model is near chance.**
  - Absolute action accuracy 0.103, against a chance level of 0.125.
  - Predicted per-receiver change: precision 0.29, recall 0.09, base rate 0.21.
  - The legal score gap does not predict change.
  - One snapshot was debugged: the code is right. Queues change fast relative to packet
    staleness, and the eight MP2 phases are nearly tied.
- **Receiver-local information is informative.**
  - The local preferred action matches the true prefix action 67% of the time.
  - The local gap predicts change: 0.30 in the lowest quintile against 0.10 in the highest.
- **Value of requested swaps** (single-receiver one-swap candidates):
  - adding the requested sender to a fragile receiver (gap < 1) gains +0.36, against −0.05 for
    other swaps;
  - with the top-2 refresh score > 5 and gap < 2, the gain is +0.50 to +0.83, against −0.08 to
    −0.12 at score ≤ 0.

## 3. Results

Full table: `MITIGATION_DEV_TABLE_20260927.txt`. Seed-averaged, 384 development groups.

| method | +28 R1 | +56 R1 | +56 direct | +84 direct | % oracle at own cap (+84 dir) |
|---|---|---|---|---|---|
| ctrl_public (legal) | +0.69 | +0.94 | +1.31 | +1.20 | 7.6 |
| ctrl_history (legal) | +0.38 | +0.37 | +1.20 | +1.61 | 10.1 |
| aux_public (legal, aux labels) | +0.76 | +1.04 | +1.51 | +1.81 | 11.4 |
| struct_legal (legal) | +1.07 | — | +1.58 | +2.24 | 14.1 |
| bid_prefgap (10 B) | +1.17 | +1.86 | +2.26 | +2.76 | 17.4 |
| mlp_top2 (10 B) | +0.96 | +1.57 | +1.95 | +2.23 | 14.1 |
| **mlp_top2_joint (10 B)** | +0.64 | +1.40 | **+2.50** | **+3.19** | **20.1** |
| rule_request / rule_top2 (10 B, no learning) | +0.49 / +0.08 | +0.74 / +0.50 | +0.77 / +1.01 | +1.05 / +0.98 | ≤ 6.6 |
| ref_joint (PRIVILEGED) | +8.41 | +9.76 | +11.86 | +13.32 | 83.9 |

## 4. Reading

- **Auxiliary actor-response supervision alone does not help reliably.** `aux_*` stays within the
  controls' intervals. Gating by the predicted change hurts.
- **Some directions give a positive difference with 95% CI > 0 against the chosen control at the
  same total cap** (§3 table): `struct_legal` at +28, `bid_prefgap` at +28/+56/+84,
  `mlp_top2` R1, and `mlp_top2_joint` direct at +56/+84.
  - The largest is `mlp_top2_joint` direct at +84: +1.58 [+0.63, +2.73] against ctrl_history.
  - Legal-only `struct_legal` improves on the controls at +28 by about +0.4 to +0.7. This is a
    small legal gain, not yet the headroom.
- **Rules without learning are weak.** Per-swap signals do not add up to good multi-receiver
  profiles under a naive additive score.
- **The gap remains large.** The best charged method reaches about 20% of the oracle at its cap.
  The privileged reference reaches 64–84%. Predicting responses from local bids (stage A:
  accuracy 0.70 against 0.68–0.71 for "always p1") is the weak link.
- **The freeze picks mlp_top2_joint, direct, +84, control ctrl_history**
  (`b2_freeze_20260927/`), mechanically by the preregistered rule.
- **Two cautions.**
  - This is the maximum over 36 candidates on an opened panel, so a winner's curse is expected.
    That is why the result must be confirmed on a fresh panel.
  - +84 B is about +44% over the mean prefix bytes (~190 B per step).

## 5. Closed-loop oracle headroom (`MARL_hetero_closed_loop.py`)

- Frozen MP2; 16 development episodes (501–508 × 2 headways).
- At each of 26 decisions, the candidate with the best TRUE held-phase value within the cap is
  transmitted, and the simulation continues.

| cap | Σ waiting vs prefix | episodes better | finished trips | bytes |
|---|---|---|---|---|
| +28 | −9.6% (−23.4 … +6.3) | 13/16 | +14.5 | +5.0% |
| +56 | −10.3% (−23.9 … +5.2) | 14/16 | +14.9 (15/16 better) | +10.4% |

- Held-phase repair value translates into closed-loop traffic value on this panel.
- The reference is not deployable, because it uses oracle rollouts.
- Closed-loop runs of the frozen learned selectors are the next step (the evaluator is ready).

## 6. Failed or superseded attempts (kept)

- `bid_request_dev_20260927_222123`: crashed because a glob matched a log file. It was fixed and
  rerun as `bid_request_dev_20260927_222226`.
- The first `MITIGATION_DEV_TABLE` attempt failed because zsh does not word-split variables; it
  is kept in `legacy/`.
