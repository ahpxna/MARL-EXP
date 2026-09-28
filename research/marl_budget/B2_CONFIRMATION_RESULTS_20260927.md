# B2 — receiver-local charged bids: CONFIRMATION result (27/09/2026, 22:51)

- Protocol: `PROTOCOL_B2_FRESH_BID_20260927.md`, with Amendment 1 and §5 FROZEN DESIGN.
  - Its sha ae3dd907… is the same in the collector manifests, the confirmation report and the
    current file.
  - The freeze was written at 22:49:52; the first confirmation label at 22:51:02.
- No ledger is edited.

## Frozen design (chosen mechanically on development data)

- **Bid** `mlp_top2_joint`: a 1 B receiver bid (best and runner-up MP2 phase, gap bin), plus a 1 B
  header, charged inside the total cap.
- **Scheduler side:**
  - refresh scores from the public topology, the known MP2 code and the legal receiver mirror;
  - a stage-A response model trained with privileged counterfactual actions as TRAINING labels
    only;
  - a critic on the predicted soft joint action.
- **Policy** direct; **total cap** +84 B over the prefix bytes; **control** `ctrl_history` (the
  no-bid legal control that was better at this cap on development data).

## Confirmation panel and provenance

- **Panel.** Fresh traffic seeds 601–616 × headways 8 and 16: 32 episodes, 192 snapshots, 768
  groups.
  - Collector `MARL_hetero_b2_collect.py`.
  - Replays: mirror, response, request-bid and top-2-bid, all COMPLETE with their reproduction
    checks.
- **Evaluation.** `MARL_hetero_b2_confirm_v2.py` with the frozen models, τ and stage A. No
  refitting. Run dir `b2_confirm_20260927_225002/`.

## Result: PASS (all four preregistered criteria)

| quantity | value |
|---|---|
| Δ = gain(bid) − gain(ctrl_history), seed-averaged | **+1.85, 95% CI [+0.95, +2.84]** (c1 ✓) |
| gain(bid) | +3.12 [+1.70, +4.59] (c2 ✓) |
| per-seed gains | +3.90, +2.98, +2.48 (c3 ✓) |
| gain(bid_queue), same-byte simple bid | +0.98 (c4 ✓: bid > queue) |
| control gain | +1.27 |
| oracle R1 at the bid's cap | +17.66 → the bid reaches **17.7% of the oracle** |

`mlp_top2_joint` is also the best method at every other cap and policy on this panel. At +28, for
example, direct gives +1.21 to +1.86 against about +0.9 for the controls.

## What this supports, and what it does not

- **Supports.** On frozen MP2 / held-phase H = 3 / 3×3 CityFlow, a 1-byte receiver-local bid,
  charged inside the same byte cap, improves repair selection by about 2.4× over the better no-bid
  legal selector, on traffic never used for development.
- **Does not establish:**
  - closed-loop benefit (tested separately: PROTOCOL_B3);
  - learned actors (E3);
  - more than about 18% of the oracle headroom. The privileged joint-action reference reaches
    64–84%.
- **Labels and scope.**
  - The direct policy shares the critic whose epoch was selected for repair_R1; it is a
    shared-critic comparator.
  - The oracle is over the stored candidate set.
  - +84 B is about +44% of the mean prefix bytes. The comparison is at equal total bytes.
