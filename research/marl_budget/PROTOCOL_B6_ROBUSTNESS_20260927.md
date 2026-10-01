# PROTOCOL B6 — robustness panels: capacity processes and held-out loads (DESCRIPTIVE, preregistered)

- Written 27/09/2026 ~23:20, before any B6 label exists.
- No ledger is edited.
- The scope (§5 E3) asks for fixed, bursty and shifted budgets, and for held-out loads. Every
  earlier hetero panel used i.i.d. uniform capacities k_i ∈ {1..7}. The `bursty` BudgetTraceSpec
  passed to the environment is overwritten by the hetero capacity trace, so the earlier label
  "bursty" was inaccurate.

## Panels

All panels: fresh seeds, prefix live policy, labels as in B1. Collector
`scripts/MARL_hetero_panel_collect.py`.

| panel | capacity process | headways | seeds |
|---|---|---|---|
| cap_fixed | k_i fixed per episode, U{1..7} | 8, 16 | 1001–1008 |
| cap_bursty | per-receiver Gilbert–Elliott: k_hi ~ U{4..7} / 1 | 8, 16 | 1011–1018 |
| cap_low | U{1..3} i.i.d. | 8, 16 | 1021–1028 |
| cap_high | U{5..7} i.i.d. | 8, 16 | 1031–1038 |
| load_12 | i.i.d. U{1..7} | 12 (interpolation) | 1041–1048 |
| load_24 | i.i.d. U{1..7} | 24 (lighter, extrapolation) | 1051–1058 |
| load_5 | i.i.d. U{1..7} | 5 (heavier, extrapolation) | 1061–1068 |

## Evaluation (frozen models; no refit)

- **Evaluator:** `scripts/MARL_hetero_panel_eval.py`.
- **Methods, all frozen as used in B2/B5:**
  - ctrl_public, ctrl_history, struct_legal, bid_prefgap, mlp_top2, mlp_top2_joint;
  - ref_joint (PRIVILEGED).
- **Settings:** caps +28/+56/+84, policies R1/direct, bids charged.
- **Endpoint:**
  - capacity panels: mean held-phase gain over the prefix on LIVE-K groups only (the process
    under test);
  - load panels: all groups.
  - Fraction of the oracle.
  - Cluster bootstrap over episodes.
- **Descriptive.** No PASS/FAIL. What is reported: whether the B2 design's advantage over the
  control at +84 direct keeps its sign and CI in each panel, and how gains scale with capacity.
- **Frozen MP2, held-phase H = 3.** It is not closed loop.
