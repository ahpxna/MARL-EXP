# EXPLORATORY schedule-only dose: hold-r age-first at fixed K (3×3, development panel)

Written 01/10/2026 19:16:12 EDT, before the runs (Lean/papers subagent hypothesis H2).  models/marl_delivery_hold.HoldDelivery(r):
the age-first order is recomputed every r steps and reused in between — same K, fresh count, packets and bytes.  Evaluator
scripts/MARL_e3_hold_eval.py (r = 1 reproduces the plain relay rows 8/8 at K = 1 and K = 2).  Channel-only burdens (no policy):
K = 2: B_3 1.64 / 2.21 / 5.31 / 8.10 / 11.95 for r = 1 / 2 / 3 / 4 / 6 (never-heard 0.54 → 1.92); K = 3: 0 / 3.20 / 5.95 for r = 1 /
4 / 6; reference K = 1 (r = 1) 8.48.  Arms: relay6Cage_st_s0–9 at (K = 2, r ∈ {2, 3, 4, 6}) and (K = 3, r ∈ {4, 6}); r = 1 rows
and Z rows reused (e3_negflip_20261001, e3_dev_Z_20261001; Z ignores the schedule).
Predictions (the stale tail is causal, relative reading τ = 3): mean gain vs Z falls monotonically with B_3 across the eight
(K, r) cells; K = 2 / r = 4 (B_3 8.10, two fresh senders) is negative like K = 1 (dev −1.33 %).  Kill: K = 2 / r = 4 positive on
≥ 7/10 seeds, or Spearman(B_3, mean gain) over the cells > −0.5.  Caveat fixed now: holding also raises never-heard (0.54 →
1.31 at r = 4), so the test separates "one fresh sender" from "stale tail + missingness", not age from missingness.
