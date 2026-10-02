# Addendum 1 to PROTOCOL_E3_EXACT_DEMAND_1B_20261001: the SIGN of G′ (stale copies can make communication harmful)

Written 01/10/2026 11:00 EDT.  At this moment protocol 1's target has 79 of 80 arms complete and its report file still holds
only the 10:41 pre-launch "INCOMPLETE" stub: no target result has been read.  The v4 predictor probes are still running, so
no G′ value is known either.  Nothing in protocol 1 or 1b is changed; this adds one prediction on the same target.

## Motivation (from the v4 smoke, seed 0, one episode, 234 receiver-steps)
The EMPTY base needed fresh messages on FEWER receiver-steps than the CACHE base (0.26 vs 0.29; mean prefix depth 0.55 vs
1.24): stale cached copies push the teacher's action out of its own acceptable set.  Hence G′_s(K) = Q^∅_prefix(0) −
Q^C_prefix(K) can be NEGATIVE at small K: with K fresh senders on top of stale copies the teacher can be worse off than with
the local observation alone.  The external audits did not raise this.

## Prediction (fixed now)
- P-sign: over the 70 cells (s, K), cells with G′_s(K) < 0 have realised gain_s(K) < 0 more often than cells with
  G′_s(K) > 0.  Statistic: difference of the two shares, Δ = P(gain < 0 | G′ < 0) − P(gain < 0 | G′ > 0); SUPPORTED iff
  Δ > 0 and the seed-cluster bootstrap (resample seeds with all their K cells, 4000 draws, generator seed 0) puts the 95 %
  lower bound of Δ above 0.  Unit of resampling = seed (no pseudoreplication of the 70 cells).
- If no cell has G′ < 0, P-sign is UNDETERMINED (not failed), and the stale-harm reading is reported as absent at the
  capacities tested.
- Reported with it: the number of cells with G′ < 0 per K, and Q^∅_prefix(0) − Q^C_prefix(0) per seed (the stale-harm
  index: negative = stale copies hurt the teacher before any fresh message).

## Not changed after this file
P-sign, its statistic, threshold, bootstrap and the undetermined case.  Implemented in
`scripts/MARL_e3_exact_demand_report.py` (added before the report first runs on complete data).
