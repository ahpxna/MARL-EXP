# Pre-specified confirmatory test: predicting the value of communication before learning it (direction A)

Written 01/10/2026 08:2x EDT, BEFORE any run on the reserved panel 2701–2764 (that panel has never been evaluated: the
ten-seed panel run of PROTOCOL_E3_TEN_SEEDS_20260930.md did not start — disk full, ledger L-196/L-197).

## Predictors (all computed ONLY from the development panel 901–964 or training logs, already on disk)
- N_s — the teacher's message need: 1 − share of receiver-steps whose teacher action with no fresh sender (cache base,
  v1 probe) is in A_0.25 (`e3_decision_depth_ten_report_20261001.json`, primary_cache.N).  The obstruction-mass proxy
  (LeanMarlObstructionMassV1).
- D_s — the naive comparator: 1 − final training agreement of the zero-byte student distill_none_s<s> with the teacher
  (last `agree` value in `e3_delivery_actors_20260929/distill_none_s<s>.log`): 0.081 0.076 0.069 0.061 0.080 0.125 0.102
  0.043 0.031 0.069 (s0…s9).
## Target (reserved panel, measured once)
- gain_s = −(mean over the three age-first cells iid / cap4 / low of the paired waiting effect of relay6Cage_st_s<s> vs
  distill_none_s<s>), exactly the primary arm and endpoint of PROTOCOL_E3_TEN_SEEDS_20260930.md.
## Predictions (fixed now)
- P-A1: Spearman(N_s, gain_s) ≥ 0.5.
- P-A2: Spearman(N_s, gain_s) > Spearman(D_s, gain_s).
- Development-panel values for reference (exploratory, ledger L-198): Spearman(N_s, −G_s) = 0.794 (pre-registered
  V-D10), with relay6_st 0.685, relay6Cage_st 0.794; D_s: −0.273 / −0.006 / −0.273.
## Not changed after this file
Predictors, target, panel, threshold.  Report script to be written before the panel is run and must read only these
files.
