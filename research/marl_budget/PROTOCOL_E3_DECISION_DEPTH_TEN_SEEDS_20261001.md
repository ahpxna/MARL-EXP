# Pre-specified secondary test: does the TEACHER's message need predict the relay gain? (V-D10)

Written 01/10/2026 01:08 EDT, BEFORE any V-D run on seeds 2–9 (ledger L-192).  Development panel 901–964 × 8/16 (the
same panel as the existing relay6Cage satrot evaluations and the seed-prediction report; NOT the reserved panel
2701–2764).

## Measurement
`scripts/MARL_e3_decision_depth_probe.py` with `--relay relay6Cage_st_s<s> --teacher set_full_s<s> --order agefirst
--rule prefix --capacity low`, parity against `e3_satrot_eval_20260930/relay6Cage_st_s<s>_agefirst_low/rows.json`,
s = 0 … 9.  Per seed, the teacher's MESSAGE NEED N_s = 1 − (share of receiver-steps whose teacher action with NO
decoded sender is in A_ε), at ε = 0.25 (primary; 0 and 1.0 secondary).  A_ε is the teacher-defined acceptable set
(labelled proxy, not ground truth).

## Prediction (written before the runs)
- Spearman(N_s, −G_s) ≥ 0.5, where G_s is the development relay-vs-zero-byte effect of `e3_seed_prediction_report_20260930.json`
  (more teacher message need ↔ larger relay gain).  Also reported: Spearman(N_s, −H_s) against the BYTEBUDGET headroom.
- Reading: N_s is a policy-specific proxy of the obstruction mass of the zero-byte observation
  (`LeanMarlObstructionMassV1`); a positive association supports "communication gains where the zero-byte observation
  hides obstructions"; no association means the gain is not explained by the teacher's own message need.

## Not changed after this file
Arms, panel, ε, statistic, threshold.

## ADDENDUM 01:15 EDT (written before any V-D10 result was read; the primary analysis above is unchanged)
While checking v1 smoke numbers, it was found that `env.counterfactual_view` keeps every non-heard sender as a STALE
CACHE entry (direct receptions of earlier steps), and the teacher's encoder reads the cache.  So the v1 quantity above is
"the teacher's message need ON TOP OF its direct cache".  This is the quantity the primary analysis uses, as specified.
A v2 probe (`scripts/MARL_e3_decision_depth_probe_v2.py`, `scripts/RUN_marl_e3_decision_depth_v2.sh`) records the same
quantity AND the pure decision depth with an EMPTY base (cache stripped); the empty-base N_s is reported as a SECONDARY,
not pre-registered, analysis.  (A v2 bug — the `base` argument shadowed by a loop variable — was found by its own smoke
test, where the two bases agreed exactly, and fixed before any v2 run.)
