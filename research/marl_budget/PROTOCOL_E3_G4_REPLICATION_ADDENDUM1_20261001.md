# Addendum 1 to PROTOCOL_E3_G4_REPLICATION_20261001: teacher confidence as a pre-registered competitor of N_s

Written 01/10/2026 11:2x EDT.  The 4×4 chain started 11:17; no 4×4 student has finished training and no 4×4 target run
exists.  Trigger: protocol 1b's comparator list (3×3, read 11:2x) showed the teacher's mean full-view top-2 logit margin
predicting the realised gain about as well as N_s (dev 0.612 / reserved 0.709 / panel 2801 0.758 vs N_s 0.794 / 0.685 /
0.661; margin–N_s rank correlation 0.55; partial rank correlation of N_s with gain given the margin +0.49 / +0.43).
Nothing in the protocol is changed; this adds one rule.

## Added measurement
margin_s = mean over receiver-steps of the teacher's top-2 logit gap on the full fresh view, on the same development
episodes and closed loop as N_s (relayCage_st_s under age-first / low, seed901–932 × 8 / 16), recorded by
`scripts/MARL_e3_teacher_margin_probe.py` (written before it runs; a light probe: no subsets, no rollouts).

## Added rule (fixed now)
- R4 (specificity beyond teacher confidence): Spearman(N_s, gain_s) > Spearman(margin_s, gain_s), AND the partial rank
  correlation of N_s with gain_s given margin_s (linear residuals of ranks) ≥ 0.3.  If R2 holds but R4 fails, the
  claim is stated as "a teacher-side information-reliance measure predicts the gain", not "decision demand".
