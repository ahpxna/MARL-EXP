# Pre-specified test E1: a both-sided MISMATCH LAW for learned receivers (quality vs compatibility)

Written 02/10/2026 01:2x EDT (`date` 01:18:06 before writing), BEFORE any run below.  User 01:0x: "làm E1".  Source:
MARL_RESULTS_VS_LITERATURE_20261002.md (E1); interim TM3 (L-238); H-C (L-237); Smith-predictor delay mismatch (both
directions degrade).

## Design
Panel 3701–3764 × headways 8 / 16 (checked unused 01:18 by parsing every manifest's traffic seeds), used once.  Students
seeds 0–3 (relayCK1_st_s4 is still training; it may be added later by an addendum before its rows exist):
relay6Cage_st_s<s> (trained iid) and relayCK1_st_s<s> (trained const K = 1), each at const K = 1, 2, 3 and iid
(scripts/MARL_e3_ageclip_eval.py --A -1, the train-match evaluator); Z = distill_none_s<s> (scripts/MARL_e3_delivery_eval_v6.py).
Mismatch x = Wasserstein-1 distance between the deployment and the training channel's merged-view age histograms
(channel-only, g3_nopolicy composition; fixed now):
| student | K = 1 | K = 2 | K = 3 | iid |
|---|---|---|---|---|
| relay6Cage (train iid) | 2.837 | 1.107 | 0.366 | 0 |
| relayCK1 (train K = 1) | 0 | 1.730 | 2.472 | 2.837 |
The channel itself improves with K for both students (net count rises), so QUALITY predicts gains rising with K for both;
COMPATIBILITY predicts relay6Cage rising and relayCK1 FALLING with K.

## Predictions (gain vs Z, mean over seeds 0–3)
- ML1: for each student, Spearman(x, gain) over the four capacities ≤ −0.8.
- ML2 (the discriminating one): relayCK1's gain at iid < at K = 2 < at K = 1 (falling as the channel improves).
- ML3 (crossing): relayCK1 > relay6Cage at K = 1; relay6Cage > relayCK1 at K = 2, K = 3 and iid.
- ML4: pooled over the 8 (student, capacity) cells, Spearman(x, gain) ≤ −0.7.
Reading fixed now: ML1–ML3 → the value of communication for a learned receiver is governed by its training–deployment
channel mismatch on both sides (a compatibility band, not channel quality); ML2 failing (relayCK1 rising with K) → channel
quality dominates and the band is one-sided.  Exploratory: n = 4 seeds; two-level bootstrap reported, no significance
rule.  Launcher scripts/RUN_marl_e3_mismatch_law.sh and report scripts/MARL_e3_mismatch_law_report.py written before the run.
