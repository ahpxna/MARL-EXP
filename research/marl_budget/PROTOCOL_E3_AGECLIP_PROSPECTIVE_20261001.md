# Pre-specified PROSPECTIVE test: re-labelling out-of-range copy ages at deployment removes the K = 1 loss

Written 01/10/2026 12:14:15 EDT (`date`), BEFORE any run on the panel below.  Source: the exploratory probes
PROTOCOL_E3_NEGFLIP_VS_Z_20261001 (net_Z(1) < 0 on 10/10 seeds; copies at const K = 1 far older than under the iid training
process) and PROTOCOL_E3_AGE_COUNTERFACTUAL_20261001 (decision level: clip +0.030, reaching Z's acceptability), plus a
development-panel closed-loop look (seeds 0–3, seed901–904 × 8/16: clip effect +4.94 / +0.24 / +0.35 / −0.01 %).

## Panel
Traffic seeds 3101–3164 × headways 8 and 16 s (128 episodes), used once; checked unused at 12:1x by parsing every
manifest's traffic seeds (maximum used 3064).

## Arms (seeds 0–9)
- R_none: relay6Cage_st_s<s>, age-first, relay v2 merge, 3 B codebook, scripts/MARL_e3_ageclip_eval.py --A -1 (parity with
  the relay v6 evaluator path verified on the development panel at const K = 1 and iid);
- R_clip: the same with --A 2 (every entry of the merged view older than 2 decision steps — the iid 95th percentile of the
  maximum copy age — is read by the actor with age 2; the protocol state is unchanged; deployable, no oracle);
- Z: distill_none_s<s>, scripts/MARL_e3_delivery_eval_v6.py, no messages.
Capacities: const K = 1 and iid.  Endpoint per pair: −(Σ waiting X / Σ waiting Y − 1) × 100 over the 128 paired episodes.
Uncertainty: two-level bootstrap (seeds, then traffic seeds within each; 4000 draws; generator seed 0).

## Rules (fixed now; unit = seed, n = 10)
- A1 (primary): at const K = 1, clip effect (R_clip vs R_none) mean > 0 with bootstrap lower bound > 0.
- A2 (loss removed): at const K = 1, R_clip vs Z mean gain with bootstrap lower bound > −0.5 % (non-inferiority);
  "reversed" additionally reported if the lower bound > 0.  (R_none vs Z at K = 1 was −1.65 / −1.45 % on two panels.)
- A3 (no harm in the training regime): at iid the 95 % interval of the clip effect lies inside [−0.5, +0.5] %.
- A4 (secondary): Spearman(development decision-level clip gain acc_clip − acc_S at K = 1, clip effect at K = 1) ≥ 0.5;
  predictor table: s0 +0.046, s1 +0.000, s2 +0.081, s3 +0.041, s4 +0.017, s5 +0.012, s6 +0.037, s7 +0.037, s8 +0.016, s9 +0.015.
- If A1 fails, the age-feature reading of the K = 1 loss is not supported at task level.
Launcher `scripts/RUN_marl_e3_ageclip_prospective.sh`, report `scripts/MARL_e3_ageclip_prospective_report.py`, both written
before the runs.
