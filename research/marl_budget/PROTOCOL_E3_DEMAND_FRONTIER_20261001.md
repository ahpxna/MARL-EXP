# Pre-specified test 1: does the teacher's decision-demand curve predict the capacity frontier of relay gain?

Written 01/10/2026 10:4x EDT, BEFORE any run on the panel below (user 10:3x: "viết protocol bước 1 và 2 rồi chạy luôn").
Context: PROTOCOL_E3_COMM_VALUE_PREDICTOR_20261001 (P-A1/P-A2 supported on the reserved panel, ledger L-201) used one
number per seed, N_s = Q_s(0).  This test asks whether the WHOLE demand curve Q_s(k) predicts where, in capacity, the gain
appears (EXTERNAL_ANALYSIS_VERIFICATION_20261001.md, item "Q(k)").  Evidence class: confirmatory for the stated rules,
eval-only (no training).

## Panel
Traffic seeds 2801–2864 × headways 8 and 16 s (128 episodes), used once.  Checked unused at 10:3x by parsing the
`traffic_seeds` of every manifest under research/marl_budget (none contains any of 2801–2864).

## Predictors (fixed now; computed from data already on disk, development panel 901–964)
Source: `research/marl_budget/e3_decision_depth_ten_20261001/cage_s<s>_agefirst_low/depth.npz` (V-D10 probe, relay6Cage
closed loop under age-first / low, CACHE base, ε = 0.25, stream = age-first order; 29 952 receiver-steps per seed).
d = number of senders, in stream order, the teacher needs before its action is in A_0.25 of its full-view logits (a
teacher-defined, labelled oracle diagnostic; ledger L-194 for the cache-base caveat).
- Demand curve Q_s(k) = P[d > k]; N_s = Q_s(0) (identical to the V-D10 N_s).
- Satisfiable need S_s(K) = Q_s(0) − Q_s(K) = P[0 < d ≤ K]:

| s | S(1) | S(2) | S(3) | S(4) | S(5) | S(6) | S(7) | N_s |
|---|---|---|---|---|---|---|---|---|
| 0 | 0.0807 | 0.1321 | 0.1607 | 0.1855 | 0.2155 | 0.2543 | 0.2879 | 0.306 |
| 1 | 0.1045 | 0.1673 | 0.2044 | 0.2348 | 0.2824 | 0.3555 | 0.4186 | 0.456 |
| 2 | 0.1001 | 0.1538 | 0.1825 | 0.2068 | 0.2465 | 0.3019 | 0.3591 | 0.391 |
| 3 | 0.0695 | 0.1052 | 0.1295 | 0.1542 | 0.1840 | 0.2197 | 0.2484 | 0.268 |
| 4 | 0.0857 | 0.1275 | 0.1537 | 0.1782 | 0.2205 | 0.2681 | 0.3086 | 0.334 |
| 5 | 0.0579 | 0.1067 | 0.1479 | 0.1860 | 0.2250 | 0.2625 | 0.2945 | 0.316 |
| 6 | 0.0806 | 0.1232 | 0.1552 | 0.1779 | 0.2092 | 0.2419 | 0.2727 | 0.296 |
| 7 | 0.1270 | 0.1817 | 0.2107 | 0.2285 | 0.2691 | 0.3299 | 0.3826 | 0.405 |
| 8 | 0.0318 | 0.0517 | 0.0665 | 0.0789 | 0.0904 | 0.1014 | 0.1122 | 0.118 |
| 9 | 0.0533 | 0.0781 | 0.0990 | 0.1162 | 0.1304 | 0.1466 | 0.1614 | 0.172 |

- Predicted frontier SHAPE (mean over seeds, normalised at K = 7): D̃(K) = 0.278, 0.431, 0.531, 0.614, 0.728, 0.872, 1.000.
  Null shapes: STEP (any message suffices) = 1 for every K ≥ 1; LINEAR = K/7.
- Known limitation, stated before the run: across seeds the ranks of S_s(K) agree with those of N_s at 0.89–1.00 for
  every K, so the curve can add information only through the SHAPE in K, not through the cross-seed ranking.

## Arms (all trained; no training)
- Relay students relay6Cage_st_s0 … s9 (age-first trained, 185-bit saturated layout), evaluator
  `scripts/MARL_e3_delivery_eval_relay_v6.py` (sha256 f925751b…; = the SATROT evaluator plus const<k>; parity with the
  satrot rows checked 10:3x on seed 901 × 8/16, byte-identical) with `--relay age --quant 4 --order agefirst
  --deliveries prefix --capacity const<K>`, K = 1, …, 7 (every receiver decodes K packets at every step).
- Comparator: the same-seed zero-byte students distill_none_s0 … s9, `scripts/MARL_e3_delivery_eval_v6.py` (sha256
  fcd0dad7…) `--deliveries none --capacity iid` (capacity cannot affect a zero-byte student: L-203).
- Checkpoint sha256 prefixes (F7 of the audit): `research/marl_budget/e3_demand_frontier_20261001/CKPT_SHA256.txt`,
  copied from the scratch record made at 10:39 before any run.

## Endpoint
gain_s(K) = −(Σ waiting relay / Σ waiting Z − 1) × 100 over the 128 paired episodes (positive = relay better).

## Predictions and rules (fixed now)
- **P1 (shape).** ḡ(K) = mean over seeds of gain_s(K); g̃(K) = ḡ(K) / max_K ḡ(K).  MAD(x) = mean over K = 1…7 of
  |g̃(K) − x(K)|.  SUPPORTED iff MAD(D̃) < MAD(STEP) and MAD(D̃) < MAD(LINEAR).  Reported with a two-level bootstrap
  (resample seeds, then traffic seeds within each, 4000 draws, generator seed 0) of P(MAD(D̃) < both).
- **P2 (replication of the N_s law on a new panel and a new capacity process).** Ḡ_s = mean over K of gain_s(K).
  SUPPORTED iff Spearman(N_s, Ḡ_s) ≥ 0.5.
- **Kill rule for the demand-curve line:** if P1 and P2 both fail, the demand curve is not pursued further (N_s is then a
  reserved-panel / capacity-process-specific correlate); if only P2 holds, the scalar law stands and the curve is
  dropped; if only P1 holds, the shape is reported as development evidence for one more pre-registered test.
- **Secondary (reported, no rule):** per-K Spearman(S_s(K), gain_s(K)) and Spearman(N_s, gain_s(K)); the smallest K at
  which ḡ(K) has its lower bound above 0; monotonicity of ḡ in K; per-seed frontiers; bytes per episode.

## Not changed after this file
Panel, arms, evaluators, predictors (the table above), endpoint, P1, P2, kill rule.  The report script
`scripts/MARL_e3_demand_frontier_report.py` is written before the runs and reads only these files.
