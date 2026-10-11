# PROTOCOL — the standard parametric support gate (Mahalanobis, SIL-C style) vs our joint-support monitor FB_S
Written 03/10/2026 13:0x EDT (day wake), before any panel run of FB_M*; one non-panel smoke (4×4 relayCK1_s0, iid, 9001 × 8:
RELAY 1841, Z 1888, FB_S / FB_M / FB_M95 / FB_Mq 1888 with 413–416 of 416 decisions flagged; seen).
Why: reviewers (SIL-C, LITERATURE_DEEP_READ) expect a χ²-quantile / Mahalanobis support gate as the standard fallback baseline
that our monitor FB_S (L-293) must beat.  Script scripts/MARL_e3_fallback_eval_v2.py (v1 + FB_M, FB_M95, FB_Mq; stored-row parity).
Design: the SAME feature as FB_S (the joint age-count key without its time bin), Gaussian fit on the receiver's own calibration
views (the existing e3_fallback_20261002/<net>/cal_<arm>_s<s>/calib.json, unchanged), pseudo-inverse (singular: counts sum to a
constant); FB_M flags d² > χ²_0.99(rank), FB_M95 χ²_0.95, FB_Mq the empirical 99 % quantile of d² on the calibration views.
Measured on the calibration views (s0): χ² gates false-alarm 5.6–15.4 % (nominal 1 %; counts are discrete, non-Gaussian);
FB_Mq 0–3.9 %; FB_S (LOO) 0–5.2 %.  Panels = the #3 panels (4×4 4901–4964 seeds 0–9: relayCK1, relayCage × K ∈ {1, iid, 2, 3};
3×3 4801–4864 seeds 0–4: relayCK1, relay6Cage × K ∈ {1, iid, 2, 3}) so that RELAY and FB_S are re-run and must equal the stored
rows exactly (self-check, every episode); Z from the stored Z_s rows.  FB_S results on these panels are known (L-293); FB_M* not.
Predictions (fixed now; gain vs Z, same definitions as L-293):
* FM1 at the 4×4 upgrade hazard (relayCK1, iid) FB_Mq recovers ≥ ½ of the RELAY deficit (as FB_S).
* FM2 cost of the χ² gate: in the own-channel benefit cells (relayCK1 K1, relayCage iid; both nets) FB_M keeps < 0.75 of RELAY's
  gain in ≥ 1 cell, while FB_S keeps ≥ 0.75 everywhere (L-293 FB2) — the textbook gate is costly on discrete count features.
* FM3 non-inferiority of ours: FB_S ≥ FB_Mq − 0.3 points in every 4×4 cell.
* FM4 ranking: Spearman(FB_Mq rate, −gain RELAY) ≥ 0.6 on 4×4 (FB_S: +0.83).
Reported: 3×3; FB_M95; fallback rates; cells where FB_Mq beats FB_S.
Limits: simulation only; own receivers; no real controller logs / J2735 / independent stack / real cross-version data.
Parity check (13:0x): one panel episode (4901 x 8, relayCK1_s0 iid) run with --systems FB_S ONLY (no FB_M* value on the panel was computed): RELAY and FB_S equal the stored rows.

## Amendment 1 (14:2x EDT 03/10; pre-result — no FB_M* row has been read; the run is in progress and its eval code is unchanged)
From the audit by subagent B (ledger L-300): (a) FM4 (and the reprinted FB6 of L-293) use AVERAGE ranks for ties (scipy spearmanr);
the earlier argsort-of-argsort ranks depended on cell order; FB_S's comparator becomes +0.88 (4×4) and +0.50 (3×3), verdicts unchanged.
(b) FM2 requires BOTH networks; the report prints INCOMPLETE otherwise.  (c) The FB_Mq calibration false-alarm figure "0–3.9 %" above is
now reproduced by scripts/MARL_e3_fbm_calib_falsealarm.py (output calib_false_alarm.json): FB_M 5.6–15.4 %, FB_M95 7.6–15.4 %, FB_Mq
0–3.85 % across the 30 receivers; FB_Mq exceeds its nominal 1 % because the key at the empirical threshold is counted as above it (a
floating-point tie between the vectorised and the per-view distance) — a property of this run's FB_Mq, reported as such.
