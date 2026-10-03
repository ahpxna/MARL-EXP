# Pre-specified PROSPECTIVE test of the W1 mismatch law with a NEW training channel (const K = 2)

Written 02/10/2026 11:4x EDT (`date` 11:44:41 before writing), BEFORE any training or evaluation below.  User 11:3x:
"research trong lúc 4x4 chạy".  Source: MARL_COMPAT_MECHANISM_20261002.md §5.2; the law of L-249 (E1, fitted on panel
3701–3764) replicated with frozen parameters on panel 3801–3864 (L-258) for the two receivers it was fitted on.  It has never
been tested on a receiver trained on a channel it was not fitted on.  This test does that, with every parameter frozen.

## The law (frozen)
gain(r, K) = q(K) + a_r − c · W1(P_K, P_train(r)),  c = 1.252 % per W1 unit (E1), W1 on the g3_nopolicy merged-view age
histograms (research/marl_budget/e3_channel_composition_20261001/g3_nopolicy/composition.json, ages 0–14, normalised).
For two receivers on the same panel the information term q(K) and the panel cancel:
d(K) = gain(relayCK2, K) − gain(relay6Cage, K) = (a_CK2 − a_6) − c · [W1(P_K, P_2) − W1(P_K, P_iid)].
W1 to P_2 (computed now): K1 1.730, K2 0, K3 0.742, iid 1.107; to P_iid: 2.837, 1.107, 0.366, 0.
Predicted d(K) − d(iid) (no free parameter): K1 +2.77, K2 +2.77, K3 +0.92, iid 0.
Likewise e(K) = gain(relayCK2, K) − gain(relayCK1, K), predicted e(K) − e(K1): K1 0, K2 +4.34, K3 +4.34, iid +4.34.

## Arms
- relayCK2_st_s<s>, s = 0–4: scripts/MARL_e3_actor_distill_v9.py, the relayCK1 recipe (teacher set_full_s<s>, prefix
  delivery, relay age, order agefirst, quant 4, 500 iterations) with --capacity const2; watchdog WITHOUT --out, 20 retries,
  --park-if-no-state.
- Comparators on the same panel: relay6Cage_st_s0–4 (trained iid), relayCK1_st_s0–4 (trained const 1), Z = distill_none_s0–4.
Panel: traffic seeds 3901–3964 × headways 8 / 16 (checked unused 11:43 by parsing all 210 444 manifest / config files under
research/marl_budget), used once.  Capacities K = 1, 2, 3 and iid (scripts/MARL_e3_ageclip_eval.py --K k --A -1; Z with
scripts/MARL_e3_delivery_eval_v6.py --deliveries none --capacity iid).  Endpoint, pairing, two-level bootstrap as
PROTOCOL_E3_TRAIN_MATCH_K1 (mean over seeds 0–4).

## Predictions (fixed now)
- W1a (signs): d(K1) − d(iid) > 0, d(K2) − d(iid) > 0, d(K3) − d(iid) > 0.
- W1b (quantitative, zero free parameters): over the four capacities, Pearson(predicted, observed) of d(K) − d(iid) ≥ 0.9
  AND max |observed − predicted| ≤ 1.0 point; the same for e(K) − e(K1).
- W1c (the law's distinctive shape): |d(K1) − d(K2)| < |d(K2) − d(K3)| — flat from K = 1 to K = 2, a step to K = 3
  (moving from K = 1 to 2 brings the iid-trained and the K = 2-trained receivers equally closer, so their difference is flat).
- W1d (band, reported): relayCK2's own gain vs Z peaks at K = 2 or K = 3 (W1 smallest at K = 2, information rising to K = 3).
Reading fixed now: W1a–W1c → the mismatch law is a property of the receiver's training channel, predictive for a new
training channel before any of its runs; W1b failing with W1a holding → the ordering transfers but not the slope; W1a failing
→ the law does not extend beyond the two receivers it was fitted on.  Exploratory: n = 5.
Launcher scripts/RUN_marl_e3_w1_prospective.sh and report scripts/MARL_e3_w1_prospective_report.py written before the run;
started after the 4×4 scheduler finishes (CPU).
