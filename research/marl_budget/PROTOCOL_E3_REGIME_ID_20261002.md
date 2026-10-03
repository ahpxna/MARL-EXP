# Pre-specified test H-RID: does the mixture-trained receiver condition its age response on the channel regime?

Written 02/10/2026 12:5x EDT (`date` 12:50:51 before writing), BEFORE any run below.  User 12:4x: "làm hết đi" (the H-RID probe
offered at 12:47).  Source: L-256 (relayMIX covers the feasible set; specialist premium ≈ 1 point at K = 1) and L-258 (the W1
to its POOLED training histogram describes relayMIX only partly).  H-RID: the mixture receiver infers the regime from its view
and uses a regime-conditional age response, like the specialist of each regime.

## Test
scripts/MARL_e3_age_response_probe_v2.py --tag relayMIX_st (the H-C probe, unchanged: every relayed entry's age label set to
a = 0..10, content unchanged, student's argmax scored in the teacher's A_0.25; development episodes 901–904 × 8/16) for
seeds 0–3 at K = 1 and at iid (K = 0).  Comparators: the H-C report's curves of relayCK1 (K = 1-trained) and relay6Cage
(iid-trained), same seeds, states, episodes (research/marl_budget/e3_age_response_shift_report_20261001.txt).
Metric per curve: peak age over a = 1..10 and the drop from the peak to a = 8 (H-C's HC1 metric).

## Predictions (fixed now)
- RID1 (K = 1 states): relayMIX's drop is smaller than relay6Cage's (same seed) in ≥ 3 of 4 seeds AND its peak age ≥ 3 in
  ≥ 3 of 4 seeds (the K = 1 specialist's peaks: 4 / 4 / 4 / 3).
- RID2 (iid states): relayMIX's peak age ≤ 2 in ≥ 3 of 4 seeds (relay6Cage's peaks there: 1 / 1 / 1 / 1).
Reading fixed now: RID1 + RID2 → regime-conditional age response (H-RID supported: the mixture receiver behaves like the
specialist of each regime, which is why the pooled W1 under-describes it); RID1 failing with RID2 holding → it keeps the iid
response everywhere (the K = 1 coverage comes from elsewhere).  Exploratory: n = 4.
