# Pre-specified test on the SECOND NETWORK (4×4): train-match at K = 1, the upgrade hazard, the W1 law, and projection

Written 02/10/2026 12:5x EDT (`date` 12:54:59 before writing), BEFORE any training or evaluation below.  User 12:4x: "chạy
luôn cái 4x4 train K=1 sau khi đã chạy xong lean và probe".  Sources: 3×3 train-match (L-250), E1 / W1 law (L-249, L-258),
4×4 const-K target (L-270: iid-trained relay at K1 / K2 / K3 / iid = −2.41 / +2.49 / +5.18 / +6.39 % vs Z), 4×4 support
diagnostics (12:55, descriptive: for a K = 1-trained receiver deployed at iid the FRESH COUNT is out of support at 93 % and
the PRESENT COUNT at 96 % of receiver-steps; at K2 fresh 100 %, present 80 %).

## Arms
relayCK1_st_s<s> on the 4×4 grid, s = 0–9: scripts/MARL_e3_actor_distill_v9.py under MARL_grid_relay_wrapper (nearest8),
teacher set_full_s<s> (4×4), prefix delivery, relay age, order agefirst, quant 4, 500 iterations, --capacity const1 (the
4×4 relayCage_st recipe of PROTOCOL_E3_G4_REPLICATION with the K = 1 training channel; bit-identity of v9 with the chain's
trainer: L-253); watchdog WITHOUT --out, 20 retries, --park-if-no-state.  Comparators: relayCage_st_s<s> (4×4, iid-trained)
and Z = distill_none_s<s> (4×4).
Panel 4201–4264 × 8/16 (checked unused 12:52 by parsing every manifest / config), used once.  Evaluations (4×4 wrappers):
relayCK1 and relayCage at K = 1, 2, 3, iid (scripts/MARL_e3_ageclip_eval.py --A −1); relayCK1 with the onefresh projection
at K = 2, 3, iid (scripts/MARL_e3_projection_eval.py); Z.  Endpoint, pairing and two-level bootstrap as
PROTOCOL_E3_TRAIN_MATCH_K1 (mean over seeds 0–9).  Started only after the full Lean gate and the H-RID probe (user's order).

## Predictions (fixed now)
- GTM1 (rescue on the second network): relayCK1 vs Z at K = 1, mean ≥ 0 and bootstrap lower bound > −0.5 %.
- GTM2 (matching helps): relayCK1 vs relayCage at K = 1, lower bound > 0.
- GTM3 (upgrade hurts, P-UP2 on 4×4): relayCK1's gain vs Z at iid < its gain at K = 1.
- GTM4 (the W1 law with the 3×3 slope, zero free parameters): d(K) = gain(relayCage) − gain(relayCK1); with the 4×4 g4
  histograms (W1 to iid: K1 3.688, K2 2.689, K3 1.085; to K1: K2 1.047, K3 2.615, iid 3.688) and c = 1.252 % per W1 unit,
  predicted d(K) − d(K1) = 0 / +2.56 / +6.53 / +9.23 at K1 / K2 / K3 / iid.  Supported iff Pearson(predicted, observed) ≥ 0.9
  over the four cells; the magnitude (the 4×4 slope fitted on the observed differences) is reported, not ruled.
- GTM5 (exploratory, projection): onefresh vs plain for relayCK1 at iid > 0, but recovering less than half of the gap to
  relayCage at iid (the 4×4 present count is also out of support and onefresh does not touch it).
Reading fixed now: GTM1–GTM3 → the train/deploy compatibility account (rescue by matching, upgrade hazard) holds on a second
network; GTM4 → the W1 law transfers across networks with its slope; failures are reported as scope limits.
Launcher scripts/RUN_marl_g4_train_match.sh and report scripts/MARL_e3_g4_train_match_report.py written before the run.

## Addendum 1 — SUPPORT predictions (written 02/10/2026 15:0x EDT, `date` 15:07:36, BEFORE any evaluation of this protocol exists:
the evaluation directory is empty; round-1 training at iteration ≈ 220/500)
Channel-side support diagnostics of the 4×4 K = 1 training channel (research/marl_budget/e3_support_diagnostics_g4_joint_20261002.json,
development episodes): out-of-support mass of the deployment views for a K = 1-trained receiver — K2: fresh count 100 %, present
count 79.8 %, stale count 66.1 % (FEWER stale entries than K = 1 ever shows); K3: fresh 100 %, present 88.5 %, stale 0 %;
iid: fresh 93.4 %, present 96.2 %, stale 0 %.  Thesis "support, not freshness" (MARL_LESSONS_AND_STORY_20261002):
- SV1: relayCK1 (4×4) gains vs Z at K2, K3 and iid are each BELOW its gain at K1 (every richer channel leaves its support on
  ≥ 80 % of receiver-steps) — the upgrade hazard at every richer channel, not only at iid (GTM3).
- SV2: among the upgrades the gain falls with the present-count violation: gain(K2) > gain(K3) > gain(iid).
- SV3 (the discriminating cell): at K2 the stale count leaves the support in the LOW direction (fewer stale copies); a pure
  "fewer stale copies is better" count reading predicts gain(K2) ≥ gain(K1); the support reading predicts gain(K2) < gain(K1)
  (= SV1 at K2).
Scored with the report (means over seeds 0–9); exploratory.
