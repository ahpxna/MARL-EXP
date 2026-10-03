# Pre-specified test: projecting the (coverage, time) pair into the training support repairs the 4×4 K = 1 loss where the clip failed

Written 02/10/2026 13:0x EDT (`date` 13:05:43 before writing), BEFORE any run on the panel below (smokes on development episode
901 only: identity at iid — 0 views moved, same queue — and 400 of 416 views moved at K1; no gain looked at).  User 13:0x:
"chạy thêm chưa? chẩn đoán kết hợp …".  Source: L-272, a double dissociation (descriptive): 3×3 K1 — max age out of the iid
support (85 %), clip repairs; 4×4 K1 — max age in support, coverage × late-episode out of support (50 %), clip fails (G4).

## Projection (fixed now; scripts/MARL_e3_projection_eval_v2.py --project timecov)
Support table: research/marl_budget/e3_g4_coverage_time_table_iid_20261002.json (4×4 iid channel, development episodes
901–904 × 8/16: for each present count c, the decision steps at which it occurs — c ≤ 12 only at steps 0–5).  The actor reads
its unchanged view with the decision-step feature replaced by the latest step s ≤ t at which the table shows its present
count (the earliest if none ≤ t).  Only the time feature moves; nothing else.

## Design
4×4, panel 4301–4364 × 8/16 (checked unused 12:52), seeds 0–9: relayCage_st (iid-trained) plain and timecov at K = 1 and
at iid; Z.  Endpoint, pairing, two-level bootstrap as before.

## Predictions (fixed now)
- TP1 (repair where the clip failed): timecov vs plain at K = 1, mean > 0 with bootstrap lower bound > 0.
- TP2 (no harm in the training regime): at iid the 95 % interval of timecov vs plain lies inside [−0.5, +0.5] %.
- Reported: timecov vs Z at K = 1 (does it remove the reversal?).
Reading fixed now: TP1 + TP2 → the 4×4 reversal is a JOINT-support failure (coverage persisting late) and its repair is the
projection of that joint statistic — "repair = projection of the out-of-support statistic" holds across networks with
different culprits; TP1 failing → time also carries non-support information the receiver needs (demand phase), and the
minimal-move projection of a joint statistic is not free.  Exploratory: n = 10.
