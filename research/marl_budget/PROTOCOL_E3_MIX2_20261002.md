# Pre-specified test C: does a mixture of only the two EXTREME channels (K = 1 and iid) cover the intermediate ones?

Written 02/10/2026 15:1x EDT (`date` 15:16:27 before writing), BEFORE any run.  User 15:1x (queue C after the CPU-heavy jobs).
Thesis: support, not freshness (MARL_LESSONS_AND_STORY_20261002).  The 3×3 support diagnostics show the intermediate channels'
per-entry statistics inside the UNION of the K = 1 and iid supports (K2: fresh count 2 occurs under iid; ages up to 5 occur
under K = 1).  If support is about per-statistic coverage, a K1 + iid mixture suffices; if intermediate JOINT configurations
need their own data, it does not.

## Arms
relayMIX2_st_s0–4: scripts/MARL_e3_actor_distill_v11.py --capacity mix --mix-regimes iid,const1 (balanced 64 / 64 TRAIN,
8 / 8 SELECT; otherwise the relayMIX recipe; self-check TEST_marl_distill_v11_mix2: v11 default = v10 bit-exact).
Comparators: relayMIX_st (4-regime mixture), relay6Cage_st, relayCK1_st, Z (seeds 0–4).  Panel 4501–4564 × 8/16 (unused,
checked at launch), capacities K = 1, 2, 3, iid.  Started only after the 4×4 train-match finishes (queue).

## Predictions (fixed now; means over seeds 0–4)
- C1 (coverage of the middle): relayMIX2's gain vs Z at K2 and at K3 ≥ relayMIX's − 0.3.
- C2 (extremes kept): relayMIX2 at K1 ≥ 0 (lower bound > −0.5) and at iid ≥ relay6Cage − 0.3.
Reading fixed now: C1 → covering the extremes' supports covers the intermediate channels (support = per-statistic
coverage); C1 failing → the joint view configurations of intermediate channels need their own training data.
