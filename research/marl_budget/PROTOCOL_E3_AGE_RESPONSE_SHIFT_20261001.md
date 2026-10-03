# Pre-specified EXPLORATORY test of H-C: does the learned age-response curve follow the TRAINING age distribution?

Written 01/10/2026 23:0x EDT (`date` 23:07:29), before any run below.  User 23:0x: "xong H-C chưa".  H-C (MARL_DIRECTION_
BRAINSTORM): remote-inference AoI theory (Shisher–Sun, arXiv 2404.16281) assumes the learned error function e(δ) transfers to
deployment regardless of the AoI distribution; for a learned receiver e(δ) should instead depend on the AoI distribution
it was TRAINED on.  Half the evidence exists (L-227): the iid-trained relay6Cage_st peaks at relayed-age labels 1–2 (its
training ages: channel histogram at iid 7621 / 6110 / 855 / 57 copies at ages 0 / 1 / 2 / 3, none older) and falls with age.

## Test
scripts/MARL_e3_age_response_probe_v2.py (v1 with --tag; same closed loop and relabelling: every relayed entry's age label
set to a = 0..10, content unchanged, the student's argmax scored in the teacher's A_0.25) on relayCK1_st_s<s> (trained at
const K = 1: relayed ages 1–8 in training, channel histogram 1800 / 1728 / 1656 / 1584 / 1176 / 1120 / 1064 / 864 at ages
1–8), s = 0–3 (s4 still training), K = 1 and iid states, development episodes 901–904 × 8/16 (the train-match target
panel is not touched).  Comparator: v1's numbers for relay6Cage_st_s0–3 (same episodes).
Caveat: each student is scored on its own closed-loop states (d^R of that student).

## Predictions (fixed now), on K = 1 states
- HC1 (primary): drop from the curve's peak (over a = 1..10) to a = 8 is smaller for relayCK1 than for relay6Cage of the same
  seed in ≥ 3 of 4 seeds.  relay6Cage drops: 0.169 / 0.001 / 0.218 / 0.137 (s0–s3).
- HC2: the range max − min of acceptability over a = 1..8 (relayCK1's training range) is smaller than relay6Cage's in ≥ 3 of
  4 seeds.
- Reported, no rule: the peak age; the a = 0 value (never seen for relayed copies by either student); iid-state curves.
Reading fixed now: HC1 → the learned error-vs-age function moves with the training age distribution (H-C supported: the
"AoI function" of a learned receiver is a property of its training channel, not of the data alone).  HC1 failing → the
relabelling sensitivity is not explained by training support.
