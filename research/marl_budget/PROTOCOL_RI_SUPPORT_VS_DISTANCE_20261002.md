# Pre-specified test: SUPPORT coverage, not W1 distance, decides a learned receiver's value (equal-distance receivers)

Written 02/10/2026 13:1x EDT (`date` 13:17:17 before writing), BEFORE the full run (a smoke printed training losses and the W1
values only: A 3.97, B 4.05, C 4.02, D 0.02 — no gain).  User 13:1x (lessons / story).  Thesis to test
(MARL_LESSONS_AND_STORY_20261002.md §3, after Johansson–Sontag–Ranganath 2019): what matters is whether the training
support covers the deployment, not the distance between the distributions.  None of our earlier results holds the
distance fixed while varying the support (in the channel experiments the two co-vary).

## Test (scripts/RI_support_vs_distance.py; the RI_aoi_shift testbed's functions, unchanged)
Deployment δ ~ U{0..3}.  Receivers: A U{4..7} (W1 4, disjoint support); B ½ U{0..3} + ½ U{8..11} (W1 4, covering); C U{0..11}
(W1 4, covering); D U{0..3} (matched, W1 0).  Seeds 0–4; gain = 1 − MSE/MSE(silent).

## Predictions (fixed now)
- SD1: gain(B) > gain(A) and gain(C) > gain(A), in the mean and in ≥ 4 of 5 seeds — at EQUAL W1.
- SD2: |gain(D) − gain(B)| < |gain(D) − gain(A)| and |gain(D) − gain(C)| < |gain(D) − gain(A)| (mean).
Reading fixed now: SD1 + SD2 → the W1 law is a regularity of channel shifts in which distance and support coverage co-vary;
the mechanism is support (the reading of L-266 / L-274: minimising W1 is no repair); SD1 failing → distance itself matters.
