# Pre-specified test A: does clipping an OUT-OF-RANGE age to the training edge help on a downgrade, in the second domain?

Written 02/10/2026 15:1x EDT (`date` 15:12:02 before writing), BEFORE the full run (a smoke printed training losses only).
User 15:1x: "làm A B trước đi".  Source: the interface rule of L-274 / L-279 ("only clip per-entry values outside the trained
range; never relabel in-range values"), supported so far by the 3×3 MARL clip only (+0.79 % prospective, +0.69 %).

## Test (scripts/RI_clip_downgrade.py; the age-role testbed's functions unchanged)
A FAST receiver trained on δ ~ U{0..3}; deployed on δ ~ U{a..a+3}, a = 4..8 (ages never seen).  PLAIN label δ vs CLIP label
min(δ, 3) (content unchanged).  Drift λ ∈ {0, 0.1, 0.2, 0.4}; seeds 0–4; gain = 1 − MSE/MSE(silent).

## Predictions (fixed now)
- CL1 (the interface rule): clip ≥ plain in the mean over a = 4..8, at ≥ 3 of the 4 drifts.
- CL2 (LeanMarlAgeRoleV1, over-trust bound with these noise levels: local variance 1 per coordinate, remote error variance
  ≈ 0.09 δ): at λ = 0 the clip is never below silence (gain ≥ 0 at every a = 4..8).
- Reported: the λ-dependence of clip − plain (under drift the clip under-propagates the copy, plain extrapolates the age input).
Reading fixed now: CL1 → the interface rule (clip out-of-range values to the edge) holds in a second domain; CL1 failing →
the 3×3 MARL clip worked for a domain-specific reason and the rule must be stated as MARL-specific.  Exploratory, n = 5.
