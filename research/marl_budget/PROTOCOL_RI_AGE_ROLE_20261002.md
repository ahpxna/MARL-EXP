# Pre-specified test: the ROLE of the age label decides which repair of an upgrade works

Written 02/10/2026 12:2x EDT (`date` 12:21:20 before the testbed; this file after a smoke that printed training losses only),
BEFORE any full run.  User 12:2x: "v giờ làm gì với cái phát hiện này" (L-261: relabelling the age hurt the remote-inference
predictor by −0.50, while in the MARL receivers age is hypothesised to be a reliability cue).

## Hypothesis
For a learned receiver, the age label plays two roles: a RELIABILITY cue (how much to trust the remote copy against local
information) and a PROPAGATION horizon (how far the remote state must be extrapolated).  Relabelling a fresher copy with an
older label (the training-free age remap) is conservative — and safe — when age is only a reliability cue (a driftless
source: the best use of a copy is a weight, and a smaller weight than optimal is never worse than ignoring the copy), and
biased when age is a propagation horizon (a drifting source).  Emulation (feeding a genuinely older buffered copy) is always
consistent; the freshest in-support emulation should be the best consistent choice.

## Testbed (scripts/RI_age_role_testbed.py, fixed now)
z_{t+1} = 0.98 R(λ) z_t + 0.3 ε (rotation λ rad/step), remote X = z + noise 0.05, local L = z + noise 1, target z_t; input
[L, X_{t−δ}, δ/10]; MLP as RI_aoi_shift; trained on δ ~ U{4..7}; deployed at δ ~ U{a..a+3}, a = 0..8; at a = 0..3 also LABEL
REMAP (label δ + 4 − a), FULL EMULATION (δ' ~ U{4..7}) and MINIMAL EMULATION (δ' = max(δ, 4)).  λ ∈ {0, 0.1, 0.2, 0.4};
seeds 0–4; gain = 1 − MSE/MSE(silent local-only predictor); means over seeds.

## Predictions (fixed now)
- AR1 (role decides the remap): the remap harm h(λ) = mean over a = 0..3 of (plain − remap) rises strictly with λ over the
  four values.
- AR2 (driftless safety, the theorem's prediction): at λ = 0 the remap gain is ≥ 0 (not worse than silence) at every
  a = 0..3, and |h(0)| ≤ 0.02.
- AR3 (best consistent repair): minimal emulation ≥ full emulation at every λ and a = 0..3.
- Reported, no rule: the upgrade regression r(λ) = plain(a = 4) − plain(a = 0); plain vs emulation at a = 0..3.
Reading fixed now: AR1 + AR2 → whether a training-free relabel can repair an upgrade is decided by the role of age in the
receiver (reliability vs propagation), which a deployer can probe; AR3 → the network-side repair of an upgrade should
throttle only to the edge of the training support.  Exploratory: n = 5.  Report scripts/RI_age_role_report.py written before
the run.
