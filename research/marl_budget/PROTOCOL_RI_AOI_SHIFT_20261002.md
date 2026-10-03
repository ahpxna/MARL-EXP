# Pre-specified test, SECOND DOMAIN: AoI-distribution shift for a learned remote-inference predictor

Written 02/10/2026 12:0x EDT (`date` 12:03:25 before writing the testbed; this file after a smoke that printed training
losses only, no gain), BEFORE any full run.  User 11:5x: "làm 1, 2, 4" (step 2 of MARL_DIRECTION_ROUND10_20261002.md).

## Question
Remote-inference AoI theory (Shisher–Sun, arXiv 2404.16281) trains one predictor over "a variety of AoI values" and assumes the
deployment AoI distribution equals the training one.  In our MARL receivers the value of aged information follows the
W1 distance between deployment and training age distributions, and an upgrade (fresher deployment) can HURT (P-UP2, E1).
Does the same hold for a learned remote-inference predictor in their own model, and do the repairs split by direction?

## Testbed (fixed now; scripts/RI_aoi_shift_testbed.py, source sha256 recorded in the manifest)
Noisy damped pendulum; remote sample X = (sin θ, cos θ, θ') + noise 0.05; local sensor L = (sin θ, cos θ) + noise 0.5; target
the current (sin θ, cos θ); input [L_t, X_{t−δ}, δ/10]; MLP 6–64–64–2 tanh, Adam 1e-3, batch 512, 20 epochs, 200 000 training
and 100 000 test samples (independent trajectories); silent predictor f0 on L only (compiled silence's analogue);
gain = 1 − MSE(f)/MSE(f0).  AoI windows δ ~ U{a..a+3}; trained: fast (a = 0), slow (a = 4), mix (U{0..11}); deployed at
a = 0..8; slow-trained at a = 0..3 also with EMULATION (a buffered sample with δ' ~ U{4..7}) and LABEL REMAP (true X_{t−δ},
label δ + 4 − a).  Seeds 0–4.  W1 between two windows of equal width = |a − a'| (shifts).

## Predictions (fixed now; mean over seeds unless stated)
- UR1 (primary: upgrade regression): slow-trained gain at a = 0 < its gain at a = 4, in the mean and in ≥ 4 of 5 seeds.
- UR2 (crossing, as E1): fast-trained > slow-trained at a = 0, and slow-trained > fast-trained at a = 4.
- UR3 (mixture covers the set): mix-trained gain ≥ max(fast, slow) − 0.02 at every a = 0..8.
- UR4 (emulation, the network/receiver-side repair of an upgrade): slow-trained with emulation at a = 0..3 within ± 0.01 of its
  a = 4 gain (stationarity makes this a check of the claim "an upgrade can always be emulated", not a discovery).
- Reported, no rule: gain vs W1 slopes on each side for slow-trained; LABEL REMAP vs plain at a = 0..3 (expected to FAIL
  here, unlike the MARL age remap: this predictor uses δ as a PROPAGATION horizon, not as a reliability cue — mislabelling the
  age mis-propagates); the specialist premium of mix at a = 0 and a = 4.
Reading fixed now: UR1 + UR2 → the training-relative hazard is not specific to MARL; it appears in the remote-inference
model whose theory assumes it away; UR1 failing → in this smooth single-source setting the MLP extrapolates to fresher AoI,
and the hazard needs the richer view of the MARL receivers (scope statement).  Exploratory: n = 5; no significance rule.
Report: scripts/RI_aoi_shift_report.py written before the run.
