# EXPLORATORY: why is the decision-level net_Z positive while the return is negative (4×4, K = 1, seed 0)?

Written 01/10/2026 19:09:50 EDT, before the runs.  Trigger: e3_g4_s0_devlook (L-219): net_Z +0.010, closed-loop −4.95 %
(one seed, 8 episodes).  Probe scripts/MARL_e3_negflip_probe_v3.py (smoke on 3×3: relay / Z flags equal v1, queue parity).
Runs: 4×4 seed 0 at const1, const2, iid (seed901–904 × 8/16); 3×3 seeds 0–9 at const1 (reference: net_Z −0.026 there);
4×4 seed 0 return on 24 more development episodes (seed905–916 × 8/16), relay (ageclip eval, A = −1) vs Z.
Expectations stated now:
- E1 scoring on d^R: at 4×4 K = 1 the relay's acceptability on its OWN states is below Z's on Z's OWN states, although on the
  relay's states the relay is ahead (the relay's states are harder).
- E2 graded regret: mean teacher regret top − L(a) of the relay exceeds Z's on the relay's states at 4×4 K = 1.
- E3 timing: the per-step queue gap relay − Z at 4×4 K = 1 opens in the first third of the episode (coverage phase).
- E4 robustness: the 32-episode 4×4 K = 1 gain is below −2 %.
