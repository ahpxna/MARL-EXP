# Channel–receiver compatibility: what the 02/10 night established, and the mechanism it points to

Written 02/10/2026 11:4x EDT (`date` 11:42).  User 04:0x / 11:3x: "research trong lúc 4x4 chạy".  Sources: ledger L-249 (E1),
L-250 (train-match), L-252 (architecture control), L-256 (E4), L-258 (out-of-sample decomposition).  All 3×3 CityFlow,
age-first relay, 3 B codebook; Z = the distilled zero-byte student.  n = 3–10 seeds per cell; two-level bootstrap.

## 1. The chain of evidence (pre-registered unless marked)
| Step | Question | Result | Status |
|---|---|---|---|
| Detection | Does a channel-only count predict the sign of relay-vs-silence? | net/(m−1) > θ; ρ +0.983 in sample, 6/6 prospective hold cells (L-239, L-240) | coordinate post hoc, then out of sample |
| Cause 1 | Is the K = 1 loss the receiver's training mismatch? | Train at K = 1: +2.40 % vs Z (5/5), +4.18 % vs the iid-trained (TM1, TM2, L-250) | pre-registered |
| Cause 2 | Is it one architecture's weakness? | Attention and per-slot also lose at K = 1, win at iid (AC1 both, L-252) | pre-registered |
| Band | Can a better channel hurt? | The K = 1-trained receiver: +2.40 % at K = 1 → +0.29 % at iid (P-UP2, 5/5) | pre-registered |
| Law | Is it governed by train/deploy distance? | Spearman(W1, gain) = −1 for both receivers (ML1, ML2, ML4; L-249); crossing at K ≈ 2, not 1–2 (ML3 failed) | pre-registered |
| Replication | Does the law transfer to a new panel with frozen parameters? | 4/4 cells, error ≤ 0.35 points (L-258) | post hoc in time, zero free parameters |
| Fix | Can one receiver cover the feasible set? | Mixture-trained: ≥ 0 at every K (+0.97 % at K = 1, 9/10), no cost at iid (+0.05 %), best worst case; ≈ 1-point premium for the specialist at K = 1 (MX1, MX2, MX4; MX3 failed; L-256) | pre-registered |
| Limit | Can a scheduler repair it? | At K ≤ 2 no scheduler can lower the count (Lean net floor attained by age-first; count-deadline reduction exactly 0, L-240) | proved + measured |

## 2. The mechanism the numbers fit
gain(receiver r, channel K) ≈ q(K) + a_r − c · W1(P_K, P_train(r)),  c ≈ 1.25 % per W1 unit (ages in decision steps).
* q(K) — the information the channel carries: a big step from K = 1 to K = 2, then flat (E1's inferred q: 1.20 / 2.81 /
  3.10 / 3.04; the mixture-trained curve, where compatibility is mostly removed: 0.97 / 1.92 / 2.16 / 2.15).  Information
  saturates early on this network.
* W1(P_K, P_train) — channel-only, computable before deployment from the age histograms of the merged views, needs no policy.
* Consequence: most of the variation between receivers is compatibility, not information.  The design rules follow:
  (i) measure W1 between the deployment and the training age histograms before deploying; (ii) if the deployment set is
  known, train on its mixture (minimax); (iii) a receiver trained on a poor channel should be GIVEN that channel (throttling
  restores compatibility: relayCK1 is better at K = 1 than at iid on every seed).
* The mixture receiver is described only partly by the W1 to its pooled histogram (corr 0.79 / 0.91, residuals ≈ 1 point,
  L-258) — it sits between "a receiver trained on the average histogram" and "a receiver that identifies the regime and
  is matched to each".  Hypothesis (H-RID, untested): the mixture receiver infers the regime from its view (e.g. the number
  of fresh entries reveals K) and conditions its age response on it.  Test: its age response (the H-C probe) split by
  regime should differ, and the specialist premium at K = 1 should shrink with regime-labelled inputs.

## 3. Theory status
* `LeanMarlMismatchW1V1` (new, 02/10): |E_p g − E_q g| ≤ L · W1(p, q) on the ages (discrete Kantorovich–Rubinstein via Abel
  summation), W1 convex under mixtures, the bound attained.  Grounds the linear law under a MODEL assumption (value =
  expectation of an L-Lipschitz age response); the assumption is not proved for the learned receivers.
* Receiver floor / net floor / prefix instance (V1, V2, PrefixInstanceV1, NetFloorV1): which channels force out-of-support
  copies for every scheduler.
* Not proved: the link from the count or W1 to the return (empirical); any optimality of the mixture.

## 4. Against the literature (abstract-level unless noted; searches 02/10 11:3x)
| Our piece | Closest | Known there | Ours adds |
|---|---|---|---|
| Train on the deployment channel helps | MARL with communication-constrained priors (arXiv 2512.03528, read in full HTML): test-matched dropout priors beat generic ones | matching helps; only equal-or-harsher test conditions evaluated; no transfer metric; no-comm baseline is plain MADDPG | the opposite direction (upgrade hurts) with return evidence; a channel-only distance that predicts transfer, out of sample; a strong distilled silent comparator |
| Mixture training is minimax | Domain randomization theory (Chen et al., ICLR 2022, arXiv 2110.03239): sim-to-real gap bounds | DR near-optimal in the worst case | quantified specialist premium (≈ 1 point at the K = 1 corner), and that the remaining curve is the information term |
| W1-Lipschitz transfer bounds | Lipschitz model-based RL (Asadi et al. 2018), Wasserstein robust MDPs, imitation bounds (arXiv 2212.03922) | value moves at most L·W | the distance is on the CHANNEL's age histogram, policy-free, measured to be linear with a stable slope across panels |
| Random-delay RL | DA-Dreamer / conservative agents (arXiv 2509.20869, 2507.18992) | a good method should do better under shorter delays (else pad the delay) | learned communicating receivers violate it (P-UP2); padding = throttling restores it |
| Latency in collaborative perception | SyncNet (ECCV 2022), V2X-ViT: train with random latency 0–500 ms | randomised latency training; degradation with latency | the both-sided law and its channel-only predictor |
Verdict: the three claims of 02/10 00:5x (training-relative band, channel-only predictive coordinate, scheduler
impossibility) remain unfound; the W1 law and its frozen-parameter replication strengthen claim 2; E4 is a confirmation
of a known principle (randomisation / mixture), now with its premium measured.

## 5. Next experiments (cheap first)
1. H-RID probe (eval-only, minutes): the mixture receiver's age response by regime; is the regime decodable from its view?
2. A prospective W1 test: a receiver trained at const K = 2 (one regime between the two specialists; 5 trainings × ≈ 40 min)
   — its gains at K = 1, 3, iid are predicted NOW by the frozen law (q from E1, c = 1.25, offset unknown: predict the
   SHAPE, i.e. the three differences to relay6Cage), then measured on an unused panel.  This is the cleanest prospective test
   of the law.
3. The 4×4 network (running): only iid-trained receivers there, so it tests detection (Addendum 4, C-rel vs C-abs), not the
   W1 law; a 4×4 K = 1-trained receiver would be the second-network test of the band.
