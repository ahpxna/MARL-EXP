# Verification of the third external audit ("net decision effect = repair − corruption"), 01/10/2026 11:5x–12:1x EDT

Inputs read: the audit text (user, 11:4x); `scripts/MARL_e3_protocol_demand_{probe,report}.py`; the prospective test
(`PROTOCOL_E3_HARM_PROSPECTIVE_20261001.md`, report 11:55:12); its comparator addendum (written 11:51:58, before the
report existed); the new exploratory probe against Z (`PROTOCOL_E3_NEGFLIP_VS_Z_20261001.md`, written 11:58:37).

## A. Numbers the audit quotes — all CORRECT
1b P1b ρ = −0.079, shape ties linear; margin 0.612 / 0.709 / 0.758 vs N 0.794 / 0.685 / 0.661; whole-fibre κ = 0.019,
obstruction 0.98, teacher action in A_ε 0.31 / 0.33; S^proto at K = 1: N 0.244, S_best 0.160, S_protoS 0.169,
harm_S 0.077, net_S 0.092; harm_S 0.077 / 0.037 / 0.029 / 0.021 / 0.016 (K = 1, 2, 3, 5, 7 — not 1…5); ρ at K = 1
net_S 0.564 vs S_best 0.042 (development-derived, step-1 panel).  Prior art VIL2C, CGDC, CoDe, CAIC, Don't Fire
Together: all exist (round 5 of MARL_NOVELTY_CHECK_DIRECTIONS_20261001.md).

## B. Prospective result (panel 3001–3064, pre-registered)
H1 ρ(net_S(1), gain(1)) +0.527 vs S_best +0.345 → SUPPORTED; H2 K = 1 loss −1.45 %, relay effect [+0.48, +2.49] % →
SUPPORTED; H3 mean ρ +0.705 (+0.527 / +0.806 / +0.782) → SUPPORTED.  Comparators: N +0.200 / +0.733 / +0.685, margin
+0.164 / +0.612 / +0.648.

## C. Where the audit is WRONG or overstates
1. **net_S is an accuracy difference, not a mechanism.**  net_S = P(need ∧ protoS) − P(¬need ∧ ¬protoS) = acc_S − acc_E
   exactly (checked to 1e-16 on all 50 cells), acc_E = teacher-on-local-only acceptability.  Its baseline is the teacher
   fed an empty view, which it never saw in training — not the comparator Z.
2. **net_S has the wrong sign at K = 1.**  Mean net_S(1) = +0.092 on both panels while the realised gain is −1.65 / −1.45 %;
   the relay student is MORE often acceptable than the empty-view teacher (0.848 vs 0.756).  So net_S ranks seeds; it
   does not "explain the K = 1 loss".
3. **"S_best = ideal" is wrong.**  S_protoS (0.169) > S_best (0.160) at K = 1: S_best uses the teacher on direct-subset
   cache views and ignores relayed copies, so it is not an upper bound.  The Paper-A "potential vs realised" analogy
   rests on that label.
4. **The K = 1 advantage of net_S over S_best did not replicate convincingly.**  Development-derived panel: difference
   +0.52 (bootstrap P(> 0) 0.95); prospective: +0.18, 95 % [−0.54, +0.74], P(> 0) 0.69.  H1 passed by its letter;
   ρ = 0.527 has 95 % [−0.20, +0.88].  At K = 2, 3 net_S and S_best are equal (differences −0.01 / −0.02).
5. **"Before deployment" does not hold for net_S.**  It needs the trained relay student run closed loop.  Its natural
   competitor is the development-panel gain (C4): prospective +0.345 / +0.309 / +0.782, step-1 +0.636 / +0.370 / +0.758.
   Neither dominates; the development gain gets the LEVEL right (−1.33 % dev vs −1.45 % target at K = 1).
6. **The components are weak alone.**  Prospective K = 1: acc_S +0.406, −harm_S +0.418, acc_E −0.479 (i.e. N_dev
   +0.479); at K ≥ 2 the N_dev part carries net_S (−acc_E 0.745 vs net_S 0.806 / 0.782).
7. **BYTEBUDGET "should have small S⁻"** is close to a tautology: with every sender delivered the view is almost the full
   view, so the teacher-defined acceptability is ≈ 1 by construction (V-U lesson).  Not a discriminating test.
8. **Paper-1 revival "repair − λ·harm"** is positive-congruent training / compatibility-penalised updates (Yan et al. 2021;
   Bansal et al. 2019).  Not new as a method.

## D. What the audit missed (and is now tested)
- The comparator: negative flips must be counted against Z (correct by Z, wrong by relay), Yan et al.'s definition.
- The training distribution: relay6Cage_st was trained under the iid capacity process; constant K = 1 shifts the age of
  relayed copies (paper_marl_v2 already reports age-shift failures under the congestion order).
- Per-seed gains are a stable seed property across panels (ρ(gain 2801, gain 3001) = 0.794 / 0.939 / 0.915 for K = 1 / 2 / 3),
  so the ceiling for any predictor is high and n = 10 intervals are wide.

## E. Result of the probe against Z (`PROTOCOL_E3_NEGFLIP_VS_Z_20261001.md`, EXPLORATORY, development panel, 12:0x)
Self-checks passed on all 40 cells: Z acting from the empty counterfactual view equals its real-view action at every step
and reproduces the e3_dev_Z rows; the relay closed loop and need / protoS flags equal the protocol-demand probe's.

| K | acc_S | acc_Z | acc_E | repair_Z | flip_Z | net_Z | net_S | mean copy age (steps) | gain 2801 / 3001 |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 0.848 | 0.874 | 0.756 | 0.060 | 0.086 | **−0.026** | +0.092 | 3.06 | −1.65 / −1.45 % |
| 2 | 0.913 | 0.891 | 0.734 | 0.068 | 0.046 | +0.022 | +0.179 | 1.57 | +1.01 / +0.95 % |
| 3 | 0.936 | 0.893 | 0.734 | 0.076 | 0.033 | +0.043 | +0.203 | 0.88 | +1.72 / +1.72 % |
| iid | 0.950 | 0.892 | 0.727 | 0.083 | 0.025 | +0.058 | +0.223 | 0.54 | reserved panel +2.29 % |

- X1 TRUE: net_Z(1) < 0 on 10/10 seeds, > 0 at K = 2, 3 and iid — against the right comparator the decision level has the
  SIGN of the realised gain at every K (net_S had it wrong at K = 1), and gain / net_Z is roughly constant (≈ 40–60 % per unit).
- X3 TRUE: copy age at const K = 1 is 3.06 steps vs 0.54 under the training process (max-age p95 2, p99 3 under iid; median
  7 at K = 1) on 10/10 seeds; 88 % of K = 1 receiver-steps carry a copy older than the iid p95, and flips are 2.23× as
  frequent on those steps (0.092 vs 0.041).  The K = 1 regime is out of the training age range almost everywhere.
- X4 (exploratory, both panels already read): K = 1 ρ(net_Z, gain) +0.709 [+0.06, +0.94] / +0.673 [−0.00, +0.93] vs
  net_S +0.564 / +0.527; K = 2 +0.782 / +0.709 (net_S +0.745 / +0.806); K = 3 +0.547 / +0.395 (net_S +0.697 / +0.782).
  acc_Z alone carries nothing (−0.08 / −0.07): what varies by seed is how far the relay student falls on stale copies.
- Reading: the K = 1 loss is the iid-trained relay student's decisions degrading on copies far older than any it was
  trained on, below the zero-byte student's level.  This is the age-shift mechanism already reported in paper_marl_v2
  for the congestion order, now located at decision level; "communication inherently corrupts decisions" is not shown.
  Not yet separated: age FEATURE extrapolation vs stale CONTENT misleading (next probe), and training at K = 1.

## F. User follow-ups 12:1x (OOD beyond age; train-match rescue; Z parity; d^R caveat) — status
- **Clow is not a control** (configs): relay6Clow_st_s0/s1/s5 = capacity 'low' (K i.i.d. on {1, 2, 3}) under the congestion
  order; neither constant K = 1 nor age-first.
- **Train-match rescue launched** (`PROTOCOL_E3_TRAIN_MATCH_K1_20261001.md`, sha256 49b0ecac…, 12:18:45): relayCK1_st_s0–4
  trained with scripts/MARL_e3_actor_distill_v7.py --capacity const1 (smoke: every revealed K during training and select = 1,
  7956/7956); target panel 3201–3264; TM1 rescue vs Z, TM2 vs the iid-trained student, TM3 iid cost, TM4 dev net_Z.
- **Z parity, full**: on 16 complete development episodes (seeds 0 and 7), at 416/416 steps the encoding of the probe's
  empty view is byte-identical to the evaluator's real no-message view, the evaluator's own Policy object chooses the same
  action for every agent, and the queue sums equal the e3_dev_Z rows; every negative-flip run also asserts action
  equality at every step of every episode.
- **Outcome 1, not 2**: Δacc(1) = net_Z(1) = −0.026 < 0 on 10/10 seeds — the K = 1 failure is visible at the immediate
  decision level; same-state (s ~ d^R) decision effect and whole-trajectory gain agree in sign at K = 1, 2, 3 and iid.
  The caveat stands: Z is scored on the relay's states, so net_Z is not a closed-loop difference.
- **Composition, not only age** (view-statistics probe running, `PROTOCOL_E3_VIEW_OOD_20261001.md`): at const K = 1 the
  merged view is identical across seeds (fresh 1.00, relayed 5.87, never-heard 1.13, stale 3.99, max age 6.36) — the shift
  is set by the channel schedule alone.  The age-clip counterfactual (age feature only, composition unchanged) recovered
  +0.030 of acceptability, which bounds what age alone explains at the decision level.

## G. View-composition result (`e3_viewstats_report_20261001.txt`, EXPLORATORY, 40 cells, parity with the negative-flip probe exact)
| regime | fresh | relayed | coverage | never-heard | stale (> 2 steps) | stale share | max age p50/p90/p99 | flip_Z |
|---|---|---|---|---|---|---|---|---|
| iid (training) | 4.07 | 3.75 | 0.978 | 0.18 | 0.03 | 0.004 | 1 / 2 / 3 | 0.025 |
| K = 1 | 1.00 | 5.87 | 0.859 | 1.13 | 3.99 | 0.519 | 7 / 8 / 8 | 0.086 |
| K = 2 | 2.00 | 5.46 | 0.933 | 0.54 | 1.69 | 0.212 | 5 / 5 / 5 | 0.046 |
| K = 3 | 3.00 | 4.71 | 0.964 | 0.29 | 0.49 | 0.061 | 2 / 3 / 3 | 0.033 |
- V1 FALSE as stated: TV of the fresh count from iid is 0.85–0.88 at every constant K (a constant is a point mass against
  iid's spread over 1–7); TV of stale count / max age / never-heard does fall with K (0.86 / 0.86 / 0.24 at K = 1 →
  0.48 / 0.67 / 0.07 at K = 3).
- V2 TRUE: 84.6 % of K = 1 receiver-steps lie outside the iid joint support of (fresh, stale, max age), 0 % at K = 3 — but
  83.3 % at K = 2, where the gain is positive: out-of-support share alone does not decide the sign.
- Flips at K = 1 rise with the stale count (0.041 with none → 0.097 with five) and the maximum age (≈ 0.06 up to 6 steps,
  0.099 at 7–8).  Under iid, steps with a single fresh sender (in distribution) have flip_Z 0.034 — far below const
  K = 1's 0.086.  So the harmful part of the K = 1 shift is ACCUMULATED STALENESS of relayed copies, not sparsity of
  fresh senders at the step; fresh-count sparsity alone is benign in distribution.

## H. Prospective age-clip result (`e3_ageclip_prospective_report_20261001.txt`, panel 3101–3164, 50 arms; two CityFlow stalls of seed 2 restarted by the watchdog, partial dirs in legacy/)
- A1 SUPPORTED: at const K = 1, re-labelling copies older than 2 steps raises the relay's gain by +0.79 % [+0.05, +1.55].
- A2 NOT SUPPORTED: relay + clip still loses to Z at K = 1, −0.89 % [−1.67, −0.02] (plain relay −1.70 % [−2.92, −0.67]:
  the K = 1 loss replicates on a THIRD panel).  Clipping removes roughly half of the observed mean gap (0.79 / 1.70) —
  not an additive causal decomposition: intervention effects need not add.
- A3 SUPPORTED: at iid the clip effect is −0.03 % [−0.08, +0.01] — harmless in the training regime.
- A4 SUPPORTED: the development decision-level clip gain ranks the seeds' closed-loop clip effect (Spearman +0.644).
- Same-state vs whole-trajectory discrepancy: at the decision level the clip brought the relay to Z's acceptability
  (0.878 vs 0.874), yet the closed loop still loses 0.89 %.  So the A_0.25 decision measure over-states the repair, or the
  remaining loss compounds along the trajectory; the other half of the K = 1 loss is not the age feature.  The
  train-match test (TM1–TM4) decides whether it is a training mismatch in content / composition or the channel itself.

## I. Fifth external note (user 12:4x) verified, and the age-counterfactual dose over K (12:4x, EXPLORATORY)
Correct: "age-feature OOD is a causal contributor to the K = 1 failure, not the whole failure" (A1 prospective, A2 failed);
"roughly half", not a 46 % decomposition; A3 shows the repair acts where the shift is (no generic-regularisation reading);
A4 secondary; A_0.25 is a diagnostic, not an objective; matching average decision acceptability does not imply matching
return (0.878 vs 0.874 acceptability, −0.89 % return).  Tail severity rather than generic OOD distance — now measured:
| regime | P(max age > iid max 3) | E[(max − 2)+] | B_stale = E[Σ_j (a_j − 3)+] | P(≥ 3 stale) | clip gain (decision) | net_Z | gain |
|---|---|---|---|---|---|---|---|
| iid | 0.000 | 0.02 | 0.00 | 0.00 | +0.000 | +0.058 | +2.06 / +2.29 % |
| K = 1 | 0.846 | 4.47 | 8.48 | 0.80 | **+0.030** (9/10 seeds) | −0.026 | −1.65 / −1.45 / −1.70 % |
| K = 2 | 0.833 | 2.24 | 1.64 | 0.00 | **+0.000** (4/10) | +0.022 | +1.01 / +0.95 % |
| K = 3 | 0.000 | 0.49 | 0.00 | 0.00 | +0.000 | +0.043 | +1.72 / +1.72 % |
K = 2 is beyond the training age range on 83 % of steps (max age 5 vs 3) yet the age clip changes nothing there: the actor
tolerates moderate extrapolation and fails only in the far tail (≈ 4 copies of age 6–8 at K = 1).  Exceedance probability
does not separate K = 1 from K = 2; tail burden does.
Addition the note missed: the relay student's input contains Z's (local observation), so a relay student CAN represent Z by
ignoring messages.  If the K = 1-trained student still loses to Z (TM1 fails), the residual is a learning / representation
failure of DAgger distillation on that interface, not missing information; "why is receiving imperfect messages worse than
ignoring them" then becomes the question.
Process fix: the 4×4 waiter would have printed the replication report before Addendum 2's net_Z was computed; it was
replaced (b2jj21wgv stopped — a waiter only; the five chain lanes untouched) by one that runs, in order: R5 development
probes (Z rows, net_Z at iid / low, relay parity against Rdev_low) → margin probes → replication report → R5 report →
the 4×4 const-K launcher (`PROTOCOL_E3_G4_CONSTK_20261001.md`, sha256 86c31bee…, written 12:40:15 before any run).

## J. Sixth external note (user 14:0x: information inclusion, Outcomes A/B/C, tail burden, 4×4 threshold) verified
- **Inclusion holds at the architecture level, verified constructively.**  CommAdapter's own block is local only (lane
  vehicles / waiting, own phase, phase elapsed, decision step); SetActorNet mean-pools φ(sender block)·heard with pooled = 0
  for Z (nothing heard).  A relay-architecture net with Z's body / head weights and φ's last layer zeroed, run through the
  whole relay pipeline (age-first, relay v2 merge, 3 B quantisation) at const K = 1 and at iid, reproduces Z's development
  queue sums on 8/8 episodes each (parity self-check).  So Π_Z ⊆ Π_relay in this implementation, not only in information.
- **bayes_refine exists** (`LeanMarlCommValueV1.bayes_refine`: a finer view never has larger Bayes risk); a single-decision
  statement.  For the closed-loop team problem the same conclusion needs no theorem: every agent can ignore messages, so the
  team-optimal value with relay views is at least Z's.  The K = 1 loss is therefore a gap between the information-monotone
  optimum and what the learner attains — the note is right.
- **Correction to "learner failed"**: the students are trained by DAgger to imitate a privileged teacher, an objective whose
  optimum is NOT monotone in the student's information (the imitation gap, Weihs et al. NeurIPS 2021; causal confusion —
  "access to more information can yield worse performance" — de Haan, Jayaraman, Levine NeurIPS 2019; copycat shortcuts on
  history-like features, Wen et al. NeurIPS 2020).  Stale relayed copies are history-like features correlated with the
  teacher's actions.  So Outcome C would implicate the objective as much as the optimiser.
- **Synchrony (correlated errors across receivers) checked, not supported at the decision level**: dispersion of the
  per-step number of unacceptable relay decisions 1.40 at K = 1 vs 1.39 for Z on the same states (iid 1.24 vs 1.47).
- **Prior art for the Outcome-C framing**: "When Upstream Messages Override Correct Answers" (Gong et al., arXiv 2609.36855,
  29 Sep 2026: LLM receivers change correct answers after wrong upstream messages up to 32 %, mostly by answer substitution;
  removing unreliable messages recovers part).  The "receiver fails to ignore a message it could ignore" question is
  therefore not new; the specific part is a structural channel trigger with a dose variable and two repairs.
- **TM4 (development, pre-registered) for the two finished K = 1-trained students**: net_Z at K = 1 +0.029 / +0.057 (acc_S
  0.935 / 0.927) vs the iid-trained −0.038 / −0.012.  Target (TM1–TM2) not yet read.
- **4×4 threshold**: G5 added before any 4×4 const-K run (`PROTOCOL_E3_G4_CONSTK_ADDENDUM1_20261001.md`, sha256 aea98d96…):
  b* = 3.7; viewstats v2 (per-step b2, b3; v1 fields byte-identical) replaces v1 in the 4×4 launcher.

## K. Exposure–response on 3×3 (`e3_exposure_response_report_20261001.txt`, viewstats v2, 40 cells, EXPLORATORY)
P(flip_Z | b3 = Σ_j (a_j − 3)+): 0 → 0.030 (iid 0.025, K = 1 0.046, K = 2 0.021, K = 3 0.033); 1–2 → K = 1 0.050, K = 2 0.046;
3–5 → K = 1 0.078, K = 2 0.060; 6–9 → 0.090; 10–14 → 0.097 (13 200 of K = 1's 18 720 steps).  Monotone, and K = 1 and K = 2
roughly agree at equal burden.
Time confound and a second component: burden grows with the step index and decisions get harder as traffic builds (iid flip
0.011 at t = 1–2, 0.029 at t ≥ 6).  At matched late steps (t ≥ 6) flips order by burden: iid (b3 0) 0.029, K = 2 (b3 2.0) 0.051,
K = 1 (b3 10.8) 0.096.  At early steps (t = 1–2, b3 = 0 in every regime) K = 1 still flips 0.062 vs K = 2 0.019 and iid
0.011, with 5.5 / 3.0 / 0.37 never-heard senders: a SPARSE-COVERAGE component at the start of the episode that the age clip
cannot touch (no stale copies yet).  Decision-level picture at K = 1: early missingness, then the stale tail (most steps).

## L. Corrections from the artifact subagent (18:3x–19:1x), verified
- §K overstated the dose-response: at constant K the per-step burden is a deterministic function of (K, t) (identical across
  seeds and episodes, L-218), so "flips rise with per-step burden; K = 1 ≈ K = 2 at equal burden" is a between-regime contrast
  plus the early K = 1 ramp; within K = 1 late steps the slope of flips on b3 is flat.  The clip-threshold dose
  (`PROTOCOL_E3_CLIP_THRESHOLD_DOSE_20261001.md`, written 19:00:15 before the runs) is graded: +0.030 / +0.017 / +0.006 /
  +0.001 at A = 2 / 3 / 5 / 7 — predicted "A = 3 ≈ A = 2" FAILED (age 3 is in the thin tail of training: 57 of 14 643 iid
  entries), A = 5 and A = 7 as predicted.  Reading: sensitivity follows the training DENSITY of the age feature, not a hard
  support boundary.
- The prospective gate cells (const 1 / 2 / 3, iid) cannot distinguish a view-keyed gate from the schedule "K = 1 and t ≥ 8";
  GT2 at iid is trivially true.  Any gate claim needs random-capacity cells.
- Verified: ρ(mean K = 1 gain over three panels, reserved congestion-order penalty at cap4 / low) = −0.818 (one-sided
  permutation p 0.003), N_s unrelated (0.24 / 0.04); ρ(dev net_Z at K = 1, congestion cap4 / low gain) = +0.721.

## M. Prospective gate result (L-221)
GT1 NOT SUPPORTED (K = 1 gate vs Z −0.59 % [−1.17, +0.02]); GT2 trivially SUPPORTED; GT3 SUPPORTED (+0.78 % [+0.12, +1.53]).
Two independent deployment-side repairs (clip, gate) each recover ≈ 0.8 % of the ≈ 1.4–1.7 % K = 1 loss.  The claim "never
worse than silence" is not established; the gate is a K = 1 schedule (Z for t ≥ 8) at constant K, as the artifact agent noted.

## N. "Is it just the architecture?" (user 20:0x) — verified points and the control launched
- Architecture (models/marl_comm_actor_set.py): φ per sender block (shared), masked by `heard`, pooled = Σ φ·heard / (Σ heard + 1)
  (not exactly a mean), concatenated with the own block and agent one-hot, then an MLP.  No explicit reliability gate.
- Already shown: the architecture CAN represent silence (relay net with Z's weights and φ ≡ 0 reproduces Z 8/8 at K = 1 and
  iid) — the failure is not "cannot represent Z"; the same architecture trained at K = 1 has positive development net_Z (TM4).
- Against a pure DILUTION reading: re-labelling the ages of the stale copies (content unchanged, still pooled) recovers
  0.848 → 0.878, almost as much as dropping them (0.883); dilution by stale CONTENT would not be repaired by a label change.
  The failure is the age feature's representation outside the training range (architecture × training regime).
- Not yet excluded: that a different aggregator would not fail.  Pre-registered control `PROTOCOL_E3_ARCH_CONTROL_20261001.md`
  (sha256 c4f8bbaf…): relay students with attention pooling (learned reliability weighting) and with per-slot concatenation
  (no pooling), seeds 0–2, same DAgger recipe (scripts/MARL_e3_actor_distill_v8.py; smoke: trains, the relay v6 evaluator
  builds AttnActorNet from the config), panel 3601–3664; AC1 generic / AC2 architecture-specific.
- Wording until then: "under this receiver architecture and training regime, channel-forced view shift can make
  communication worse than silence"; never "communication is fundamentally harmful".  The channel theorem is
  architecture-independent (it bounds every receiver's freshness); only the CONSEQUENCE for a learned receiver depends on
  architecture and training.
