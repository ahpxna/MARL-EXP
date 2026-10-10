<!-- Draft by subagent B (03/10/2026 13:0x EDT), copied unedited; every number carries its ledger / note source; items marked [VERIFY] or [no ledger row] are not yet verified. Not a manuscript. -->

# Paper 1 — draft: Related Work and Results

Draft by subagent B, 03/10/2026 12:5x EDT (read-only on the repo).  Sources: research/papers/audits/PAPER1_OUTLINE_20261003.md,
NOVELTY_POSITION_20261003.md (Addenda 1–3), LITERATURE_DEEP_READ_20261003.md, G7_FLOORS_SCOPE_20261003.md,
research/papers/_figures/paper1_draft_20261003/README.md, MARL_SELF_AUDIT_LEDGER_20260928.md (L-249 … L-296; L-201 for the
reserved panel), research/city_sim/CITY_LEDGER_20261002.md (C-8 … C-10).  Conventions: every number is copied from the cited
ledger row / note; "gain vs Z" = −(Σ waiting / Σ waiting of Z − 1) · 100 per seed, positive = better than the same-seed
compiled-silent student Z; brackets are the 95 % intervals recorded in the source; "(a/b)" counts seeds.  Items marked
**[VERIFY]** rest on paper summaries that LITERATURE_DEEP_READ says must be re-checked against the PDF.

---

## 2 Related work

**Delay- and channel-robust communication in MARL.**  The degradation we study in the upgrade direction has been observed
before: Rainbow Delay Compensation (RDC; arXiv 2505.03586v4, NeurIPS 2025) tests policies at fixed observation delays 0–12
(Figs 8–9) and reports that the policy trained under delay (Base) and the one trained with delay randomisation (Base+DR)
drop at delays 0–2, which the authors attribute to an "inability to generalize to unseen delay conditions" (verified sentence;
NOVELTY_POSITION Addendum 3).  We therefore do not claim to have discovered the phenomenon.  RDC reads it as a generalisation
failure and remedies it with compensators; our contribution is to measure it against a same-teacher compiled-silent student,
to split it into an information and an excess term, to explain it by the receiver's (joint) training support — Base+DR's
randomisation range excludes delays 0–2, i.e. it is an out-of-support case in our sense — to predict it channel-side, to show
it at the decision level on identical states, and to map which repairs work (Addendum 3).  The plot values in RDC (e.g. on
TAG) were not verified and are not used.  CGDC (arXiv 2604.03785) models a delayed-communication POMG and bounds the
delay-induced return loss by an information gap Δ_info, the KL divergence between action distributions under a timely and a
delayed message; its "no message" reference is the same policy with masked messages, whereas our reference is a separately
distilled silent student — a difference that matters (R5).  CoDe (arXiv 2501.05207, AAAI 2025) handles asynchronous messages
with age-decayed attention (MARL_NOVELTY_CHECK_DIRECTIONS_20261001); DACOM (2022) is a delay-aware communication method
**[VERIFY: no details in our notes]**.  CALF (arXiv 2603.12543) trains a single-agent controller under network middleware
(zero latency, a fixed 50 ms delay, or a full network model) and deploys it on hardware; every CALF policy does better as its
channel improves — including the fixed-delay policy, whose zero-delay condition is outside its training (CartPole return
218 → 482 from the worst to the clean condition, Tables 4–5, checked in LITERATURE_DEEP_READ) — so CALF shows no upgrade
hazard and serves as a contrast case; our mixture receiver is the CALF-style randomised-channel baseline.  Decoupled Delay
Compensation (arXiv 2605.26286) repairs the downgrade direction for synchronously trained policies with an execution-time
belief estimator (residual GRU + Kalman layer) that moves inputs back toward the training distribution; for a stale-trained
receiver the analogous edit is to garble the upgraded channel back into the trained range, which we test (R4).  A
communication-constrained-priors study (arXiv 2512.03528) evaluates only equal-or-harsher test channels (L-259); mixture
training is domain randomisation, whose theory is given by Chen et al. (ICLR 2022, arXiv 2110.03239; L-259).

**Freshness theory.**  Shisher and Sun (MobiHoc 2022, arXiv 2208.06948; follow-up arXiv 2404.16281) show that the inference
error of a learned predictor can be non-monotone in the age of information, and their Lemma 3 (§III-B) bounds the deviation of
the inference error by a χ² divergence β between training and inference conditional laws, assumed for all inputs (Addendum 1).
Their per-AoI curves are matched-training curves — our information term — and the bound presumes full covariate support, which
is where our receivers fail (LITERATURE_DEEP_READ).  2404.16281 assumes identical training and deployment AoI distributions
(L-260).  Neither reports a stale-trained predictor deployed on a fresher channel (Addendum 1, from summaries of the HTML).  The
relay channel itself (piggybacked status tables in round-robin broadcast, relay age) is Kaul–Yates–Gruteser (GLOBECOM 2011),
with all-to-all multi-hop AoI bounds by Farazi–Klein–Brown (JCN 2019) (MARL_NOVELTY_CHECK_DIRECTIONS_20261001).

**Backward compatibility of updated models.**  That an updated component can break a frozen consumer is established.  Bansal
et al. (arXiv 1906.01148) define the compatibility of an update with a user's mental model of the old system and report that a
more accurate but incompatible update lowers team performance (summary).  BCT (Shen et al. 2020, arXiv 2003.11942) shows an
independently trained better embedding scoring 0.0 % against a frozen old gallery and restores compatibility with an influence
loss; its normalised update gain is the precedent of our information / excess split (LITERATURE_DEEP_READ, PDF read).
Positive-congruent training (Yan et al. 2021, arXiv 2011.09161) introduces the negative flip rate (NFR) and reduces it from
6.44 to 2.35 at roughly equal error; Srivastava et al. (2020, arXiv 2008.04572) define backward trust / error compatibility
(BTC / BEC) and report a downstream error rising from 55 to 86.4 % after a 14 % more accurate upstream model (PDF read).
SIL-C (arXiv 2509.20612) gives frozen high-level policies a support-validated skill interface with fallback **[VERIFY: reported
backward transfer −14 … −37 % without, +18.6 … +42.5 % with — summary only]** — the closest precedent of our support fallback.
Support-based explanations of transfer failure are standard in domain adaptation (Johansson, Sontag and Ranganath, AISTATS 2019;
Zhao et al., ICML 2019; clipping only extreme activations, ReAct, NeurIPS 2021; L-276).  Our setting differs in four ways
(LITERATURE_DEEP_READ, novelty consequence): the update is a channel refinement with unchanged message semantics, so the
Bayes-optimal value cannot fall (Lean `upgrade_emulation`, knowledge level); the frozen consumer is a closed-loop multi-agent
decision receiver measured against a compiled-silent bar; the harm is split exactly where an exact floor exists; and it is
predicted channel-side.

**Distillation to silent students.**  Distilling a communicating or centralised teacher into communication-free students is an
established method family (CTDS 2022, PTDE 2022, CTEDD 2019, DDCA, CoDiMAD, KD-MARL 2026, MAGPO 2025), and Communication-
Enhanced Tutoring (2025) compares distillation against communication (NOVELTY_POSITION).  We use the same-teacher distilled
silent student not as a method but as the mandatory bar any runtime communication must clear.

**Language drift and frozen listeners.**  Under joint fine-tuning, emergent or natural-language protocols drift (Lee et al.
2019, arXiv 1909.04499); in SIL (Lu et al. 2020, arXiv 2003.12694) a frozen pretrained ranker's R1 falls from about 0.22 to
0.09 as the speaker improves **[VERIFY: read from a plot]**, and a speaker optimised against one listener succeeds 98 % with it
and 37 % with a held-out listener, recovering to about 80 % with a listener population (Wang et al. 2021, arXiv 2110.05422)
**[VERIFY: summary only]**.  There, frozen learned listeners are evaluation instruments or co-trained partners; here the frozen
learned receiver is the deployed controller and the producer-side change is a channel improvement.  We found no work on
communication-protocol versioning between learned agents (three searches, not exhaustive; LITERATURE_DEEP_READ).

---

## 4 Results

**Scope.**  All results are from simulation with components we trained ourselves (CityFlow 3×3 and 4×4 grids; a linear-Gaussian
and a pendulum remote-inference testbed; a stylised car–light model C0; SUMO grid4): there are no real controller logs, no J2735
traces, no independently developed vehicle stack and no real cross-version data (L-292, C-8).  Each closed-loop number is a gain
vs the same-seed compiled-silent student Z on a 64-traffic-seed × 2-headway panel used once, unless marked as development.  Lean
results are cited as "compiled, smoke-gated": the full gate was stopped after 33 of 315 modules (L-280), and they bound
fresh-view **knowledge** (knowledge floors), not decisions, value or return (G7_FLOORS_SCOPE).

### R1 The training-channel hazard runs in both directions

*Downgrade: an iid-trained receiver on K = 1.*  The relay receiver trained on iid capacities falls below Z at constant K = 1 on
every panel: 3×3 −2.35 % [−3.71, −1.15] (L-249), −1.90 % [−3.67, −0.21] (L-250), −1.44 % [−2.67, −0.31] (L-256), −2.23 %
(L-282), −1.50 % (L-266), −1.76 % (L-287); 4×4 −2.41 % [−4.15, −1.01] (L-270, G1), −2.58 % [−3.97, −1.32] (L-286), −2.47 %
(L-279), −2.51 % (L-294).  The reversal is architecture-general: attention −1.48 %, per-slot concatenation −11.53 % and mean
pooling −2.87 % at K = 1, while all three gain at iid (+2.83, +2.57, +3.43; L-252; AC1 SUPPORTED for both alternatives, AC2 NOT
SUPPORTED).

*Upgrade: a K = 1-trained receiver on fresher channels.*  On 4×4 the K = 1-trained receiver gains +5.80 % [4.38, 7.15] on its own
channel and loses −3.55 % [−6.22, −0.94] at iid (GTM3 SUPPORTED; L-286); the loss replicates on three further 4×4 panels
(−3.22, L-294; −3.78 [−6.56, −0.94], L-293; −3.60, L-295; −3.37, L-296).  On 3×3 the same receiver gains +2.40 % [1.36, 3.42]
at K = 1 (5/5) and +0.29 % [−1.62, 2.07] at iid (P-UP2 SUPPORTED 5/5; L-250), with the fall from K = 1 to iid replicating on
five further panels (+2.38 → +0.42 [−2.07, 2.39], L-249; +2.57 → +0.25, L-266; +2.33 → +0.20, L-274; +2.05 → −0.08, L-282;
+2.38 → +0.11, L-287).  On 3×3 the upgraded receiver therefore ends near Z (−0.26 [−2.48, 2.02] on the fallback panel; L-293)
rather than clearly below it.  A receiver trained at K = 2 is peaked at its own channel and loses in both directions: −2.66 %
[−4.33, −0.95] at K = 1, +2.86 % at K = 2, +2.50 % at K = 3, +0.61 % at iid (W1d; L-282).

*The matched receiver wins at every channel tested.*  At K = 1 the K = 1-trained receiver beats the iid-trained one by +8.11 %
[6.04, 9.97] (10/10; L-286) on 4×4 and +4.18 % [2.04, 6.15] (5/5; L-250) on 3×3; at iid the order reverses (3×3 −3.03 %
[−4.27, −1.91], 5/5 < 0; L-250).  Pooled over 17 finished panels, the deployment channel equal to the training channel is the
best cell in 30 of 30 receiver × panel rows (train × deploy matrix, research/marl_budget/e3_train_deploy_matrix_20261003/
README.md; Fig. F1, F4) **[no ledger row]**.

*Decision-level flips on identical states.*  With the zero-byte student driving, so that every channel sees the same world states,
and teacher-acceptable sets as labels, the K = 1-trained receiver's net flip (positive minus negative flips) from K = 1 to iid is
−0.067 on 3×3 (5/5 < 0; backward trust compatibility BTC 0.867, agreement 0.776) and −0.084 on 4×4 (10/10; BTC 0.863); the
iid-trained receiver's net flip from iid to K = 1 is −0.089 (3×3 5/5, 4×4 10/10); the four-regime mixture's net flip from K = 1
to iid is +0.031 (0/5 < 0; BTC 0.953); the K = 2-trained receiver loses both ways (−0.073 to iid, −0.065 to K = 1; 5/5 each).
FL1–FL4 are all SUPPORTED: about 12 % of the receiver's acceptable decisions become unacceptable and about 4–5 % the other way
(L-292; Fig. F3).  These are Z's closed-loop states, not the receiver's own, and the negative flip rate from A to B equals the
positive flip rate from B to A by construction (figure README), so only one direction per pair carries information.

*Other domains.*  In the pendulum remote-inference testbed a predictor trained on ages 4–7 scores 0.900 at deployment ages 0–3
against 0.952 at ages 2–5 (UR1 SUPPORTED, 5/5), while moderate upgrades help — the curve is non-monotone (L-261).  In the
linear-Gaussian age-role testbed the upgrade regression is −0.268 / −0.241 / −0.017 / +1.689 (gain units) at drift
λ = 0 / 0.1 / 0.2 / 0.4: without drift a fresher deployment helps, with strong drift it falls below silence (−1.144; L-263).  In
SUMO, a learned light that beats the actuated light by +2.63 / +2.57 / +2.48 / +2.75 s/veh over four training seeds raises the
old learned fleet's approach cost by +30.17 [22.35, 38.53], +7.00 [6.12, 7.71], +6.81 [6.27, 7.35] and −0.43 [−0.76, −0.11]:
the hazard appears in 3 of 4 training pairs and B1 is NOT SUPPORTED (C-8).

### R2 The loss is excess risk, not lost information

We split a frozen receiver's change into the change of an information floor and the change of its excess over that floor
(the normalised form is BCT's update gain; LITERATURE_DEEP_READ).

*Exact floor (RI).*  In the linear-Gaussian testbed the Bayes MSE falls from 0.619 (training ages 4–7) to 0.223 (ages 0–3) at
every drift, while the frozen receiver's MSE goes 0.622 → 0.249 (λ = 0), 0.623 → 0.287 (0.1), 0.625 → 0.601 (0.2) and
0.634 → 2.982 (0.4); its excess-risk change is +0.023 / +0.060 / +0.372 / +2.744 (NOVELTY_POSITION Addendum 1; reproduced,
Schur check 2.7e-15; expected Bayes risk, not sample-matched).  An upgrade that strictly improves the information floor can
therefore make the deployed receiver worse through excess alone (Fig. F2a).

*Exact floor (C0).*  For the car trained on the actuated light ACT, the change of regret when the light is replaced splits into
floor + excess as FT −3.27 + 2.45 (excess up on 5/5 seeds), EXT +1.21 + 20.93, CUT +0.86 + 0.70, A5 +0.81 + 8.75 (regret units);
in exact cost units FT −3.62 + 2.41, the excess eating 67 % of the information gain, and EXT +5.71 + 21.78 (Addendum 2).  Excess
rises on every light except A2 (C-9).  C0's producing code version is not verifiable from the record (C-9), so these numbers
carry a provenance caveat.

*Matched-receiver proxy (E3).*  Using the receiver trained on the new channel as the information reference, the 4×4 upgrade
K = 1 → iid splits into information +0.22 [−0.25, +0.78] and excess −9.57 [−12.09, −7.16]; on 3×3 into +0.83 [+0.25, +1.48]
(5/5 > 0) and −2.94 [−4.10, −1.90] (train-match panel) or +0.72 and −2.78 (mixed-channel panel).  In the downgrade direction the
excess is −8.37 (4×4) and −4.30 / −4.09 (3×3).  The excess is negative in 20 of 20 seed pairs in both directions and carries
102 % (4×4) and 135–139 % (3×3) of the upgrade loss (Addendum 2; Fig. F2c–d).  The proxy is not the information floor: against
C0's exact floor it ranks lights with Spearman 0.33, a bias of +1.09 and the wrong sign on two of nine lights (FT, A4; Addendum 2).

*Formal counterpart.*  At the level of fresh-view knowledge, an upgraded prefix channel can emulate the old one while a downgrade
below the floor cannot be emulated (LeanMarlEmulationV1: `upgrade_emulation`, `downgrade_strict`; compiled, smoke-gated, L-262),
so the Bayes optimum cannot lose from an upgrade; and in an explicit instance a training-optimal frozen rule falls below silence
after an information-preserving upgrade (LeanMarlSupportV1 `upgrade_hazard`; smoke gate PASS, L-264).  These are knowledge
floors and instances; they do not bound decisions or return (G7_FLOORS_SCOPE).

### R3 The excess is organised by joint training support

*Distance ranks, but does not quantify.*  Across deployment channels the gain difference between the K = 1- and iid-trained
receivers is linear in a channel-only W1 mismatch difference (slope −1.25 % per W1 unit, R² 0.99 on 4 points, post hoc; ML1,
ML2, ML4 SUPPORTED, ML3 NOT SUPPORTED; L-249) and predicts a new panel with |error| ≤ 0.35 points (L-258); the 4×4 slope is
2.21 % per W1 unit (GTM4 SUPPORTED, Pearson +0.970; L-286).  Prospectively, on a new training channel (K = 2), the zero-free-
parameter W1 law fails (W1b NOT SUPPORTED, Pearson 0.764 with errors up to 1.36; W1c NOT SUPPORTED: the K = 2-trained receiver
is not rescued at K = 1, −2.66 vs −2.23, although its W1 to K = 1 is smaller, 1.73 vs 2.84; L-282).  Post hoc on these 12 cells
the out-of-support count of entries older than two steps ranks gains slightly better than W1 (Spearman −0.853 vs −0.825; L-282).

*Equal distance, different support.*  In the remote-inference testbed, receivers at equal W1 = 4.0 from the deployment ages
differ by support: disjoint support 0.899 (0.885 … 0.911), covering supports 0.978 and 0.979, matched 0.985; covering recovers
92 % of the gap (SD1, SD2 SUPPORTED, 5/5; L-277).

*Which statistic leaves the support.*  On 3×3, upgrades of the K = 1-trained receiver put only the fresh count out of support
(K2 100 %, K3 100 %, iid 87.6 % of receiver-steps), while downgrades of the iid-trained receiver put the maximum age out of
support (K1 84.6 %, K2 83.3 %) and iid → K3, where it wins (+2.64 %), puts nothing out of support (L-268).  On 4×4 no marginal
statistic leaves the iid support at K = 1 (L-271), but the joint feature coverage × late episode does (50.0 % at K1, 0 % at K2,
0.7 % at K3, matching the signs −2.41 / +2.49 / +5.18 %) — a double dissociation: the age clip repairs on 3×3 (+0.79 %
prospective, +0.69 % on panel 4001) but not on 4×4 (+0.18 %; L-272, L-270 G4).  On 4×4 the K = 2 cell discriminates support
from "fewer stale copies is better": the K = 1-trained receiver gains +2.15 at K = 2 against +5.80 at K = 1 although K = 2
delivers fewer stale copies (SV1–SV3 SUPPORTED; L-286).  The mixture receiver's age response is regime-conditional, like the
K = 1 specialist on K = 1 views and like the iid specialist on iid views (RID1, RID2 SUPPORTED, n = 4; L-278).

*A channel-side prospective rule.*  Rule A with the training-relative staleness threshold (K_min 1.25: K = 1 forced negative,
K ≥ 2 allowed) classified 3 of 3 4×4 constant-K cells correctly, the absolute version 1 of 3 (K_min 3.45 fails at K2 and K3),
predicted before the 4×4 target was run (Addendum 4; L-270).  Lean gives rule A's channel cap as a corollary of the net floor
(LeanMarlProvisioningV1; smoke gate PASS, L-264) — the cap only, not the sign of the gain (G7_FLOORS_SCOPE).

*A support monitor sees the upgrade hazard; a freshness monitor does not.*  At the 4×4 upgrade hazard (K = 1-trained receiver at
iid, plain −3.78 [−6.56, −0.94]) a monitor of the receiver's joint support falls back to Z on 99 % of decisions and recovers
100 % of the deficit (−0.01), while a mean-age monitor falls back 0 % (FB3 SUPPORTED); its fallback rate ranks the relay's loss
over 8 cells (FB6 SUPPORTED, Spearman +0.83; L-293).  On 3×3, FB3 could not be tested (no upgrade-hazard cell on that panel)
and FB6 is NOT SUPPORTED (Spearman +0.46 over 16 cells; L-293).

*Support contracts are not sufficient.*  In SUMO, a receiver contract (accepted time-in-phase region + exposure) computed from
the new light's human-traffic logs does not rank the fleet's regression (Spearman 0.36 vs 0.40 for the receiver-free share over
36 lights × seeds; B3 NOT SUPPORTED); a light inside the fleet's support still regresses it (under FT: in support, r 29.6, and
13.1 worse than an FT-trained fleet, n 20; B4, B4′ SUPPORTED); and the cap frontier has no knee at the fleet's 50 s support
(p(50) 0.11, p(60) 0.08, p(30) 0.45, but r(30) 1.61 < ½ r(50) 2.03; B5 NOT SUPPORTED; C-8).  In-support (semantic) harm
therefore exists beside the support hazard.

### R4 Repairs that act on the joint system work; input edits do not

*Matched training.*  Training at the deployment channel rescues the K = 1 loss: +2.40 % [1.36, 3.42] vs Z (TM1, TM2 SUPPORTED;
L-250) and +5.80 % on 4×4 (GTM1, GTM2 SUPPORTED; L-286).

*Mixture training (minimax receiver).*  A receiver trained on the four channels gains at K = 1 (+0.97 % [0.34, 1.64], 9/10; MX1
SUPPORTED) at no cost at iid (+0.05 % vs the iid specialist, 6/10; MX2 SUPPORTED), but trails the K = 1 specialist by −1.05 % at
K = 1 (0/5; MX3 NOT SUPPORTED; L-256).  On 4×4 it gains +5.27 % [3.91, 6.59] at K = 1, +5.78 % at K = 2, +5.98 % at K = 3 and
+5.83 % at iid; its worst cell (+5.27) beats the iid-trained (−2.51) and K = 1-trained (−3.22) receivers' worst cells (D1, D3
SUPPORTED), but it costs −0.52 % at iid, just past the bound (D2 NOT SUPPORTED; L-294).  A mixture of only the two extreme
channels is positive everywhere (+1.99 % [0.44, 3.51] at K = 1 … +2.73 % at iid) but falls 0.52 / 0.57 below the four-regime
mixture at K = 2 / 3 (C1 NOT SUPPORTED) and below the iid specialist at iid (2.73 vs 3.28; C2 NOT SUPPORTED on its iid half;
L-287).  The mixture receiver also tracks a channel that switches within the episode (+2.19 / +2.09 / +2.44 % on three
schedules vs +1.75 / +0.41 / +0.46 for the K = 1 specialist; SW1, SW2 SUPPORTED; L-285).

*Support fallback to the silent student.*  On 4×4 all six fallback predictions are SUPPORTED (FB1–FB6; L-293), but the generic
support monitor is conservative between channels: for the K = 1-trained receiver it falls back on about 96–100 % of decisions at
K2 / K3, forfeiting gains of +2.04 / +2.02 % (4×4) and +1.45 / +0.94 % (3×3) (L-293).

*Producer-side compatible mode.*  Capping the learned light's green at 50 s keeps +2.32 of its +2.61 s/veh gain (89 %) while
cutting the fleet's regression from +10.89 to +4.05 (37 %); caps 50 and 60 qualify (B2 SUPPORTED; C-8).

*Input relabelling fails.*  Transporting the age marginal to the training histogram makes every receiver worse than plain
(K = 1-trained at K2 −6.16 % [−8.81, −3.41], K3 −6.34 %, iid −5.21 % [−7.85, −2.15]; iid-trained at K1 −3.92 %, K2 −7.13 %, K3
−5.67 %), below Z by −2.6 … −5.4 % (RM1, RM2, RM3, RM5 NOT SUPPORTED; L-266).  Showing direct entries one step old to put the
fresh count inside the K = 1 support costs −2.88 % [−4.73, −1.15] at K2, −7.39 % [−11.51, −3.41] at K3 and −11.39 %
[−18.10, −4.72] at iid (SP1–SP3 NOT SUPPORTED; L-274), and −17.8 % at iid on 4×4 (GTM5 NOT SUPPORTED; L-286).  Moving the
decision-step feature to repair a joint coverage statistic costs −2.21 % [−2.78, −1.62] at K1 (10/10 negative; TP1 NOT SUPPORTED,
TP2 SUPPORTED; L-279).  The only interface edit that helped is the 3×3 clip of out-of-range ages on the downgrade (+0.69 % vs plain
on panel 4001, RM4; L-266); it does not transfer to 4×4 (+0.18 % [−0.10, +0.49], G4 NOT SUPPORTED; L-270) or to the pendulum
testbed, where clipping is below plain at every drift (CL1 NOT SUPPORTED; L-285).

*Per-entry garbling helps against relabelling but is not a repair.*  Re-aging each fresher entry to a value from the trained range
together with its payload (emulation) beats relabelling the age alone at iid on 4×4 (+4.63 % [2.83, 6.32], 9/10; EM2 SUPPORTED)
but not plain (+0.75 % [−1.01, 2.32], 6/10; EM1 NOT SUPPORTED), recovers 0.75 of a 9.42-point hazard (EM3 NOT SUPPORTED), is
inert in support (EM4 SUPPORTED), shows no effect on 3×3 (EM5 NOT SUPPORTED), and hurts at K2 / K3 on 4×4 (−11.08 / −4.27 % vs
plain; L-295).

*Receiver-side throttling fails.*  Dropping deliveries so that the K = 1-trained receiver sees only a K = 1 schedule at iid costs
−11.15 % [−14.13, −7.84] vs plain on 4×4 (1/10; JT1 NOT SUPPORTED), equals its age-relabelled variant (−0.42 %, 5/10; JT2 NOT
SUPPORTED), is also far below plain at K2 (−7.69 %) and K3 (−9.81 %), and has the wrong sign on 3×3 (−0.77 %, 1/5; JT4 NOT
SUPPORTED), where it still beats its relabelled variant by +4.77 % [3.24, 6.05] (5/5; L-296).

*Reading: the receiver's support is co-produced.*  Deliveries are scheduled by the protocol's sender-side age mirror, which
assumes every delivered packet was accepted, so a receiver that drops packets meets staleness patterns K = 1 never produces
(L-296).  The same holds in SUMO: with human drivers only, every max-green setting yields identical greens of at most 19 s
(median 5 s), and the learned fleet's 50 s support appears only when the fleet itself drives (time in phase reaching exactly the
max green M on every net; p99 11 / 17 / 31 / 45 s for M = 40 / 50 / 60 / 80; C-10).  Repairs that act on the joint system —
matched or mixture training, a switching actor, or keeping the producer in its old mode — work; edits of the receiver's inputs
or reception alone do not (L-296).

### R5 The silence bar

A compiled-silent student distilled from the same teacher is a strict bar.  Where its training channel is in support, relay
communication clears it: on the reserved 3×3 ten-seed panel the age-first relay changes waiting time by −2.29 % [−3.25, −1.39]
at iid, −2.04 % [−3.03, −1.10] at cap4 and −1.26 % [−2.08, −0.50] at low capacity relative to Z (negative = better; L-201), and
on 4×4 it gains +6.26 % [5.32, 7.25] at iid, 5.78 % at cap4 and 2.93 % at low (10/10; R1 SUPPORTED; L-270).  The same-receiver
masked-message reference used in CGDC-style analyses is far weaker: with messages masked, the 4×4 K = 1-trained receiver scores
−14.87 % [−26.83, −7.02] vs Z and the iid-trained one −15.30 %; on 3×3 −4.07 % and −4.55 % (JT3 SUPPORTED; L-296).  Measured
against a masked reference, every hazard of R1 would look like a gain; measured against Z, the upgraded and downgraded receivers
fall below silence.  A teacher-side predictor of the relay's value over Z did not replicate on the second network (Spearman
0.236 < 0.5; R2 NOT SUPPORTED; L-270).

---
## Corrections to the [VERIFY] items (03/10/2026 14:0x EDT; subagent A read the PDFs; RDC re-checked by me on pp. 8, 17, 18)
Replace in §2 (each sentence verified; quotes ≤ 15 words):
1. RDC: "Rainbow Delay Compensation (RDC; arXiv 2505.03586v4, NeurIPS 2025) trains FT-QMIX under random observation delays (Base; Base+DR
   adds a delay-reconciled critic that sees the delay-free state) and tests at fixed delays (MPE 0–12, SMAC 0–9; Figs 8–9, Tables 4 and 6);
   on MPE, where training delays span 3–9 (App. C, Table 2, as we read it), both drop at delays 0–2 — TAG 110.2 at delay 0 vs 135.2 at
   delay 3 for Base, 135.1 vs 156.9 for Base+DR — which the authors attribute to an 'inability to generalize to unseen delay conditions'
   (§5.2); on SMAC, whose training range includes 0–2, no comparable drop appears."  (Remove "trained with delay randomisation".)
2. SIL-C: backward transfer of the initially trained policy on Franka Kitchen +2.6 → +18.6 (Emergent) and 0.0 → +42.5 (Explicit) over its
   own base PTGM + adapter-append; fine-tuning baselines lose 13.6–36.9 points (Table 1, 4 seeds); gate = Mahalanobis distance to Gaussian
   prototypes at the square root of the 99 % χ² quantile, fallback to the original subtask.
3. Calibrate your listeners: 98 % with the training listener, 37 % with a held-out listener (chance 33 %), 10 seeds (Table 1); ensemble of
   30 listeners ≈ 75 % (read from Fig. 3a — NOT 80 %); over-confidence quote verified.
4. SIL: frozen image-ranker R1 21.9 % → 9.7 ± 1.2 % under Gumbel fine-tuning, 21.7 % with SIL (App. C, Table 2, 5 seeds) — a table, not a plot.
5. Bansal 2019: sentence verified (§5.1): "a more accurate but incompatible classifier results in lower team performance".
6. DACOM (AAAI 2023): TimeNet learns how long to wait for delayed messages; SINR-dependent delay, mean delay 10–90 % of a step; modified MPE,
   highway-env intersection, SMAC 3m / 8m / 2s3z / 3s5z; no train-at-one-delay / test-at-another experiment seen.

**Correction (17:4x, external review, verified on Table 4):** Base at delay 6 is 125.4; 142.3 is Base+DR at delay 6. Drop the words 'minimax', 'iff', 'exact E3 decomposition', 'receiver-only repair impossible', 'FB_S beats the standard gate' (ledger L-302); describe L-292 flips as disagreement with the teacher's A_0.25 set on Z-driven states; describe L-296 as an input intervention, not an emulation of the training protocol.
