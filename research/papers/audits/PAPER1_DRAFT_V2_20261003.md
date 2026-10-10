<!-- Draft v2, 03/10/2026 18:2x EDT. Coordinator rewrite of PAPER1_DRAFT_RELATED_RESULTS_20261003.md (v1 is kept unchanged as
history), aligned with PAPER1_CLAIM_MAP_20261003.md. Every number is the claim map's. Items that wait for the paired repair
panel (P1, 5301) or for P2 are marked [P1] or [P2]. Not a manuscript. -->

# Paper 1 — draft v2: abstract, contributions, related work, results

## Abstract (draft; numbers fixed by the claim map)

**Setting.** A learned receiver is trained to act on messages that arrive over one communication channel. It is then deployed
after the channel changes, and it is not retrained.

**What we measure.** We evaluate this deployment systematically in multi-agent traffic-signal control (CityFlow 3×3 and 4×4).
Every receiver is compared with a compiled-silent student distilled from the same teacher, so the bar is strict.

**Findings.**

* On its own channel the relay receiver clears that bar: +5.80 % at constant capacity 1 and +6.02 % at i.i.d. capacities on 4×4.
* Moved to the other channel it falls below it, in both directions: −3.55 % [−6.22, −0.94] after an upgrade and −2.58 % after a
  downgrade.
* A receiver trained on the deployment channel recovers +8.1 to +9.6 points.
* A masked-message reference of the kind used in earlier analyses would score every one of these losses as a gain.

**Information versus use.** We separate the information a channel carries from the receiver's ability to use it. In a
remote-inference testbed the split is exact: the Bayes risk falls with the upgrade while the frozen receiver's risk rises
through its excess alone. On traffic we report the corresponding matched-training contrast, not a Bayes decomposition.

**Repairs.** We compare runtime repairs (support and Gaussian-distance fallbacks, input adapters) with retraining (matched,
mixture) on one paired panel, reporting harm blocked, benefit kept and cost [P1]. [P2: one causal test of why input-only
adapters fail — included only if its gates pass.]

## 1. Contributions (scoped)

1. **A deployment evaluation against a strict silence bar.** It covers a train × deploy matrix, both channel directions, a
   same-teacher compiled-silent comparator, and primary panels with recorded provenance.
   * We do not claim the upgrade-direction drop as new: RDC reports one.
2. **Information versus use.**
   * In the RI testbed: an exact decomposition.
   * On traffic: a matched-training contrast, labelled as such.
   * A Lean counterexample: a training-optimal frozen receiver worse than silence after a Blackwell-dominating upgrade (one
     finite example, fixed laws).
3. **A paired comparison of repairs with costs** [P1]. It shows when to keep the receiver, when a fallback is enough, and when
   to retrain, including what each detector gives up.
4. [P2, conditional] One mechanism test of why a receiver-side input adapter fails, with the information and replay
   feasibility gates reported whether or not they pass.

## 2. Related work (corrected)

**Delay- and channel-robust communication in MARL.** Rainbow Delay Compensation (RDC; arXiv 2505.03586v4, NeurIPS 2025)
trains FT-QMIX under random observation delays (Base) and tests at fixed delays (MPE 0–12, SMAC 0–9). Base+DR adds a
delay-reconciled critic that sees the delay-free state.

* On MPE, training delays span 3–9 (App. C, Table 2, as we read it), and both variants drop at delays 0–2.
* On TAG, Base scores 110.2 / 135.2 / 125.4 at delays 0 / 3 / 6, and Base+DR scores 135.1 / 156.9 / 142.3.
* The authors attribute the drop to an "inability to generalize to unseen delay conditions" (§5.2).
* On SMAC, whose training range includes 0–2, no comparable drop appears.

We therefore do not claim to have found the phenomenon. Our contribution is the comparison against a same-teacher silent
student, the information-versus-use separation, and the paired map of repairs with costs.

Other work in this line:

* **CGDC** (arXiv 2604.03785) bounds the delay-induced loss by an information gap. Its "no message" reference is the same
  policy with masked messages; ours is a separately distilled silent student, a difference that changes signs (R5).
* **DACOM** (AAAI 2023) learns how long to wait for delayed messages. It does not train at one delay and test at another.
* **CALF** (arXiv 2603.12543) is a contrast case: each of its policies improves as its own channel improves. Our mixture
  receiver is the CALF-style randomised-channel baseline.
* **Decoupled Delay Compensation** (arXiv 2605.26286) repairs the downgrade direction with an execution-time belief estimator.

**Freshness theory.** Shisher and Sun (arXiv 2208.06948; 2404.16281) show that a learned predictor's error can be
non-monotone in the age of information. Their bound depends on a divergence between training and inference conditional laws.
The relay channel itself is that of Kaul–Yates–Gruteser (GLOBECOM 2011).

**Backward compatibility of updated models.** That an updated component can hurt a frozen consumer is established:

* Bansal et al. 2019: "a more accurate but incompatible classifier results in lower team performance" (§5.1).
* BCT (Shen et al. 2020): its normalised update gain has the same form as our information-versus-use split.
* Positive-congruent training (Yan et al. 2021).
* Srivastava et al. 2020.

**Support gates with fallback.** SIL-C (arXiv 2509.20612) gates frozen high-level policies with a Mahalanobis distance to
Gaussian prototypes at √χ²_0.99 and falls back to the original subtask. On Franka Kitchen it reports backward transfer
+2.6 → +18.6 and 0.0 → +42.5 over its own base (Table 1). Our parametric gate is SIL-C-style (one full-covariance prototype),
not SIL-C's diagonal gate. Monitors with fallback are standard (Simplex, runtime assurance); we claim no new monitor.

**Frozen listeners.**

* In SIL (Lu et al. 2020), a frozen ranker's R1 falls from 21.9 % to 9.7 ± 1.2 % (App. C, Table 2).
* A speaker trained against one listener succeeds 98 % with it and 37 % with a held-out listener (chance 33 %), and about 75 %
  with a 30-listener ensemble (Wang et al. 2021, Table 1 and Fig. 3a).

In both, the frozen learned listener is an evaluation instrument or a co-trained partner; here it is the deployed controller.
[Re-check against the PDFs before printing: the PCT NFR 6.44 → 2.35, BCT, Srivastava and Lee numbers, per handover A §2.]

## 4. Results

**Scope.**

* All results are from simulation with components we trained (CityFlow; RI testbeds; SUMO as a second domain).
* Each closed-loop number is a gain vs the same-seed compiled-silent student Z on a 64-traffic-seed × 2-headway panel used
  once, with a two-level bootstrap CI.
* Re-evaluations of the same checkpoints on new panels are replications over traffic, not over training randomness.
* Theorems hold under fixed input distributions, open loop.

### R1 The hazard runs in both directions (4×4 primary panel 4201)

**Upgrade.** The K1-trained receiver gains +5.80 % [4.38, 7.15] on its own channel and −3.55 % [−6.22, −0.94] at iid. The
paired drop is −9.35 [−12.15, −6.58], and it is negative on 10/10 seeds.

**Downgrade.** The iid-trained receiver gains +6.02 % [5.01, 7.21] at iid and −2.58 % [−3.97, −1.32] at K1. The paired drop
is −8.60 [−10.29, −6.77].

**3×3 (3201).**

* The upgrade lowers the K1-trained receiver from +2.40 % [1.36, 3.42] to +0.29 % [−1.62, 2.07]: close to Z, not below it.
* The downgrade takes the iid-trained receiver to −1.90 % [−3.67, −0.21].

**Matched receivers, at the two channels where one exists.** The matched receiver beats the mismatched one by +8.11
[6.04, 9.97] at K1 and +9.57 [7.06, 12.24] at iid (10/10 each). No 4×4 receiver was trained at K2 or K3.

**Matrix (descriptive).** Over 17 panels the diagonal is the best cell in 30/30 receiver × panel rows. These rows re-evaluate
the same checkpoints; the pooling rule is given in the F1 caption.

**Teacher-relative disagreement (diagnostic, dev episodes 901–904).** On states driven by Z, the K1-trained receiver's net
agreement with the teacher's A_0.25 acceptable set changes by −0.084 from K1 to iid (4×4, 10/10 < 0). This measures
disagreement with the teacher, not wrong actions.

### R2 Information versus use

**Exact (RI testbed).** The Bayes MSE falls from 0.619 to 0.223 with the upgrade at every drift. The frozen receiver's excess
changes by +0.023 / +0.060 / +0.372 / +2.744 at λ = 0 / 0.1 / 0.2 / 0.4. With strong drift the receiver gets worse although
the information improves. This is expected Bayes risk in a linear-Gaussian model, a computation, not a theorem.

**Traffic (matched-training contrast).** Take the receiver trained on the new channel as the reference. The 4×4 upgrade then
splits into a reference change of +0.22 [−0.25, 0.78] and a residual of −9.57 [−12.09, −7.16], with the residual negative in
20/20 seed pairs.

* This is a contrast between two trained receivers, not a decomposition into Bayes optima.
* Against C0's exact floor the same proxy ranks lights with Spearman 0.33. C0 is secondary because its producer is
  unverifiable.

**Formal counterpart (Lean).**

* `upgrade_emulation`: an upgraded prefix channel can emulate the old one at the knowledge level.
* `SupportV1.upgrade_hazard` and `FrozenFloorV1.frozen_floor_not_monotone`: a training-optimal frozen rule can fall below
  silence after an information-preserving upgrade (one finite example).

These are knowledge floors and instances; they bound neither decisions nor return.

### R3 Diagnostics of support (descriptive)

**What leaves the support.**

* On 3×3, upgrades put the fresh count out of support and downgrades put the maximum age out of support.
* On 4×4, no marginal statistic leaves the iid support at K1, but a joint feature does.

These diagnostics were found post hoc.

**Rule A.** It classified 3 of 3 4×4 constant-K cells before the run (n = 3: an anecdote). Its Lean counterpart is a cap
only, not a sign.

### R4 Repairs under the same conditions [P1, panel 5301]

**Table.** Per cell (K1, iid, K2, K3) and per arm, the table will give:

* the absolute gain vs Z with CI, and the paired difference vs PLAIN;
* the intervention rate;
* the harmful cells, the worst cell, and the costs.

Runtime arms on one receiver checkpoint: PLAIN, MASK, FB_S±, FB_M±, FB_Mq±, EMU, THR. Retraining arms are reported apart,
with their training cost: the matched receiver at K1 and at iid only, and MIX.

**Cell groups (fixed in advance from 4201 / 4601 / 4901).**

| Group | Cells |
|---|---|
| Own | CK1@K1, Cage@iid |
| Hazard | CK1@iid, Cage@K1 |
| Benefit at risk | CK1@K2, CK1@K3, Cage@K2, Cage@K3 |

**Earlier, unpaired evidence (to be replaced by 5301).**

* On 4901, the support fallback and the Gaussian-quantile gate trade harm against benefit, per cell (handover B §3).
* On 5101, the per-slot emulation adapter beats a relabel (+4.63 [2.83, 6.32]) but not plain (+0.75 [−1.01, 2.32]).
* On 5201, the input-only throttle loses −11.15 [−14.13, −7.84] vs plain.

The "harm blocked 99.8 % / 72 %, benefit kept < 0 % / 44 %" summary of 4901 covers only the four non-own cells with a
positive mean. It is retrospective and has no CI, so it stays descriptive.

### R5 The silence bar

* The same-receiver masked reference is far below Z: on 4×4 (5201), −14.87 [−26.83, −7.02] for the K1-trained receiver and
  −15.30 [−19.97, −10.46] for the iid-trained one.
* Against that reference every hazard of R1 would look like a gain; against Z the mismatched receivers fall below silence.
* [P1 RP1 confirms or refutes this on 5301.]

### R6 Mechanism [P2; included only if both gates pass]

**Hypothesis.** The input-only adapters fail because the receiver's protocol history is not reproduced: sender selection,
mirror and cache.

**Gate 1 (information feasibility).** Any mirror update from accepted packets must use information the sender legitimately
has: a shared deterministic rule, or an ACK whose bytes and delay are counted. No direct reads of the receiver's cache are
allowed.

**Gate 2 (replay feasibility).** Measure the missing-packet rate of the new channel relative to K1's requirements. Then check
packet IDs, payloads, timestamps, cache, encoded inputs and actions on paired traces.

**If both gates pass.** Forcing the whole system back to K1 is a rollback / positive control, not a method that exploits the
upgrade.
